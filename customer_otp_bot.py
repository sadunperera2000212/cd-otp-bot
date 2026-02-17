import os
import json
import re
import asyncio
import logging
import time
import threading
from typing import Optional
from datetime import datetime
from pathlib import Path

import httpx
from bs4 import BeautifulSoup
from telegram import Update
from telegram.ext import (
    Application,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

# ✅ Telegram request config + network error types
from telegram.request import HTTPXRequest
from telegram.error import Forbidden, RetryAfter, BadRequest, TimedOut, NetworkError

# ✅ Redis (optional; only for watchlist commands if you still want)
import redis.asyncio as redis

logging.basicConfig(
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=logging.INFO,
)
logger = logging.getLogger(__name__)

# ----------- ENV -----------
TG_TOKEN = os.getenv("TG_TOKEN")
ADMIN_IDS = [int(x.strip()) for x in os.getenv("ADMIN_IDS", "6356573938").split(",")]

ALLOWED_DOMAIN = [
    d.strip().lower()
    for d in os.getenv("ALLOWED_DOMAIN", "").split(",")
    if d.strip()
]

MAX_REQUESTS_PER_USER = int(os.getenv("MAX_REQUESTS_PER_USER", "10"))
DELAY_SECONDS = int(os.getenv("DELAY_SECONDS", "30"))
STATE_FILE = os.getenv("STATE_FILE", "state.json")
COOLDOWN_SECONDS = 91  # ~3 minutes cooldown after success OR "no OTP"

# ✅ Redis URL (OPTIONAL now)
REDIS_URL = os.getenv("REDIS_URL", "").strip()

# Self-healing knobs (optional)
RESTART_EVERY_MIN = int(os.getenv("RESTART_EVERY_MIN", "0"))  # 0 = disabled
ERROR_RESTART_THRESHOLD = int(os.getenv("ERROR_RESTART_THRESHOLD", "6"))
# ---------------------------

OTP_PATTERN = re.compile(r"\b(\d{6})\b")

# ✅ Redis keys for warning watcher (ONLY if REDIS_URL is set)
WATCHLIST_KEY = "warn:watchlist"          # Redis SET of emails
INTERVAL_KEY = "warn:interval_min"        # Redis STRING minutes

# ✅ NEW FEATURE (NO REDIS): checklist stored in state.json
CHECKLIST_STATE_KEY = "checklist_emails"

# ✅ FIXED subject for /check (ONLY /check, no args)
FIXED_SUBJECT = "OpenAI - Access Deactivated"

# Track consecutive network-ish errors for auto-restart
_CONSEC_ERRORS = 0


def _allowed_domains_text() -> str:
    return ", ".join(f"@{d}" for d in ALLOWED_DOMAIN)


def _is_allowed_domain(email: str) -> bool:
    return any(email.endswith(f"@{d}") for d in ALLOWED_DOMAIN)


def _parse_ids(text: str):
    return [int(x) for x in re.findall(r"\d+", text or "")]


def _looks_like_email(text: str) -> bool:
    t = (text or "").strip().lower()
    return bool(re.match(r"^[^\s@]+@[^\s@]+\.[^\s@]+$", t))


def _norm_spaces(s: str) -> str:
    return " ".join((s or "").split()).strip()


def _extract_text_after_command(update: Update, command: str) -> str:
    """
    Lets you do:
    /elistadd a@d.com
    b@d.com
    c@d.com

    and it will capture everything after "/elistadd"
    """
    if not update.message or not update.message.text:
        return ""
    txt = update.message.text.strip()
    if not txt.lower().startswith(command.lower()):
        return ""
    rest = txt[len(command):].strip()
    return rest


def _parse_emails_from_blob(blob: str) -> list[str]:
    """
    Accepts comma-separated, space-separated, or newline-separated emails.
    """
    raw = (blob or "").strip()
    if not raw:
        return []
    parts = re.split(r"[,\s]+", raw)
    emails = []
    for p in parts:
        p = (p or "").strip().lower()
        if p:
            emails.append(p)
    return emails


# ✅ Redis client (ONLY used by watchlist commands)
redis_client = redis.from_url(REDIS_URL, decode_responses=True) if REDIS_URL else None


class StateManager:
    def __init__(self, state_file: str):
        self.state_file = state_file
        self.state = self._load_state()

    def _load_state(self) -> dict:
        Path(self.state_file).parent.mkdir(parents=True, exist_ok=True)
        if os.path.exists(self.state_file):
            try:
                with open(self.state_file, "r") as f:
                    data = json.load(f)
            except Exception as e:
                logger.error(f"Error loading state: {e}")
                data = {}
        else:
            data = {}

        data.setdefault("user_requests", {})
        data.setdefault("cached_otps", {})
        data.setdefault("cooldowns", {})
        data.setdefault("blocked_emails", {})
        data.setdefault("subscribers", [])
        data.setdefault(CHECKLIST_STATE_KEY, [])
        return data

    def _save_state(self):
        try:
            with open(self.state_file, "w") as f:
                json.dump(self.state, f, indent=2)
        except Exception as e:
            logger.error(f"Error saving state: {e}")

    # ---- quotas ----
    def get_user_requests(self, user_id: int) -> int:
        return self.state["user_requests"].get(str(user_id), 0)

    def increment_user_requests(self, user_id: int):
        uid = str(user_id)
        self.state["user_requests"][uid] = self.state["user_requests"].get(uid, 0) + 1
        self._save_state()

    def reset_user_limit(self, user_id: int):
        uid = str(user_id)
        if uid in self.state["user_requests"]:
            del self.state["user_requests"][uid]
        self._save_state()

    # ---- otp cache ----
    def cache_otp(self, email: str, otp: str):
        self.state["cached_otps"][email] = {
            "otp": otp,
            "timestamp": datetime.now().isoformat(),
        }
        self._save_state()

    def clear_email(self, email: str):
        if email in self.state["cached_otps"]:
            del self.state["cached_otps"][email]
            self._save_state()
            return True
        return False

    # ---- cooldowns ----
    def set_cooldown(self, user_id: int, seconds: int):
        next_allowed = int(time.time()) + seconds
        self.state["cooldowns"][str(user_id)] = next_allowed
        self._save_state()

    def remaining_cooldown(self, user_id: int) -> int:
        now = int(time.time())
        next_allowed = int(self.state["cooldowns"].get(str(user_id), 0))
        if next_allowed > now:
            return next_allowed - now
        return 0

    # ---- blocked emails ----
    def is_blocked(self, email: str) -> bool:
        return email in self.state.get("blocked_emails", {})

    def block_email(self, email: str, by_user_id: int):
        self.state["blocked_emails"][email] = {
            "timestamp": datetime.now().isoformat(),
            "by": by_user_id,
        }
        self._save_state()

    def unblock_email(self, email: str) -> bool:
        if email in self.state.get("blocked_emails", {}):
            del self.state["blocked_emails"][email]
            self._save_state()
            return True
        return False

    # ---- subscribers ----
    def add_subscriber(self, chat_id: int):
        cid = int(chat_id)
        if cid not in self.state["subscribers"]:
            self.state["subscribers"].append(cid)
            self._save_state()

    def get_subscribers(self):
        return list(self.state.get("subscribers", []))

    def remove_subscriber(self, chat_id: int) -> bool:
        cid = int(chat_id)
        if cid in self.state.get("subscribers", []):
            self.state["subscribers"].remove(cid)
            self._save_state()
            return True
        return False

    # ✅ checklist stored in state.json (NO REDIS)
    def checklist_get(self) -> list[str]:
        return list(self.state.get(CHECKLIST_STATE_KEY, []))

    def checklist_add(self, emails: list[str]) -> tuple[int, int]:
        cur = set(self.state.get(CHECKLIST_STATE_KEY, []))
        added = 0
        skipped = 0
        for e in emails:
            e = (e or "").strip().lower()
            if not _looks_like_email(e) or not _is_allowed_domain(e):
                skipped += 1
                continue
            if e not in cur:
                cur.add(e)
                added += 1
        self.state[CHECKLIST_STATE_KEY] = sorted(cur)
        self._save_state()
        return added, skipped

    def checklist_remove(self, emails: list[str]) -> int:
        cur = set(self.state.get(CHECKLIST_STATE_KEY, []))
        before = len(cur)
        for e in emails:
            e = (e or "").strip().lower()
            if e in cur:
                cur.remove(e)
        self.state[CHECKLIST_STATE_KEY] = sorted(cur)
        self._save_state()
        return before - len(cur)

    def checklist_clear(self):
        self.state[CHECKLIST_STATE_KEY] = []
        self._save_state()


state_manager = StateManager(STATE_FILE)


async def fetch_otp_from_generator(email: str) -> Optional[str]:
    inbox_url = f"https://generator.email/{email}"

    headers = {
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) "
            "Chrome/120.0.0.0 Safari/537.36"
        ),
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8",
        "Accept-Language": "en-US,en;q=0.5",
        "Accept-Encoding": "gzip, deflate, br",
        "Connection": "keep-alive",
        "Upgrade-Insecure-Requests": "1",
        "Sec-Fetch-Dest": "document",
        "Sec-Fetch-Mode": "navigate",
        "Sec-Fetch-Site": "none",
        "Cache-Control": "max-age=0",
        "Referer": "https://generator.email/",
    }

    max_retries = 3

    async with httpx.AsyncClient(timeout=httpx.Timeout(25.0), follow_redirects=True) as client:
        for attempt in range(max_retries):
            try:
                logger.info(f"Fetching {inbox_url} (attempt {attempt + 1}/{max_retries})")
                response = await client.get(inbox_url, headers=headers)
                response.raise_for_status()

                soup = BeautifulSoup(response.text, "html.parser")

                newest_link = None
                email_table = soup.find(id="email-table")
                if email_table:
                    first_a = email_table.find("a", href=True)
                    if first_a and first_a.get("href"):
                        newest_link = first_a["href"].strip()

                if newest_link:
                    if newest_link.startswith("/"):
                        newest_url = "https://generator.email" + newest_link
                    elif newest_link.startswith("http"):
                        newest_url = newest_link
                    else:
                        newest_url = "https://generator.email/" + newest_link

                    logger.info(f"Opening newest email page: {newest_url}")
                    msg_resp = await client.get(newest_url, headers={**headers, "Referer": inbox_url})
                    msg_resp.raise_for_status()
                    msg_soup = BeautifulSoup(msg_resp.text, "html.parser")

                    msg_text = msg_soup.get_text(" ", strip=True)
                    msg_matches = OTP_PATTERN.findall(msg_text)
                    if msg_matches:
                        otp = msg_matches[0]
                        logger.info(f"Found OTP in newest email body: {otp}")
                        return otp

                    iframe = msg_soup.find("iframe", src=True)
                    if iframe and iframe.get("src"):
                        iframe_src = iframe["src"].strip()
                        if iframe_src.startswith("/"):
                            iframe_url = "https://generator.email" + iframe_src
                        elif iframe_src.startswith("http"):
                            iframe_url = iframe_src
                        else:
                            iframe_url = "https://generator.email/" + iframe_src

                        logger.info(f"Opening iframe for email body: {iframe_url}")
                        iframe_resp = await client.get(iframe_url, headers={**headers, "Referer": newest_url})
                        iframe_resp.raise_for_status()
                        iframe_text = BeautifulSoup(iframe_resp.text, "html.parser").get_text(" ", strip=True)
                        iframe_matches = OTP_PATTERN.findall(iframe_text)
                        if iframe_matches:
                            otp = iframe_matches[0]
                            logger.info(f"Found OTP in iframe email body: {otp}")
                            return otp

                email_bodies = soup.find_all(["div", "p", "span", "td"])
                for element in email_bodies:
                    text = element.get_text()
                    matches = OTP_PATTERN.findall(text)
                    if matches:
                        otp = matches[0]
                        logger.info(f"Found OTP (fallback): {otp}")
                        return otp

                logger.warning(f"No OTP found in inbox for {email}")
                return None

            except httpx.HTTPError as e:
                logger.error(f"Request error (attempt {attempt + 1}): {e}")
                if attempt < max_retries - 1:
                    await asyncio.sleep(2)
                else:
                    raise

    return None


# ✅✅✅ FIXED subject check: OPEN message links + check real subject in message pages (+ iframe)
async def inbox_has_subject_exact(email: str, subject_exact: str) -> bool:
    want = _norm_spaces(subject_exact)
    if not want:
        return False

    inbox_url = f"https://generator.email/{email}"

    headers = {
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) "
            "Chrome/120.0.0.0 Safari/537.36"
        ),
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8",
        "Accept-Language": "en-US,en;q=0.5",
        "Connection": "keep-alive",
        "Upgrade-Insecure-Requests": "1",
        "Referer": "https://generator.email/",
    }

    max_retries = 3

    async with httpx.AsyncClient(
        timeout=httpx.Timeout(30.0),
        follow_redirects=True,
    ) as client:
        for attempt in range(1, max_retries + 1):
            try:
                resp = await client.get(inbox_url, headers=headers)
                resp.raise_for_status()

                soup = BeautifulSoup(resp.text, "html.parser")
                email_table = soup.find(id="email-table")
                if not email_table:
                    return False

                links = []
                for a in email_table.find_all("a", href=True):
                    href = (a.get("href") or "").strip()
                    if not href:
                        continue
                    if href.startswith("/"):
                        href = "https://generator.email" + href
                    elif href.startswith("http"):
                        pass
                    else:
                        href = "https://generator.email/" + href
                    links.append(href)

                if not links:
                    return False

                # scan enough old messages
                MAX_TO_SCAN = 30

                for msg_url in links[:MAX_TO_SCAN]:
                    try:
                        msg_resp = await client.get(msg_url, headers={**headers, "Referer": inbox_url})
                        msg_resp.raise_for_status()
                        msg_soup = BeautifulSoup(msg_resp.text, "html.parser")

                        # 1) <title>
                        title = _norm_spaces(msg_soup.title.get_text() if msg_soup.title else "")
                        if title == want:
                            return True

                        # 2) <h1>
                        h1 = msg_soup.find("h1")
                        if h1:
                            h1_text = _norm_spaces(h1.get_text(" ", strip=True))
                            if h1_text == want:
                                return True

                        # 3) search full visible text
                        full_text = _norm_spaces(msg_soup.get_text(" ", strip=True))
                        if want in full_text:
                            return True

                        # 4) iframe
                        iframe = msg_soup.find("iframe", src=True)
                        if iframe and iframe.get("src"):
                            iframe_src = iframe["src"].strip()
                            if iframe_src.startswith("/"):
                                iframe_url = "https://generator.email" + iframe_src
                            elif iframe_src.startswith("http"):
                                iframe_url = iframe_src
                            else:
                                iframe_url = "https://generator.email/" + iframe_src

                            iframe_resp = await client.get(iframe_url, headers={**headers, "Referer": msg_url})
                            iframe_resp.raise_for_status()
                            iframe_soup = BeautifulSoup(iframe_resp.text, "html.parser")
                            iframe_text = _norm_spaces(iframe_soup.get_text(" ", strip=True))
                            if want in iframe_text:
                                return True

                    except httpx.HTTPError:
                        continue

                return False

            except httpx.HTTPError as e:
                logger.error(f"inbox_has_subject_exact error (attempt {attempt}/{max_retries}) for {email}: {e}")
                if attempt < max_retries:
                    await asyncio.sleep(2 * attempt)
                    continue
                return False


# ---------------- Self-healing helpers ----------------
def _start_timed_restart_thread():
    if RESTART_EVERY_MIN <= 0:
        return

    def _worker():
        logger.warning(f"Timed restart enabled. Will restart every {RESTART_EVERY_MIN} minutes.")
        while True:
            time.sleep(RESTART_EVERY_MIN * 60)
            logger.warning("Restarting bot now...")
            import sys
            os.execv(sys.executable, ["python"] + sys.argv)

    t = threading.Thread(target=_worker, daemon=True)
    t.start()


def _note_net_success():
    global _CONSEC_ERRORS
    _CONSEC_ERRORS = 0


def _note_net_error_and_maybe_restart():
    global _CONSEC_ERRORS
    _CONSEC_ERRORS += 1
    if ERROR_RESTART_THRESHOLD > 0 and _CONSEC_ERRORS >= ERROR_RESTART_THRESHOLD:
        logger.error(
            f"Consecutive network errors reached {ERROR_RESTART_THRESHOLD}. "
            "Exiting for Railway to auto-restart."
        )
        os._exit(1)


# ---------------- Commands ----------------
async def start_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message:
        return

    user = update.effective_user
    if not user:
        return

    if update.effective_chat:
        state_manager.add_subscriber(update.effective_chat.id)

    domains_text = _allowed_domains_text()

    welcome_text = (
        "✨ Welcome to *CyberDeals* OTP Service ✨\n\n"
        "📩 *How to get your OTP:*\n"
        "Just send your email address here (no commands needed).\n\n"
        "✅ *Examples you can copy:*\n"
        "• cyberdeals.ajanthan41@kabarr.com\n\n"
        f"🌐 *Allowed domains:* {domains_text}\n\n"
        f"⏳ After you send the email, I’ll wait *{DELAY_SECONDS} seconds* and then check the inbox.\n\n"
        f"📊 Each user can request up to *{MAX_REQUESTS_PER_USER}* OTP checks in total.\n\n"
        "🕒 After every check (OTP found or not), please wait *3 minutes* before sending another email.\n\n"
        "💡 Tip: Make sure the email spelling is correct to get the OTP faster."
    )

    await update.message.reply_text(welcome_text, parse_mode="Markdown")


async def _process_email_request(update: Update, context: ContextTypes.DEFAULT_TYPE, email: str):
    """Shared logic: validate + cooldown + fetch OTP + reply."""
    if not update.message:
        return

    user = update.effective_user
    if not user:
        return

    if update.effective_chat:
        state_manager.add_subscriber(update.effective_chat.id)

    is_admin = user.id in ADMIN_IDS

    if not is_admin:
        cd = state_manager.remaining_cooldown(user.id)
        if cd > 0:
            await update.message.reply_text(f"⏳ Please wait {cd} seconds before requesting again.")
            return

    email = (email or "").strip().lower()

    if not _looks_like_email(email):
        await update.message.reply_text(
            "❌ That doesn’t look like a valid email.\n\n"
            "✅ Send only the email address like this:\n"
            "• cyberdeals.kaviska@eliotkids.com\n"
            "• cyberdeals.ajanthan41@kabarr.com"
        )
        return

    if not _is_allowed_domain(email):
        await update.message.reply_text(
            f"❌ Invalid email domain.\nOnly these are supported: {_allowed_domains_text()}"
        )
        return

    if state_manager.is_blocked(email):
        if not is_admin:
            state_manager.set_cooldown(user.id, COOLDOWN_SECONDS)

        try:
            with open("otp_log.txt", "a") as lf:
                lf.write(f"[{datetime.now()}] user={user.id} email={email} result=NO_OTP\n")
        except Exception:
            pass

        await update.message.reply_text("❌ No OTP found right now. Please try again later.")
        return

    if not is_admin:
        current_requests = state_manager.get_user_requests(user.id)
        if current_requests >= MAX_REQUESTS_PER_USER:
            await update.message.reply_text(f"⛔ You reached your limit ({MAX_REQUESTS_PER_USER}).")
            return
        remaining_if_success = MAX_REQUESTS_PER_USER - (current_requests + 1)
    else:
        remaining_if_success = "∞"

    await update.message.reply_text(
        f"⏳ Got it! Checking soon…\n"
        f"📧 {email}\n"
        f"⏱️ Waiting {DELAY_SECONDS} seconds\n"
        f"📊 Remaining (if success): {remaining_if_success}"
    )

    if not is_admin:
        await asyncio.sleep(DELAY_SECONDS)

    max_rounds = 5
    for round_idx in range(1, max_rounds + 1):
        try:
            otp = await fetch_otp_from_generator(email)

            if otp:
                if not is_admin:
                    state_manager.increment_user_requests(user.id)
                state_manager.cache_otp(email, otp)

                if not is_admin:
                    state_manager.set_cooldown(user.id, COOLDOWN_SECONDS)

                try:
                    with open("otp_log.txt", "a") as lf:
                        lf.write(f"[{datetime.now()}] user={user.id} email={email} result=OTP:{otp}\n")
                except Exception:
                    pass

                _note_net_success()

                if not is_admin:
                    now_used = state_manager.get_user_requests(user.id)
                    remaining = MAX_REQUESTS_PER_USER - now_used
                else:
                    remaining = "∞"

                await update.message.reply_text(
                    f"✅ OTP Found!\n\n"
                    f"🔢 Code: `{otp}`\n"
                    f"📧 {email}\n"
                    f"📊 Remaining: {remaining}",
                    parse_mode="Markdown",
                )
                return
            else:
                if not is_admin:
                    state_manager.set_cooldown(user.id, COOLDOWN_SECONDS)

                try:
                    with open("otp_log.txt", "a") as lf:
                        lf.write(f"[{datetime.now()}] user={user.id} email={email} result=NO_OTP\n")
                except Exception:
                    pass

                _note_net_success()
                await update.message.reply_text("❌ No OTP found right now. Please try again later.")
                return

        except httpx.HTTPError:
            try:
                with open("otp_log.txt", "a") as lf:
                    lf.write(f"[{datetime.now()}] user={user.id} email={email} result=NETWORK_ERROR attempt={round_idx}\n")
            except Exception:
                pass

            if round_idx < max_rounds:
                await update.message.reply_text(
                    f"⚠️ Network issue (attempt {round_idx}/{max_rounds}). Retrying in 5 seconds..."
                )
                await asyncio.sleep(5)
                continue

            _note_net_error_and_maybe_restart()
            await update.message.reply_text("⚠️ Network issue. Please wait a few minutes and try again.")
            return

        except Exception as e:
            logger.error(f"Unexpected error: {e}")

            try:
                with open("otp_log.txt", "a") as lf:
                    lf.write(f"[{datetime.now()}] user={user.id} email={email} result=UNEXPECTED_ERROR:{str(e)[:120]}\n")
            except Exception:
                pass

            _note_net_error_and_maybe_restart()
            await update.message.reply_text("❌ An unexpected error occurred. Please try again.")
            return


# ✅ user sends plain email message (no /otp command)
async def email_message_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message:
        return

    text = (update.message.text or "").strip()
    if not text:
        return

    # ignore if it's a command just in case
    if text.startswith("/"):
        return

    await _process_email_request(update, context, text)


async def remaining_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message:
        return

    user = update.effective_user
    if not user:
        return

    current_requests = state_manager.get_user_requests(user.id)
    remaining = MAX_REQUESTS_PER_USER - current_requests
    cd = state_manager.remaining_cooldown(user.id)

    if cd > 0:
        text = f"📊 Used: {current_requests}/{MAX_REQUESTS_PER_USER}\n⏱️ Cooldown: {cd} seconds left"
    else:
        text = f"📊 Used: {current_requests}/{MAX_REQUESTS_PER_USER}\n✅ No cooldown active"

    await update.message.reply_text(text)


async def resetlimit_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message:
        return

    user = update.effective_user
    if not user:
        return

    if user.id not in ADMIN_IDS:
        await update.message.reply_text("⛔ Admin only.")
        return

    if not context.args:
        await update.message.reply_text("❌ Usage: /resetlimit <user_id>")
        return

    try:
        target_user_id = int(context.args[0])
        state_manager.reset_user_limit(target_user_id)
        await update.message.reply_text(f"✅ Reset done for user {target_user_id}")
    except ValueError:
        await update.message.reply_text("❌ Invalid user ID (must be a number).")


async def clearemail_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message:
        return

    user = update.effective_user
    if not user:
        return

    if user.id not in ADMIN_IDS:
        await update.message.reply_text("⛔ Admin only.")
        return

    if not context.args:
        await update.message.reply_text("❌ Usage: /clearemail <email>")
        return

    email = context.args[0].lower()
    if state_manager.clear_email(email):
        await update.message.reply_text(f"✅ Cached OTP cleared for {email}")
    else:
        await update.message.reply_text(f"ℹ️ No cached OTP found for {email}")


async def block_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message:
        return
    user = update.effective_user
    if not user:
        return

    if user.id not in ADMIN_IDS:
        await update.message.reply_text("⛔ Admin only.")
        return

    if not context.args:
        await update.message.reply_text("❌ Usage: /block <email>")
        return

    email = context.args[0].strip().lower()
    if not _is_allowed_domain(email):
        await update.message.reply_text(f"❌ Invalid email domain. Only {_allowed_domains_text()} is supported.")
        return

    state_manager.block_email(email, user.id)

    try:
        with open("otp_log.txt", "a") as lf:
            lf.write(f"[{datetime.now()}] user={user.id} email={email} action=BLOCK\n")
    except Exception:
        pass

    await update.message.reply_text("✅ Done.")


async def unblock_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message:
        return
    user = update.effective_user
    if not user:
        return

    if user.id not in ADMIN_IDS:
        await update.message.reply_text("⛔ Admin only.")
        return

    if not context.args:
        await update.message.reply_text("❌ Usage: /unblock <email>")
        return

    email = context.args[0].strip().lower()
    if not _is_allowed_domain(email):
        await update.message.reply_text(f"❌ Invalid email domain. Only {_allowed_domains_text()} is supported.")
        return

    ok = state_manager.unblock_email(email)

    try:
        with open("otp_log.txt", "a") as lf:
            lf.write(f"[{datetime.now()}] user={user.id} email={email} action=UNBLOCK ok={ok}\n")
    except Exception:
        pass

    await update.message.reply_text("✅ Done." if ok else "ℹ️ Not found.")


async def showlog_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    if not user:
        return

    if user.id not in ADMIN_IDS:
        await update.message.reply_text("⛔ This command is restricted to admins only.")
        return

    log_file = "otp_log.txt"
    try:
        with open(log_file, "r") as f:
            lines = f.readlines()

        if not lines:
            await update.message.reply_text("📭 Log file is empty.")
            return

        full_log = "".join(lines)

        if len(full_log) > 4000:
            chunks = [full_log[i:i + 4000] for i in range(0, len(full_log), 4000)]
            for i, chunk in enumerate(chunks, start=1):
                await update.message.reply_text(f"📜 Log Part {i}:\n\n{chunk}")
        else:
            await update.message.reply_text(f"🧾 Full Log:\n\n{full_log}")

    except FileNotFoundError:
        await update.message.reply_text("⚠️ No log file found yet.")
    except Exception as e:
        await update.message.reply_text(f"❌ Error reading log: {e}")


async def dash_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message:
        return

    user = update.effective_user
    if not user:
        return

    if user.id not in ADMIN_IDS:
        await update.message.reply_text("⛔ Admin only.")
        return

    subscribers = state_manager.get_subscribers()
    if not subscribers:
        await update.message.reply_text("ℹ️ No users to broadcast to yet.")
        return

    bot = context.bot

    if update.message.reply_to_message:
        src_chat_id = update.message.reply_to_message.chat_id
        src_message_id = update.message.reply_to_message.message_id

        sent = 0
        failed = 0

        for chat_id in subscribers:
            try:
                await bot.copy_message(
                    chat_id=chat_id,
                    from_chat_id=src_chat_id,
                    message_id=src_message_id,
                )
                sent += 1
                await asyncio.sleep(0.05)
            except RetryAfter as e:
                await asyncio.sleep(int(getattr(e, "retry_after", 1)))
            except Forbidden:
                state_manager.remove_subscriber(chat_id)
                failed += 1
            except BadRequest:
                failed += 1
            except Exception:
                failed += 1

        await update.message.reply_text(f"✅ Broadcast done. Sent: {sent}, Failed: {failed}")
        return

    if not context.args:
        await update.message.reply_text(
            "❌ Usage:\n"
            "1) /dash <text to broadcast>\n"
            "2) Reply to a message (photo/text/etc) with /dash to broadcast it."
        )
        return

    text = " ".join(context.args)

    sent = 0
    failed = 0

    for chat_id in subscribers:
        try:
            await bot.send_message(chat_id=chat_id, text=text)
            sent += 1
            await asyncio.sleep(0.05)
        except RetryAfter as e:
            await asyncio.sleep(int(getattr(e, "retry_after", 1)))
        except Forbidden:
            state_manager.remove_subscriber(chat_id)
            failed += 1
        except Exception:
            failed += 1

    await update.message.reply_text(f"✅ Broadcast done. Sent: {sent}, Failed: {failed}")


async def addusers_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message:
        return

    user = update.effective_user
    if not user:
        return

    if user.id not in ADMIN_IDS:
        await update.message.reply_text("⛔ Admin only.")
        return

    if not context.args:
        await update.message.reply_text("❌ Usage: /addusers 111,222,333")
        return

    ids = _parse_ids(" ".join(context.args))
    if not ids:
        await update.message.reply_text("❌ No user IDs found.")
        return

    before = len(state_manager.get_subscribers())
    for cid in ids:
        state_manager.add_subscriber(cid)
    after = len(state_manager.get_subscribers())

    await update.message.reply_text(f"✅ Added {after - before} users to subscribers.")


# ✅ Watchlist commands (admin only) using Redis (still optional)
async def wadd_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message:
        return
    user = update.effective_user
    if not user:
        return

    if user.id not in ADMIN_IDS:
        await update.message.reply_text("⛔ Admin only.")
        return

    if not REDIS_URL or redis_client is None:
        await update.message.reply_text("❌ REDIS_URL is not set. Cannot use watchlist commands.")
        return

    if not context.args:
        await update.message.reply_text("❌ Usage: /wadd email@domain OR /wadd a@d.com,b@d.com")
        return

    raw = " ".join(context.args).strip().lower()
    parts = re.split(r"[,\s]+", raw)
    emails = [p.strip() for p in parts if p.strip()]

    if not emails:
        await update.message.reply_text("❌ No emails found.")
        return

    added = 0
    already = 0
    invalid = []

    for email in emails:
        if not _is_allowed_domain(email):
            invalid.append(email)
            continue
        try:
            ok = await redis_client.sadd(WATCHLIST_KEY, email)
            if ok:
                added += 1
            else:
                already += 1
        except Exception as e:
            await update.message.reply_text(f"❌ Redis error: {e}")
            return

    msg = f"✅ Added: {added}\nℹ️ Already in list: {already}"
    if invalid:
        msg += "\n❌ Invalid domain:\n" + "\n".join(f"• {e}" for e in invalid[:30])
        if len(invalid) > 30:
            msg += f"\n… +{len(invalid) - 30} more"

    await update.message.reply_text(msg)


async def wremove_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message:
        return
    user = update.effective_user
    if not user:
        return

    if user.id not in ADMIN_IDS:
        await update.message.reply_text("⛔ Admin only.")
        return

    if not REDIS_URL or redis_client is None:
        await update.message.reply_text("❌ REDIS_URL is not set. Cannot use watchlist commands.")
        return

    if not context.args:
        await update.message.reply_text("❌ Usage: /wremove email@domain OR /wremove a@d.com,b@d.com")
        return

    raw = " ".join(context.args).strip().lower()
    parts = re.split(r"[,\s]+", raw)
    emails = [p.strip() for p in parts if p.strip()]

    removed = 0
    not_found = 0
    invalid = []

    for email in emails:
        if not _is_allowed_domain(email):
            invalid.append(email)
            continue
        try:
            ok = await redis_client.srem(WATCHLIST_KEY, email)
            if ok:
                removed += 1
            else:
                not_found += 1
        except Exception as e:
            await update.message.reply_text(f"❌ Redis error: {e}")
            return

    msg = f"✅ Removed: {removed}\nℹ️ Not found: {not_found}"
    if invalid:
        msg += "\n❌ Invalid domain:\n" + "\n".join(f"• {e}" for e in invalid[:30])
        if len(invalid) > 30:
            msg += f"\n… +{len(invalid) - 30} more"

    await update.message.reply_text(msg)


async def wlist_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message:
        return
    user = update.effective_user
    if not user:
        return

    if user.id not in ADMIN_IDS:
        await update.message.reply_text("⛔ Admin only.")
        return

    if not REDIS_URL or redis_client is None:
        await update.message.reply_text("❌ REDIS_URL is not set. Cannot use watchlist commands.")
        return

    try:
        emails = await redis_client.smembers(WATCHLIST_KEY)
        emails = sorted(list(emails))
    except Exception as e:
        await update.message.reply_text(f"❌ Redis error: {e}")
        return

    if not emails:
        await update.message.reply_text("ℹ️ Watchlist empty.")
        return

    text = "📌 Watchlist:\n" + "\n".join(f"• {e}" for e in emails)
    if len(text) > 3800:
        text = text[:3800] + "\n…(trimmed)"
    await update.message.reply_text(text)


async def winterval_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message:
        return
    user = update.effective_user
    if not user:
        return

    if user.id not in ADMIN_IDS:
        await update.message.reply_text("⛔ Admin only.")
        return

    if not REDIS_URL or redis_client is None:
        await update.message.reply_text("❌ REDIS_URL is not set. Cannot use watchlist commands.")
        return

    if not context.args:
        try:
            v = await redis_client.get(INTERVAL_KEY)
        except Exception as e:
            await update.message.reply_text(f"❌ Redis error: {e}")
            return
        current = v if v else "not set"
        await update.message.reply_text(f"⏱️ Current interval: {current} minutes\nUsage: /winterval 30")
        return

    try:
        n = int(context.args[0])
        if n < 1 or n > 1440:
            raise ValueError()
    except ValueError:
        await update.message.reply_text("❌ Invalid minutes. Use 1..1440")
        return

    try:
        await redis_client.set(INTERVAL_KEY, str(n))
    except Exception as e:
        await update.message.reply_text(f"❌ Redis error: {e}")
        return

    await update.message.reply_text(f"✅ Interval set to {n} minutes.")


# ===========================
# ✅ NEW FEATURE (NO REDIS): checklist + /check only
# ===========================

async def elistadd_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message:
        return
    user = update.effective_user
    if not user:
        return
    if user.id not in ADMIN_IDS:
        await update.message.reply_text("⛔ Admin only.")
        return

    blob = _extract_text_after_command(update, "/elistadd")
    if not blob:
        blob = " ".join(context.args or [])

    emails = _parse_emails_from_blob(blob)
    if not emails:
        await update.message.reply_text("❌ Usage: /elistadd email1,email2 OR paste lines after /elistadd")
        return

    added, skipped = state_manager.checklist_add(emails)
    total = len(state_manager.checklist_get())

    msg = f"✅ Checklist updated.\nAdded: {added}\nSkipped (invalid): {skipped}\nTotal saved: {total}"
    await update.message.reply_text(msg)


async def elistremove_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message:
        return
    user = update.effective_user
    if not user:
        return
    if user.id not in ADMIN_IDS:
        await update.message.reply_text("⛔ Admin only.")
        return

    blob = _extract_text_after_command(update, "/elistremove")
    if not blob:
        blob = " ".join(context.args or [])

    emails = _parse_emails_from_blob(blob)
    if not emails:
        await update.message.reply_text("❌ Usage: /elistremove email1,email2")
        return

    removed = state_manager.checklist_remove(emails)
    total = len(state_manager.checklist_get())
    await update.message.reply_text(f"✅ Removed: {removed}\nTotal saved: {total}")


async def elist_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message:
        return
    user = update.effective_user
    if not user:
        return
    if user.id not in ADMIN_IDS:
        await update.message.reply_text("⛔ Admin only.")
        return

    items = state_manager.checklist_get()
    if not items:
        await update.message.reply_text("ℹ️ Checklist is empty.")
        return

    text = "📌 Checklist:\n" + "\n".join(f"• {e}" for e in items)
    if len(text) > 3800:
        text = text[:3800] + "\n…(trimmed)"
    await update.message.reply_text(text)


async def elistclear_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message:
        return
    user = update.effective_user
    if not user:
        return
    if user.id not in ADMIN_IDS:
        await update.message.reply_text("⛔ Admin only.")
        return

    state_manager.checklist_clear()
    await update.message.reply_text("✅ Checklist cleared.")


# ✅ ONLY /check (no args, fixed subject)
async def check_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message:
        return
    user = update.effective_user
    if not user:
        return
    if user.id not in ADMIN_IDS:
        await update.message.reply_text("⛔ Admin only.")
        return

    emails = state_manager.checklist_get()
    if not emails:
        await update.message.reply_text("ℹ️ Checklist is empty. Add emails using /elistadd first.")
        return

    await update.message.reply_text(
        f"🔎 Checking {len(emails)} inboxes for EXACT subject:\n\n"
        f"“{FIXED_SUBJECT}”\n\n"
        f"(Checking one-by-one, no skipping.)"
    )

    found = []
    not_found = 0
    failed = []

    for email in emails:
        try:
            ok = await inbox_has_subject_exact(email, FIXED_SUBJECT)
            if ok:
                found.append(email)
            else:
                not_found += 1
        except Exception as e:
            logger.error(f"/check error for {email}: {e}")
            failed.append(email)

        await asyncio.sleep(0.2)

    if found:
        msg = "✅ Check done.\n\n🎯 Found in:\n" + "\n".join(f"• {e}" for e in found)
        msg += f"\n\n📭 Not found in: {not_found} inbox(es)."
    else:
        msg = "✅ Check done.\n\n❌ Not found in any inbox."

    if failed:
        msg += "\n\n⚠️ Failed to check (network/blocked):\n" + "\n".join(f"• {e}" for e in failed[:40])
        if len(failed) > 40:
            msg += f"\n… +{len(failed) - 40} more"

    await update.message.reply_text(msg)


async def error_handler(update: object, context: ContextTypes.DEFAULT_TYPE):
    logger.error(f"Update {update} caused error {context.error}")


def _build_application() -> Application:
    tg_request = HTTPXRequest(
        connect_timeout=30,
        read_timeout=30,
        write_timeout=30,
        pool_timeout=30,
    )

    app = (
        Application.builder()
        .token(TG_TOKEN)
        .request(tg_request)
        .concurrent_updates(True)
        .build()
    )

    app.add_handler(CommandHandler("start", start_command))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, email_message_handler))

    app.add_handler(CommandHandler("remaining", remaining_command))
    app.add_handler(CommandHandler("resetlimit", resetlimit_command))
    app.add_handler(CommandHandler("clearemail", clearemail_command))
    app.add_handler(CommandHandler("block", block_command))
    app.add_handler(CommandHandler("unblock", unblock_command))
    app.add_handler(CommandHandler("log", showlog_command))
    app.add_handler(CommandHandler("dash", dash_command))
    app.add_handler(CommandHandler("addusers", addusers_command))

    # watchlist (redis optional)
    app.add_handler(CommandHandler("wadd", wadd_command))
    app.add_handler(CommandHandler("wremove", wremove_command))
    app.add_handler(CommandHandler("wlist", wlist_command))
    app.add_handler(CommandHandler("winterval", winterval_command))

    # checklist + check
    app.add_handler(CommandHandler("elistadd", elistadd_command))
    app.add_handler(CommandHandler("elistremove", elistremove_command))
    app.add_handler(CommandHandler("elist", elist_command))
    app.add_handler(CommandHandler("elistclear", elistclear_command))
    app.add_handler(CommandHandler("check", check_command))

    app.add_error_handler(error_handler)
    return app


def main():
    if not TG_TOKEN:
        logger.error("TG_TOKEN environment variable is not set!")
        print("❌ ERROR: TG_TOKEN environment variable is required.")
        return

    if not ALLOWED_DOMAIN:
        logger.error("ALLOWED_DOMAIN environment variable is not set or empty!")
        print("❌ ERROR: ALLOWED_DOMAIN environment variable is required (comma-separated if multiple).")
        return

    logger.info("Starting OTP bot...")
    _start_timed_restart_thread()

    backoff = 2
    while True:
        try:
            application = _build_application()
            application.run_polling(allowed_updates=Update.ALL_TYPES)
            backoff = 2
        except (TimedOut, NetworkError, httpx.HTTPError, OSError) as e:
            logger.error(f"Telegram/network startup error: {e} — retrying in {backoff}s")
            time.sleep(backoff)
            backoff = min(backoff * 2, 60)
            continue
        except Exception as e:
            logger.exception(f"Fatal unexpected error: {e}")
            _note_net_error_and_maybe_restart()
            time.sleep(5)


if __name__ == "__main__":
    main()
