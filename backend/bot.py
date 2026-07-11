"""
================================================================================
                    TELEGRAM ADVANCED REFERRAL BOT SYSTEM
   [ v4: Softer fraud rules (fewer false-positive bans), stale verify-widget
     cleanup on every /start, and a resumable "stop bot" admin control. ]
     [ v4.1: Performance indexes + faster referral metrics for large user bases ]
         [ One person = One account. Shared IP alone is NOT a ban reason.    ]
================================================================================
"""

import os
import sys
import json
import hmac
import random
import asyncio
import hashlib
import logging
import urllib.parse
from datetime import datetime
from collections import defaultdict
import time

import httpx
import uvicorn
import aiosqlite
from dotenv import load_dotenv

from aiogram import Bot, Dispatcher, Router, F
from aiogram.enums import ParseMode, ChatMemberStatus
from aiogram.filters import CommandStart
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.types import (
    Message, CallbackQuery, InlineKeyboardMarkup, InlineKeyboardButton,
    WebAppInfo, FSInputFile, InlineQuery, InlineQueryResultCachedPhoto,
    InlineQueryResultArticle, InputTextMessageContent
)

from fastapi import FastAPI, Request, HTTPException
from fastapi.responses import HTMLResponse, JSONResponse
from fastapi.middleware.cors import CORSMiddleware
from contextlib import asynccontextmanager
from pydantic import BaseModel, Field
from typing import Optional, List

load_dotenv()

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(name)s: %(message)s",
    handlers=[logging.StreamHandler(sys.stdout)]
)
logger = logging.getLogger("ReferralBotSystem")
logger.info("════════════════════════════════════════════════")
logger.info("  BOT CODE VERSION: v4.2-debug-2026-06-30")
logger.info("  If you don't see this line after deploy/restart,")
logger.info("  the OLD code is still running on Railway.")
logger.info("════════════════════════════════════════════════")

BOT_TOKEN            = os.getenv("BOT_TOKEN", "")
ADMIN_IDS            = [int(x) for x in os.getenv("ADMIN_IDS", "0").split(",") if x.strip()]
PAYMENT_LOG_CHANNEL  = os.getenv("PAYMENT_LOG_CHANNEL", "").strip()
# Private channel (only you, the admin, should be a member of it) that
# receives a copy of the SQLite database file on a schedule — a safety
# net in case the Railway Volume is ever lost/corrupted. Leave empty to
# disable backups entirely.
DB_BACKUP_CHANNEL_ID   = os.getenv("DB_BACKUP_CHANNEL_ID", "").strip()
DB_BACKUP_INTERVAL_HOURS = int(os.getenv("DB_BACKUP_INTERVAL_HOURS", "24"))
# WEBAPP_URL = this backend's OWN public URL (Railway). Used for API calls
# and to build the /verify page link. Kept for backward compatibility.
WEBAPP_URL           = os.getenv("WEBAPP_URL", "http://localhost:8000").rstrip("/")
# FRONTEND_URL = the Mini App static site's public URL (Vercel). This is
# what Telegram "Open Mini App" buttons must point to. Falls back to
# WEBAPP_URL if not set, so old single-domain deployments still work.
FRONTEND_URL         = os.getenv("FRONTEND_URL", "").rstrip("/") or WEBAPP_URL
PROXYCHECK_API_KEY   = os.getenv("PROXYCHECK_API_KEY", "")
ALLOWED_ORIGIN       = os.getenv("ALLOWED_ORIGIN", "").strip()
DB_PATH               = os.getenv("DB_PATH", "referral_bot.db")
TASK_JOIN_WAIT_SECONDS = int(os.getenv("TASK_JOIN_WAIT_SECONDS", "5"))

# How old a Telegram WebApp initData payload is allowed to be before we
# reject it. initData is only re-issued when the Mini App is (re)opened
# inside Telegram, so this bounds how long a copied/leaked initData string
# (e.g. pasted into a normal browser) stays usable. Telegram itself
# recommends checking auth_date for exactly this reason.
MAX_INIT_DATA_AGE_SECONDS = int(os.getenv("MAX_INIT_DATA_AGE_SECONDS", str(6 * 3600)))

TELEBIRR_PROOF_IMAGE = "AgACAgQAAxkBAAIBImpM6RKFmzDV8HLYo0XHukkMK-RaAAI-D2sbGJdwUazZrBH4OObkAQADAgADeAADPAQ"

if not WEBAPP_URL.startswith(("http://", "https://")):
    WEBAPP_URL = f"https://{WEBAPP_URL}"

BOT_RULES_CAPTION = (
    "📜 <b>System Terms of Service & Anti-Fraud Policy</b>\n\n"
    "1. <b>Strict Integrity:</b> Self-referrals or multi-accounting schemes are prohibited.\n"
    "2. <b>Security Protocols:</b> Use of VPNs, proxy networks, or emulators is banned.\n"
    "3. <b>Reward Settlement:</b> Rewards are credited after Mini App identity clear.\n"
    "⚠️ <i>Note: Violations will result in a permanent ban.</i>"
)

# ─────────────────────────────────────────────────────────────────────────────
# RATE LIMITER
# ─────────────────────────────────────────────────────────────────────────────
class RateLimiter:
    def __init__(self, max_calls: int = 5, window_seconds: int = 60):
        self.max_calls     = max_calls
        self.window        = window_seconds
        self._calls: dict  = defaultdict(list)
        self._lock         = asyncio.Lock()

    async def is_allowed(self, key: str) -> bool:
        async with self._lock:
            now    = time.monotonic()
            bucket = self._calls[key]
            bucket[:] = [t for t in bucket if now - t < self.window]
            if len(bucket) >= self.max_calls:
                return False
            bucket.append(now)
            return True

verify_limiter = RateLimiter(max_calls=6, window_seconds=60)

# ─────────────────────────────────────────────────────────────────────────────
# IP COOLDOWN — አንድ IP verify ካደረገ በኋላ 3 ደቂቃ ሌላ NEW verify እንዳይሞክር
# (fingerprint ግን ለዘላለም DB ውስጥ ይቆያል — ይህ ለ rapid multi-account creation ብቻ ነው)
# ─────────────────────────────────────────────────────────────────────────────
IP_VERIFY_COOLDOWN_SECONDS = 180   # 3 ደቂቃ

class IPCooldownTracker:
    def __init__(self):
        self._last_verify: dict = {}   # ip -> timestamp
        self._lock = asyncio.Lock()

    async def is_on_cooldown(self, ip: str) -> tuple[bool, int]:
        """Returns (is_blocked, seconds_remaining)."""
        if not ip or ip in ("127.0.0.1", "::1", "unknown"):
            return False, 0
        async with self._lock:
            last = self._last_verify.get(ip)
            if last is None:
                return False, 0
            elapsed = time.monotonic() - last
            remaining = IP_VERIFY_COOLDOWN_SECONDS - elapsed
            if remaining > 0:
                return True, int(remaining)
            return False, 0

    async def mark_verified(self, ip: str):
        if not ip or ip in ("127.0.0.1", "::1", "unknown"):
            return
        async with self._lock:
            self._last_verify[ip] = time.monotonic()

ip_cooldown = IPCooldownTracker()

# ─────────────────────────────────────────────────────────────────────────────
# DATABASE SCHEMA
# ─────────────────────────────────────────────────────────────────────────────
SCHEMA = """
PRAGMA journal_mode=WAL;
PRAGMA synchronous=NORMAL;

CREATE TABLE IF NOT EXISTS users (
    user_id             INTEGER PRIMARY KEY,
    username            TEXT,
    full_name           TEXT,
    referred_by         INTEGER,
    balance             REAL    DEFAULT 0,
    is_banned           INTEGER DEFAULT 0,
    last_verify_msg_id  INTEGER DEFAULT 0,
    last_seen           TEXT    DEFAULT '',
    joined_at           TEXT    DEFAULT (datetime('now'))
);

CREATE TABLE IF NOT EXISTS verifications (
    id              INTEGER PRIMARY KEY AUTOINCREMENT,
    user_id         INTEGER UNIQUE,
    ip_address      TEXT,
    user_agent      TEXT,
    fingerprint     TEXT,
    referrer_ip     TEXT    DEFAULT '',
    tg_platform     TEXT    DEFAULT '',
    tg_version      TEXT    DEFAULT '',
    tg_app_version  TEXT    DEFAULT '',
    canvas_hash     TEXT    DEFAULT '',
    webgl_hash      TEXT    DEFAULT '',
    screen_sig      TEXT    DEFAULT '',
    verified_at     TEXT    DEFAULT (datetime('now'))
);

CREATE TABLE IF NOT EXISTS withdrawals (
    id              INTEGER PRIMARY KEY AUTOINCREMENT,
    user_id         INTEGER,
    amount          REAL,
    full_name       TEXT,
    phone           TEXT,
    status          TEXT    DEFAULT 'pending',
    channel_post_id INTEGER DEFAULT 0,
    reason          TEXT    DEFAULT '',
    created_at      TEXT    DEFAULT (datetime('now')),
    resolved_at     TEXT
);

CREATE TABLE IF NOT EXISTS force_channels (
    id           INTEGER PRIMARY KEY AUTOINCREMENT,
    channel_id   TEXT UNIQUE,
    channel_name TEXT,
    invite_link  TEXT,
    bot_added    INTEGER DEFAULT 0
);

CREATE TABLE IF NOT EXISTS settings (
    key   TEXT PRIMARY KEY,
    value TEXT
);

CREATE TABLE IF NOT EXISTS fake_join_seen (
    user_id INTEGER PRIMARY KEY,
    seen_at TEXT DEFAULT (datetime('now'))
);

CREATE TABLE IF NOT EXISTS banned_ips (
    ip_address  TEXT PRIMARY KEY,
    reason      TEXT,
    banned_at   TEXT DEFAULT (datetime('now'))
);

CREATE TABLE IF NOT EXISTS fraud_log (
    id          INTEGER PRIMARY KEY AUTOINCREMENT,
    user_id     INTEGER,
    reason      TEXT,
    ip_address  TEXT,
    details     TEXT    DEFAULT '',
    logged_at   TEXT    DEFAULT (datetime('now'))
);

-- ─────────────────────────────────────────────────────────────────────────
-- MINI APP TASK SYSTEM
-- task_type: 'force' (bot must be admin in channel_id → real membership
--            check via getChatMember before reward is paid)
--          | 'fake'  (no real check — just a Join-link + wait-timer, for
--            channels the bot cannot/should not be admin in)
-- ─────────────────────────────────────────────────────────────────────────
CREATE TABLE IF NOT EXISTS tasks (
    id           INTEGER PRIMARY KEY AUTOINCREMENT,
    title        TEXT    NOT NULL,
    channel_id   TEXT    DEFAULT '',
    invite_link  TEXT    DEFAULT '',
    task_type    TEXT    DEFAULT 'fake',
    reward       REAL    DEFAULT 0,
    position     INTEGER DEFAULT 0,
    is_active    INTEGER DEFAULT 1,
    created_at   TEXT    DEFAULT (datetime('now'))
);

CREATE TABLE IF NOT EXISTS task_progress (
    user_id      INTEGER,
    task_id      INTEGER,
    status       TEXT DEFAULT 'joined',
    joined_at    TEXT,
    completed_at TEXT,
    PRIMARY KEY (user_id, task_id)
);
CREATE INDEX IF NOT EXISTS idx_task_progress_user ON task_progress(user_id);
CREATE INDEX IF NOT EXISTS idx_tasks_position     ON tasks(position);

-- ─────────────────────────────────────────────────────────────────────────
-- ADSGRAM — REWARDED VIDEO + DIRECT LINK
-- kind: 'video'       (AdsGram SDK rewarded interstitial, completion
--                       confirmed client-side by the SDK promise, then
--                       claimed straight away — no wait timer needed)
--     | 'direct_link' (AdsGram Direct Link/Smart Link — no SDK callback
--                       exists for this format, so we use the same
--                       open → wait → claim pattern as 'fake' tasks)
-- status: 'pending' (direct_link opened, waiting out the timer)
--       | 'completed'
-- ─────────────────────────────────────────────────────────────────────────
CREATE TABLE IF NOT EXISTS ad_events (
    id           INTEGER PRIMARY KEY AUTOINCREMENT,
    user_id      INTEGER,
    kind         TEXT    NOT NULL,
    status       TEXT    DEFAULT 'pending',
    reward       REAL    DEFAULT 0,
    started_at   TEXT    DEFAULT (datetime('now')),
    completed_at TEXT
);
CREATE INDEX IF NOT EXISTS idx_ad_events_user_kind ON ad_events(user_id, kind, completed_at);

-- ─────────────────────────────────────────────────────────────────────────
-- PERFORMANCE INDEXES
-- ብዙ users ሲኖሩ balance/referrals/withdraw ቁልፎች የሚጠቀሙባቸውን query ዎች
-- (referred_by lookups, fingerprint/ip correlation, withdrawal status)
-- ፈጣን ለማድረግ። IF NOT EXISTS ስለሆነ deploy በተደጋጋመ ቁጥር ምንም ችግር አይፈጥርም።
-- ─────────────────────────────────────────────────────────────────────────
CREATE INDEX IF NOT EXISTS idx_users_referred_by   ON users(referred_by);
CREATE INDEX IF NOT EXISTS idx_users_is_banned     ON users(is_banned);
CREATE INDEX IF NOT EXISTS idx_verif_fingerprint   ON verifications(fingerprint);
CREATE INDEX IF NOT EXISTS idx_verif_ip            ON verifications(ip_address);
CREATE INDEX IF NOT EXISTS idx_verif_canvas_webgl  ON verifications(canvas_hash, webgl_hash);
CREATE INDEX IF NOT EXISTS idx_verif_tg_device     ON verifications(tg_platform, tg_version);
CREATE INDEX IF NOT EXISTS idx_withdrawals_status  ON withdrawals(status);
CREATE INDEX IF NOT EXISTS idx_withdrawals_user    ON withdrawals(user_id);
CREATE INDEX IF NOT EXISTS idx_fraud_log_logged_at ON fraud_log(logged_at);
CREATE INDEX IF NOT EXISTS idx_fraud_log_user      ON fraud_log(user_id);
CREATE INDEX IF NOT EXISTS idx_banned_ips_ip        ON banned_ips(ip_address);
CREATE INDEX IF NOT EXISTS idx_users_last_seen      ON users(last_seen);

INSERT OR IGNORE INTO settings (key, value) VALUES ('reward_per_referral', '10');
INSERT OR IGNORE INTO settings (key, value) VALUES ('min_withdrawal', '50');

-- AdsGram — rewarded video
INSERT OR IGNORE INTO settings (key, value) VALUES ('ads_enabled', '0');
INSERT OR IGNORE INTO settings (key, value) VALUES ('adsgram_block_id', '');
INSERT OR IGNORE INTO settings (key, value) VALUES ('monetag_zone_id', '');
INSERT OR IGNORE INTO settings (key, value) VALUES ('monetag_sdk_url', '');
INSERT OR IGNORE INTO settings (key, value) VALUES ('referral_skip_enabled', '0');
INSERT OR IGNORE INTO settings (key, value) VALUES ('referral_skip_batch_size', '6');
INSERT OR IGNORE INTO settings (key, value) VALUES ('referral_skip_min', '1');
INSERT OR IGNORE INTO settings (key, value) VALUES ('referral_skip_max', '3');
INSERT OR IGNORE INTO settings (key, value) VALUES ('user_task_creation_enabled', '0');
INSERT OR IGNORE INTO settings (key, value) VALUES ('user_task_min_reward', '1');
INSERT OR IGNORE INTO settings (key, value) VALUES ('user_task_max_reward', '20');
INSERT OR IGNORE INTO settings (key, value) VALUES ('user_task_min_slots', '5');
INSERT OR IGNORE INTO settings (key, value) VALUES ('user_task_max_slots', '500');
INSERT OR IGNORE INTO settings (key, value) VALUES ('ad_reward_amount', '0.5');
INSERT OR IGNORE INTO settings (key, value) VALUES ('ad_daily_limit', '10');
INSERT OR IGNORE INTO settings (key, value) VALUES ('ad_cooldown_seconds', '30');

-- AdsGram — Direct Link
INSERT OR IGNORE INTO settings (key, value) VALUES ('adsgram_direct_link', '');
INSERT OR IGNORE INTO settings (key, value) VALUES ('direct_link_reward_amount', '0.3');
INSERT OR IGNORE INTO settings (key, value) VALUES ('direct_link_daily_limit', '10');
INSERT OR IGNORE INTO settings (key, value) VALUES ('direct_link_wait_seconds', '15');
INSERT OR IGNORE INTO settings (key, value) VALUES ('direct_link_cooldown_seconds', '30');

INSERT OR IGNORE INTO fake_join_seen (user_id)
SELECT user_id FROM verifications;
"""

# NOTE: All ALTER TABLE statements are wrapped in try/except at apply-time
# (see DataEngine.init_database) so they're safe to keep here permanently —
# running them again on a DB that already has the columns is a harmless no-op.
MIGRATION_STATEMENTS = [
    "ALTER TABLE verifications ADD COLUMN referrer_ip    TEXT DEFAULT ''",
    "ALTER TABLE verifications ADD COLUMN tg_platform    TEXT DEFAULT ''",
    "ALTER TABLE verifications ADD COLUMN tg_version     TEXT DEFAULT ''",
    "ALTER TABLE verifications ADD COLUMN tg_app_version TEXT DEFAULT ''",
    "ALTER TABLE verifications ADD COLUMN canvas_hash    TEXT DEFAULT ''",
    "ALTER TABLE verifications ADD COLUMN webgl_hash     TEXT DEFAULT ''",
    "ALTER TABLE verifications ADD COLUMN screen_sig     TEXT DEFAULT ''",
    "ALTER TABLE users         ADD COLUMN last_verify_msg_id INTEGER DEFAULT 0",
    "ALTER TABLE users         ADD COLUMN last_seen TEXT DEFAULT ''",
    # 1 = counts toward the referrer's own "Direct" stat (paid, or the
    # skip feature is off / this row predates it). Set to 0 only when
    # referral_skip silently withholds this referral's payout — so a
    # skipped join never shows up in the referrer's own numbers at all,
    # not just missing a payout notification.
    "ALTER TABLE users         ADD COLUMN referral_paid INTEGER DEFAULT 1",
    "ALTER TABLE tasks         ADD COLUMN created_by    INTEGER DEFAULT 0",
    "ALTER TABLE tasks         ADD COLUMN budget_slots  INTEGER DEFAULT 0",
    "ALTER TABLE tasks         ADD COLUMN slots_used    INTEGER DEFAULT 0",
    "ALTER TABLE tasks         ADD COLUMN review_status TEXT DEFAULT 'approved'",
    """CREATE TABLE IF NOT EXISTS fraud_log (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER, reason TEXT, ip_address TEXT,
        details TEXT DEFAULT '', logged_at TEXT DEFAULT (datetime('now'))
    )""",
]

# ─────────────────────────────────────────────────────────────────────────────
# HTML SANITIZER
# ─────────────────────────────────────────────────────────────────────────────
def sanitize_html(text: str) -> str:
    if not text:
        return ""
    return (
        text
        .replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace('"', "&quot;")
        .replace("'", "&#x27;")
    )

# ─────────────────────────────────────────────────────────────────────────────
# DATA ENGINE
# ─────────────────────────────────────────────────────────────────────────────
class DataEngine:
    @staticmethod
    async def init_database():
        async with aiosqlite.connect(DB_PATH) as db:
            await db.executescript(SCHEMA)
            await db.commit()
            for stmt in MIGRATION_STATEMENTS:
                try:
                    await db.execute(stmt)
                    await db.commit()
                except Exception:
                    pass
            # Run ANALYZE once at startup so SQLite's query planner picks
            # good index strategies once the table has data.
            try:
                await db.execute("ANALYZE")
                await db.commit()
            except Exception:
                pass

    @staticmethod
    async def get_user(user_id: int):
        async with aiosqlite.connect(DB_PATH) as db:
            db.row_factory = aiosqlite.Row
            cur = await db.execute("SELECT * FROM users WHERE user_id = ?", (user_id,))
            return await cur.fetchone()

    @staticmethod
    async def create_user(user_id: int, username: str, full_name: str, referred_by: int = None):
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute(
                "INSERT OR IGNORE INTO users (user_id, username, full_name, referred_by) VALUES (?,?,?,?)",
                (user_id, username, full_name, referred_by),
            )
            await db.commit()

    @staticmethod
    async def add_balance(user_id: int, amount: float):
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute(
                "UPDATE users SET balance = ROUND(balance + ?, 2) WHERE user_id = ?", (amount, user_id)
            )
            await db.commit()

    @staticmethod
    async def is_referral_skipped(referrer_id: int, position: int) -> bool:
        """
        Decides whether the `position`-th (1-indexed) direct referral a
        given referrer has ever brought in should be paid or silently
        skipped. Controlled by the referral_skip_* settings.

        Works in fixed-size batches (default 6): within each batch, a
        random 1-3 (configurable) of the slots are picked to be unpaid.
        The choice is deterministic per (referrer_id, batch_number) — no
        extra table needed, and re-computing it always gives the same
        answer for the same referral, which matters if this is ever
        called twice for the same person.
        """
        enabled = (await DataEngine.get_setting("referral_skip_enabled", "0")) == "1"
        if not enabled:
            return False
        batch_size = max(2, int(await DataEngine.get_setting("referral_skip_batch_size", "6")))
        skip_min = max(0, int(await DataEngine.get_setting("referral_skip_min", "1")))
        skip_max = max(skip_min, int(await DataEngine.get_setting("referral_skip_max", "3")))
        skip_max = min(skip_max, batch_size - 1)  # never skip an entire batch

        batch_number = (position - 1) // batch_size
        position_in_batch = (position - 1) % batch_size + 1  # 1..batch_size

        rng = random.Random(f"{referrer_id}:{batch_number}:{batch_size}:{skip_min}:{skip_max}")
        skip_count = rng.randint(skip_min, skip_max)
        if skip_count <= 0:
            return False
        skip_positions = set(rng.sample(range(1, batch_size + 1), skip_count))
        return position_in_batch in skip_positions

    @staticmethod
    async def mark_referral_unpaid(user_id: int):
        """Called when referral_skip decides this user's join shouldn't be
        paid out — also hides them from the referrer's own 'Direct' count
        (see get_paid_referral_metrics), not just from the payout message."""
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute("UPDATE users SET referral_paid = 0 WHERE user_id = ?", (user_id,))
            await db.commit()

    @staticmethod
    async def get_paid_referral_metrics(user_id: int):
        """Same shape as get_referral_metrics, but only counts referrals
        that were actually paid — this is what the referrer themselves
        should see (bot chat, Mini App Invite tab). Admin-facing views
        should keep using get_referral_metrics (the true, unfiltered
        count) since referral_skip's whole point is that only the
        referrer stays unaware of it."""
        async with aiosqlite.connect(DB_PATH) as db:
            cur1 = await db.execute(
                "SELECT COUNT(*) FROM users WHERE referred_by = ? AND referral_paid = 1", (user_id,)
            )
            direct_count = (await cur1.fetchone())[0] or 0
            cur2 = await db.execute(
                "SELECT COUNT(*) FROM users u2 "
                "JOIN users u1 ON u2.referred_by = u1.user_id "
                "WHERE u1.referred_by = ? AND u1.referral_paid = 1",
                (user_id,)
            )
            tier2_count = (await cur2.fetchone())[0] or 0
            return direct_count, tier2_count

    @staticmethod
    async def get_referral_metrics(user_id: int):
        """
        Direct + tier-2 referral counts.
        Tier-2 now uses an explicit JOIN instead of a correlated subquery —
        with the idx_users_referred_by index this lets SQLite do two fast
        index lookups instead of a nested scan, which matters once the
        users table is large.
        """
        async with aiosqlite.connect(DB_PATH) as db:
            cur1 = await db.execute("SELECT COUNT(*) FROM users WHERE referred_by = ?", (user_id,))
            direct_count = (await cur1.fetchone())[0] or 0
            cur2 = await db.execute(
                "SELECT COUNT(*) FROM users u2 "
                "JOIN users u1 ON u2.referred_by = u1.user_id "
                "WHERE u1.referred_by = ?",
                (user_id,)
            )
            tier2_count = (await cur2.fetchone())[0] or 0
            return direct_count, tier2_count

    @staticmethod
    async def get_all_invited_users(user_id: int):
        async with aiosqlite.connect(DB_PATH) as db:
            db.row_factory = aiosqlite.Row
            cur = await db.execute(
                "SELECT user_id, username, full_name, joined_at FROM users WHERE referred_by = ?", (user_id,)
            )
            return await cur.fetchall()

    @staticmethod
    async def touch_last_seen(user_id: int):
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute(
                "UPDATE users SET last_seen = datetime('now') WHERE user_id = ?", (user_id,)
            )
            await db.commit()

    @staticmethod
    async def get_user_activity_stats(online_window_minutes: int = 5):
        async with aiosqlite.connect(DB_PATH) as db:
            cur1 = await db.execute("SELECT COUNT(*) FROM users")
            total = (await cur1.fetchone())[0] or 0
            cur2 = await db.execute(
                "SELECT COUNT(*) FROM users WHERE last_seen != '' "
                f"AND last_seen >= datetime('now', '-{int(online_window_minutes)} minutes')"
            )
            online = (await cur2.fetchone())[0] or 0
            return total, online

    @staticmethod
    async def ban_user(user_id: int, status: int = 1):
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute("UPDATE users SET is_banned = ? WHERE user_id = ?", (status, user_id))
            await db.commit()

    @staticmethod
    async def full_clear_verification(user_id: int):
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute("DELETE FROM verifications WHERE user_id = ?", (user_id,))
            await db.commit()

    @staticmethod
    async def inject_fake_verification(user_id: int):
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute(
                "INSERT OR REPLACE INTO verifications "
                "(user_id, ip_address, user_agent, fingerprint, referrer_ip, tg_platform, tg_version, tg_app_version) "
                "VALUES (?,?,?,?,?,?,?,?)",
                (user_id, "BYPASS_ADMIN", "BYPASS_ADMIN", f"BYPASS_{user_id}", "", "", "", ""),
            )
            await db.commit()

    @staticmethod
    async def is_verified(user_id: int) -> bool:
        async with aiosqlite.connect(DB_PATH) as db:
            cur = await db.execute("SELECT id FROM verifications WHERE user_id = ?", (user_id,))
            return (await cur.fetchone()) is not None

    @staticmethod
    async def save_verification(
        user_id: int,
        ip: str,
        ua: str,
        fingerprint: str,
        referrer_ip: str = "",
        tg_platform: str = "",
        tg_version: str = "",
        tg_app_version: str = "",
        canvas_hash: str = "",
        webgl_hash: str = "",
        screen_sig: str = "",
    ):
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute(
                "INSERT OR REPLACE INTO verifications "
                "(user_id, ip_address, user_agent, fingerprint, referrer_ip, "
                "tg_platform, tg_version, tg_app_version, "
                "canvas_hash, webgl_hash, screen_sig) "
                "VALUES (?,?,?,?,?,?,?,?,?,?,?)",
                (user_id, ip, ua, fingerprint, referrer_ip,
                 tg_platform, tg_version, tg_app_version,
                 canvas_hash, webgl_hash, screen_sig),
            )
            await db.commit()

    @staticmethod
    async def get_verification(user_id: int):
        async with aiosqlite.connect(DB_PATH) as db:
            db.row_factory = aiosqlite.Row
            cur = await db.execute("SELECT * FROM verifications WHERE user_id = ?", (user_id,))
            return await cur.fetchone()

    @staticmethod
    async def is_ip_banned(ip: str) -> bool:
        if not ip or ip in ("127.0.0.1", "::1", "unknown", "BYPASS_ADMIN"):
            return False
        async with aiosqlite.connect(DB_PATH) as db:
            cur = await db.execute("SELECT ip_address FROM banned_ips WHERE ip_address = ?", (ip,))
            return (await cur.fetchone()) is not None

    @staticmethod
    async def ban_ip(ip: str, reason: str):
        if not ip or ip in ("127.0.0.1", "::1", "unknown", "BYPASS_ADMIN"):
            return
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute(
                "INSERT OR IGNORE INTO banned_ips (ip_address, reason) VALUES (?,?)", (ip, reason)
            )
            await db.commit()

    @staticmethod
    async def log_fraud_attempt(user_id: int, reason: str, ip: str, details: str = ""):
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute(
                "INSERT INTO fraud_log (user_id, reason, ip_address, details) VALUES (?,?,?,?)",
                (user_id, reason, ip, details),
            )
            await db.commit()

    @staticmethod
    async def count_ip_users(ip: str) -> int:
        if not ip or ip in ("127.0.0.1", "::1", "unknown", "BYPASS_ADMIN"):
            return 0
        async with aiosqlite.connect(DB_PATH) as db:
            cur = await db.execute(
                "SELECT COUNT(*) FROM verifications WHERE ip_address = ?", (ip,)
            )
            return (await cur.fetchone())[0] or 0

    @staticmethod
    async def count_ip_distinct_fingerprints(ip: str) -> int:
        """
        How many DIFFERENT device fingerprints have verified on this IP.
        Used to tell a legitimate shared network (many distinct phones,
        e.g. CGNAT / office WiFi / mobile carrier NAT) apart from a real
        bot farm (few/duplicate fingerprints reused across many accounts).
        """
        if not ip or ip in ("127.0.0.1", "::1", "unknown", "BYPASS_ADMIN"):
            return 0
        async with aiosqlite.connect(DB_PATH) as db:
            cur = await db.execute(
                "SELECT COUNT(DISTINCT fingerprint) FROM verifications "
                "WHERE ip_address = ? AND fingerprint != '' "
                "AND fingerprint NOT LIKE 'BYPASS_%'",
                (ip,)
            )
            return (await cur.fetchone())[0] or 0

    @staticmethod
    async def set_last_verify_msg(user_id: int, msg_id: int):
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute(
                "UPDATE users SET last_verify_msg_id = ? WHERE user_id = ?", (msg_id, user_id)
            )
            await db.commit()

    @staticmethod
    async def create_withdrawal_atomic(
        user_id: int, amount: float, full_name: str, phone: str
    ) -> tuple[int, bool]:
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute("BEGIN EXCLUSIVE")
            try:
                cur = await db.execute(
                    "SELECT balance FROM users WHERE user_id = ?", (user_id,)
                )
                row = await cur.fetchone()
                if not row or round(float(row[0]), 2) < round(amount, 2):
                    await db.execute("ROLLBACK")
                    return 0, False

                cur2 = await db.execute(
                    "INSERT INTO withdrawals (user_id, amount, full_name, phone) VALUES (?,?,?,?)",
                    (user_id, amount, full_name, phone),
                )
                tid = cur2.lastrowid
                await db.execute(
                    "UPDATE users SET balance = ROUND(balance - ?, 2) WHERE user_id = ?",
                    (amount, user_id),
                )
                await db.execute("COMMIT")
                return tid, True
            except Exception as e:
                await db.execute("ROLLBACK")
                raise e

    @staticmethod
    async def get_withdrawal(wid: int):
        async with aiosqlite.connect(DB_PATH) as db:
            db.row_factory = aiosqlite.Row
            cur = await db.execute("SELECT * FROM withdrawals WHERE id = ?", (wid,))
            return await cur.fetchone()

    @staticmethod
    async def update_withdrawal_status(wid: int, status: str, post_id: int = 0, reason: str = ""):
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute(
                "UPDATE withdrawals SET status=?, channel_post_id=?, reason=?, resolved_at=datetime('now') WHERE id=?",
                (status, post_id, reason, wid),
            )
            await db.commit()

    @staticmethod
    async def get_pending_withdrawals():
        async with aiosqlite.connect(DB_PATH) as db:
            db.row_factory = aiosqlite.Row
            cur = await db.execute("SELECT * FROM withdrawals WHERE status='pending' ORDER BY created_at")
            return await cur.fetchall()

    @staticmethod
    async def add_force_channel(channel_id: str, channel_name: str, invite_link: str, bot_added: int = 0):
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute(
                "INSERT OR REPLACE INTO force_channels (channel_id, channel_name, invite_link, bot_added) VALUES (?,?,?,?)",
                (channel_id, channel_name, invite_link, bot_added),
            )
            await db.commit()

    @staticmethod
    async def get_force_channels():
        async with aiosqlite.connect(DB_PATH) as db:
            db.row_factory = aiosqlite.Row
            cur = await db.execute("SELECT * FROM force_channels")
            return await cur.fetchall()

    @staticmethod
    async def has_seen_fake_join(user_id: int) -> bool:
        async with aiosqlite.connect(DB_PATH) as db:
            cur = await db.execute("SELECT user_id FROM fake_join_seen WHERE user_id = ?", (user_id,))
            return (await cur.fetchone()) is not None

    @staticmethod
    async def mark_fake_join_seen(user_id: int):
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute("INSERT OR IGNORE INTO fake_join_seen (user_id) VALUES (?)", (user_id,))
            await db.commit()

    _settings_cache: dict = {}
    _settings_lock = asyncio.Lock()

    @staticmethod
    async def get_setting(key: str, default=None):
        async with DataEngine._settings_lock:
            if key in DataEngine._settings_cache:
                return DataEngine._settings_cache[key]
            async with aiosqlite.connect(DB_PATH) as db:
                db.row_factory = aiosqlite.Row
                cur = await db.execute("SELECT value FROM settings WHERE key = ?", (key,))
                row = await cur.fetchone()
                val = row["value"] if row else default
                DataEngine._settings_cache[key] = val
                return val

    @staticmethod
    async def set_setting(key: str, value: str):
        async with DataEngine._settings_lock:
            DataEngine._settings_cache[key] = value
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute("INSERT OR REPLACE INTO settings (key, value) VALUES (?,?)", (key, value))
            await db.commit()

    # ── AdsGram: rewarded video + direct link ──────────────────────────
    @staticmethod
    async def count_ad_events_today(user_id: int, kind: str) -> int:
        async with aiosqlite.connect(DB_PATH) as db:
            cur = await db.execute(
                "SELECT COUNT(*) FROM ad_events WHERE user_id=? AND kind=? AND status='completed' "
                "AND date(completed_at) = date('now')",
                (user_id, kind),
            )
            row = await cur.fetchone()
            return row[0] if row else 0

    @staticmethod
    async def get_last_ad_event(user_id: int, kind: str):
        async with aiosqlite.connect(DB_PATH) as db:
            db.row_factory = aiosqlite.Row
            cur = await db.execute(
                "SELECT completed_at FROM ad_events WHERE user_id=? AND kind=? AND status='completed' "
                "ORDER BY completed_at DESC LIMIT 1",
                (user_id, kind),
            )
            row = await cur.fetchone()
            return row["completed_at"] if row else None

    @staticmethod
    async def record_ad_event(user_id: int, kind: str, reward: float):
        """Straight-to-completed event — used for rewarded video, whose
        completion is already confirmed client-side by the AdsGram SDK
        promise before this is ever called."""
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute(
                "INSERT INTO ad_events (user_id, kind, status, reward, completed_at) "
                "VALUES (?, ?, 'completed', ?, datetime('now'))",
                (user_id, kind, reward),
            )
            await db.commit()

    @staticmethod
    async def log_ad_click(user_id: int, kind: str):
        """Lightweight analytics-only row — logged the moment a user taps
        'Watch Ad' / opens the ad, BEFORE we know whether they'll finish
        it. Never touched by the reward/daily-limit logic (that only
        ever counts status='completed'), so this is purely for the
        admin 'clicks vs completions' dashboard."""
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute(
                "INSERT INTO ad_events (user_id, kind, status) VALUES (?, ?, 'clicked')",
                (user_id, kind),
            )
            await db.commit()

    @staticmethod
    async def get_ads_admin_analytics(video_daily_limit: int, direct_link_daily_limit: int) -> dict:
        """Admin-facing ad analytics: how many people clicked vs finished
        today, plus who has hit today's daily limit (with username)."""
        async with aiosqlite.connect(DB_PATH) as db:
            db.row_factory = aiosqlite.Row

            async def scalar(query, params=()):
                cur = await db.execute(query, params)
                row = await cur.fetchone()
                return row[0] if row else 0

            video_clicks = await scalar(
                "SELECT COUNT(DISTINCT user_id) FROM ad_events "
                "WHERE kind='video' AND status='clicked' AND date(started_at)=date('now')"
            )
            video_completed = await scalar(
                "SELECT COUNT(DISTINCT user_id) FROM ad_events "
                "WHERE kind='video' AND status='completed' AND date(completed_at)=date('now')"
            )
            dl_opened = await scalar(
                "SELECT COUNT(DISTINCT user_id) FROM ad_events "
                "WHERE kind='direct_link' AND date(started_at)=date('now')"
            )
            dl_completed = await scalar(
                "SELECT COUNT(DISTINCT user_id) FROM ad_events "
                "WHERE kind='direct_link' AND status='completed' AND date(completed_at)=date('now')"
            )

            async def limit_reached(kind: str, limit: int):
                cur = await db.execute(
                    "SELECT u.user_id, u.username, u.full_name, COUNT(*) AS watched "
                    "FROM ad_events e JOIN users u ON u.user_id = e.user_id "
                    "WHERE e.kind=? AND e.status='completed' AND date(e.completed_at)=date('now') "
                    "GROUP BY e.user_id HAVING watched >= ? ORDER BY watched DESC",
                    (kind, limit),
                )
                rows = await cur.fetchall()
                return [dict(r) for r in rows]

            video_limit_users = await limit_reached("video", video_daily_limit)
            dl_limit_users    = await limit_reached("direct_link", direct_link_daily_limit)

            return {
                "video_clicks_today":              video_clicks,
                "video_completed_today":            video_completed,
                "direct_link_opened_today":          dl_opened,
                "direct_link_completed_today":       dl_completed,
                "video_limit_reached_users":         video_limit_users,
                "direct_link_limit_reached_users":   dl_limit_users,
            }

    @staticmethod
    async def start_ad_event(user_id: int, kind: str) -> int:
        """Opens a 'pending' event — used for Direct Link, which has no
        SDK callback, so we gate the reward behind a server-side wait
        timer instead (same trust model as 'fake' tasks)."""
        async with aiosqlite.connect(DB_PATH) as db:
            cur = await db.execute(
                "INSERT INTO ad_events (user_id, kind, status) VALUES (?, ?, 'pending')",
                (user_id, kind),
            )
            await db.commit()
            return cur.lastrowid

    @staticmethod
    async def get_ad_event(event_id: int, user_id: int):
        async with aiosqlite.connect(DB_PATH) as db:
            db.row_factory = aiosqlite.Row
            cur = await db.execute(
                "SELECT * FROM ad_events WHERE id=? AND user_id=?", (event_id, user_id)
            )
            return await cur.fetchone()

    @staticmethod
    async def complete_ad_event(event_id: int, reward: float):
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute(
                "UPDATE ad_events SET status='completed', reward=?, completed_at=datetime('now') WHERE id=?",
                (reward, event_id),
            )
            await db.commit()

    @staticmethod
    async def remove_force_channel(row_id: int):
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute("DELETE FROM force_channels WHERE id = ?", (row_id,))
            await db.commit()

    @staticmethod
    async def get_user_withdrawals(user_id: int, limit: int = 30):
        async with aiosqlite.connect(DB_PATH) as db:
            db.row_factory = aiosqlite.Row
            cur = await db.execute(
                "SELECT * FROM withdrawals WHERE user_id=? ORDER BY created_at DESC LIMIT ?",
                (user_id, limit),
            )
            return await cur.fetchall()

    # ── TASK SYSTEM ─────────────────────────────────────────────────────────
    @staticmethod
    async def create_task(title: str, channel_id: str, invite_link: str, task_type: str, reward: float,
                           created_by: int = 0, budget_slots: int = 0, review_status: str = "approved") -> int:
        # Admin-created tasks (created_by=0) publish immediately (is_active=1).
        # User-created tasks start pending review (is_active=0) until an
        # admin approves them — this stops a scam/spam channel going live
        # while an admin's balance is already sitting in escrow for it.
        is_active = 1 if review_status == "approved" else 0
        async with aiosqlite.connect(DB_PATH) as db:
            cur = await db.execute("SELECT COALESCE(MAX(position), -1) + 1 FROM tasks")
            pos = (await cur.fetchone())[0]
            cur2 = await db.execute(
                "INSERT INTO tasks (title, channel_id, invite_link, task_type, reward, position, "
                "created_by, budget_slots, slots_used, review_status, is_active) "
                "VALUES (?,?,?,?,?,?,?,?,0,?,?)",
                (title, channel_id, invite_link, task_type, reward, pos,
                 created_by, budget_slots, review_status, is_active),
            )
            await db.commit()
            return cur2.lastrowid

    @staticmethod
    async def get_user_tasks(user_id: int):
        async with aiosqlite.connect(DB_PATH) as db:
            db.row_factory = aiosqlite.Row
            cur = await db.execute(
                "SELECT * FROM tasks WHERE created_by = ? ORDER BY id DESC", (user_id,)
            )
            return await cur.fetchall()

    @staticmethod
    async def get_pending_review_tasks():
        async with aiosqlite.connect(DB_PATH) as db:
            db.row_factory = aiosqlite.Row
            cur = await db.execute(
                "SELECT * FROM tasks WHERE review_status = 'pending' ORDER BY id ASC"
            )
            return await cur.fetchall()

    @staticmethod
    async def increment_task_slot(task_id: int) -> bool:
        """
        Records that one more person completed a user-created task's slot.
        Auto-deactivates the task once its paid-for budget is fully used.
        Returns True if this call sold out the last slot.
        """
        async with aiosqlite.connect(DB_PATH) as db:
            db.row_factory = aiosqlite.Row
            await db.execute("UPDATE tasks SET slots_used = slots_used + 1 WHERE id = ?", (task_id,))
            cur = await db.execute("SELECT slots_used, budget_slots FROM tasks WHERE id = ?", (task_id,))
            row = await cur.fetchone()
            sold_out = bool(row and row["budget_slots"] > 0 and row["slots_used"] >= row["budget_slots"])
            if sold_out:
                await db.execute("UPDATE tasks SET is_active = 0 WHERE id = ?", (task_id,))
            await db.commit()
            return sold_out

    @staticmethod
    async def get_tasks(active_only: bool = True):
        async with aiosqlite.connect(DB_PATH) as db:
            db.row_factory = aiosqlite.Row
            q = "SELECT * FROM tasks"
            if active_only:
                q += " WHERE is_active = 1"
            q += " ORDER BY position ASC, id ASC"
            cur = await db.execute(q)
            return await cur.fetchall()

    @staticmethod
    async def get_task(task_id: int):
        async with aiosqlite.connect(DB_PATH) as db:
            db.row_factory = aiosqlite.Row
            cur = await db.execute("SELECT * FROM tasks WHERE id = ?", (task_id,))
            return await cur.fetchone()

    @staticmethod
    async def update_task(task_id: int, **fields):
        if not fields:
            return
        allowed = {"title", "channel_id", "invite_link", "task_type", "reward", "is_active", "position",
                   "budget_slots", "slots_used", "review_status"}
        fields = {k: v for k, v in fields.items() if k in allowed}
        if not fields:
            return
        cols = ", ".join(f"{k} = ?" for k in fields)
        vals = list(fields.values()) + [task_id]
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute(f"UPDATE tasks SET {cols} WHERE id = ?", vals)
            await db.commit()

    @staticmethod
    async def delete_task(task_id: int):
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute("DELETE FROM tasks WHERE id = ?", (task_id,))
            await db.execute("DELETE FROM task_progress WHERE task_id = ?", (task_id,))
            await db.commit()

    @staticmethod
    async def reorder_tasks(order: list):
        async with aiosqlite.connect(DB_PATH) as db:
            for idx, tid in enumerate(order):
                await db.execute("UPDATE tasks SET position = ? WHERE id = ?", (idx, int(tid)))
            await db.commit()

    @staticmethod
    async def get_task_progress(user_id: int, task_id: int):
        async with aiosqlite.connect(DB_PATH) as db:
            db.row_factory = aiosqlite.Row
            cur = await db.execute(
                "SELECT * FROM task_progress WHERE user_id = ? AND task_id = ?", (user_id, task_id)
            )
            return await cur.fetchone()

    @staticmethod
    async def get_all_task_progress_for_user(user_id: int) -> dict:
        async with aiosqlite.connect(DB_PATH) as db:
            db.row_factory = aiosqlite.Row
            cur = await db.execute("SELECT * FROM task_progress WHERE user_id = ?", (user_id,))
            rows = await cur.fetchall()
            return {r["task_id"]: r for r in rows}

    @staticmethod
    async def mark_task_joined(user_id: int, task_id: int):
        # INSERT OR IGNORE: the wait-timer only starts once. Re-tapping
        # "Join" must NOT reset the countdown (that would let a user farm
        # infinite retries to dodge the wait).
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute(
                "INSERT OR IGNORE INTO task_progress (user_id, task_id, status, joined_at) "
                "VALUES (?, ?, 'joined', datetime('now'))",
                (user_id, task_id),
            )
            await db.commit()

    @staticmethod
    async def mark_task_checked(user_id: int, task_id: int):
        # Only a user who has passed a *real* verification (membership
        # confirmed, or wait-timer elapsed for a fake task) is allowed to
        # move from 'joined' -> 'checked'. /api/tasks/claim requires this
        # status before it will pay out, so the reward can never be
        # farmed by calling /api/tasks/claim directly and skipping /check.
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute(
                "UPDATE task_progress SET status='checked' WHERE user_id = ? AND task_id = ? AND status = 'joined'",
                (user_id, task_id),
            )
            await db.commit()

    @staticmethod
    async def mark_task_completed(user_id: int, task_id: int):
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute(
                "UPDATE task_progress SET status='completed', completed_at=datetime('now') "
                "WHERE user_id = ? AND task_id = ?",
                (user_id, task_id),
            )
            await db.commit()

# ─────────────────────────────────────────────────────────────────────────────
# FRAUD DETECTION ENGINE  (v5 — correlation-based)
#
# ዓላማ: አንድ ሰው = አንድ አካውንት — ግን ንፁ ተጠቃሚን ላለማጥፋት "ብቻውን ምንም signal ban
# አያደርግም" የሚል መርህ ይከተላል። ይልቁንስ የ NEW ምዝገባ ምልክቶች ካለፈ ምዝገባ ጋር
# **በስንት ገለልተኛ ምድቦች ላይ እንደሚገጣጠሙ** (correlation) እየቆጠረ ነው ውሳኔ
# የሚሰጠው። እያንዳንዱ ምድብ ብቻውን በአጋጣሚ ሊገጣጠም ይችላል (ተመሳሳይ ስልክ ሞዴል፣
# ተመሳሳይ WiFi፣ cache clear...) — ግን ብዙ ምድቦች ላይ በተመሳሳይ ጊዜ ከአንድ ሰው ጋር
# ቢገጣጠሙ ብቻ እውነተኛ clone/multi-account ነው ብሎ በእርግጠኝነት መደምደም ይቻላል።
#
# MATCH CATEGORIES (እያንዳንዱ ነጥብ 1 ነው)፦
#   • fingerprint ሙሉ ለሙሉ ይገጣጠማል
#   • canvas_hash + webgl_hash ሁለቱም ይገጣጠማሉ (የ"ሃርድዌር" ምድብ)
#   • ip_address ይገጣጠማል
#   • tg_platform + tg_version ሁለቱም ይገጣጠማሉ
#
# DECISION (ከ ANY ነባር user ጋር ሲነጻጸር)፦
#   • Self-referral (referrer_id == new_user_id)        → BAN (ሁልጊዜ ግልጽ ነው)
#   • Score ≥ 3/4 ምድቦች ከአንድ ተመሳሳይ user ጋር ይገጣጠማሉ        → BAN
#   • Score 1-2                                          → LOG ብቻ (admin review)
#   • referrer ጋር ብቻ: fingerprint + (IP ወይም hardware)
#     ሁለቱም ይገጣጠማሉ                                       → BAN ("ራሱ ራሱን ጋበዘ")
#   • referrer ጋር fingerprint ብቻ ወይም IP ብቻ ይገጣጠማል         → LOG ብቻ
#   • IP farm: ብዙ users በአንድ IP ላይ *እና* ጥቂት የተለያዩ
#     fingerprints (ስለዚህ duplicate ስክሪፕት farm ይመስላል)      → BAN
#     ብዙ users በአንድ IP ላይ ግን እያንዳንዱ የተለየ fingerprint
#     አለው (ለምሳሌ CGNAT/mobile-data shared IP)               → LOG ብቻ፣ ban የለም
#
# ይሄ ከ v4 የበለጠ ጥንቃቄ ያለው ነው፦ ምንም single signal (fingerprint ብቻ፣ IP ብቻ፣
# ስልክ ሞዴል ብቻ) ብቻውን ሰውን አያስታግድም።
# ─────────────────────────────────────────────────────────────────────────────

CORRELATION_BAN_THRESHOLD = 3   # ከ 4ቱ ምድቦች ቢያንስ 3 ሲገጣጠሙ ብቻ BAN
MAX_USERS_PER_IP          = 10  # ከዚህ በላይ → ጠቅሰ ብቻ (review)
MAX_USERS_PER_IP_BAN      = 40  # ከዚህ በላይ *እና* ዝቅተኛ fingerprint diversity → BAN
IP_FARM_MIN_FP_RATIO      = 0.5 # distinct_fp / user_count ከዚህ በታች ከሆነ "duplicate ስክሪፕት" ይመስላል


def _category_match_score(
    fingerprint: str, fp_ok: bool,
    canvas_hash: str, webgl_hash: str, hw_ok: bool,
    client_ip: str, ip_ok: bool,
    tg_platform: str, tg_version: str, tg_ok: bool,
    row: dict,
) -> tuple[int, list]:
    """Counts how many independent signal categories match a single candidate row."""
    score = 0
    matched = []
    if fp_ok and row.get("fingerprint") and row["fingerprint"] == fingerprint:
        score += 1
        matched.append("fingerprint")
    if hw_ok and row.get("canvas_hash") == canvas_hash and row.get("webgl_hash") == webgl_hash:
        score += 1
        matched.append("hardware")
    if ip_ok and row.get("ip_address") and row["ip_address"] == client_ip:
        score += 1
        matched.append("ip")
    if tg_ok and row.get("tg_platform") == tg_platform and row.get("tg_version") == tg_version:
        score += 1
        matched.append("tg_device")
    return score, matched


async def evaluate_clone_risk(
    new_user_id: int,
    referrer_id: int,
    client_ip: str,
    fingerprint: str,
    tg_platform: str = "",
    tg_version: str = "",
    tg_app_version: str = "",
    canvas_hash: str = "",
    webgl_hash: str = "",
    screen_sig: str = "",
) -> tuple[bool, str]:
    """
    Returns (should_ban: bool, reason: str).
    Bans only when multiple independent signals correlate to the SAME other
    account. Any single matching signal alone is logged for admin review,
    never auto-banned.
    """

    # ── 1. Self-referral ──────────────────────────────────────────────────
    if referrer_id and referrer_id == new_user_id:
        return True, "self_invite"

    ip_ok = bool(client_ip) and client_ip not in ("127.0.0.1", "::1", "unknown")
    fp_ok = bool(fingerprint) and fingerprint not in ("undefined", "null", "")
    hw_ok = bool(canvas_hash) and len(canvas_hash) > 8 and bool(webgl_hash) and len(webgl_hash) > 8
    tg_ok = bool(tg_platform) and bool(tg_version)

    # ── 2. Correlate against every candidate that shares ≥1 signal ────────
    if fp_ok or hw_ok or ip_ok or tg_ok:
        conditions = []
        params = []
        if fp_ok:
            conditions.append("fingerprint = ?")
            params.append(fingerprint)
        if hw_ok:
            conditions.append("(canvas_hash = ? AND webgl_hash = ?)")
            params.extend([canvas_hash, webgl_hash])
        if ip_ok:
            conditions.append("ip_address = ?")
            params.append(client_ip)
        if tg_ok:
            conditions.append("(tg_platform = ? AND tg_version = ?)")
            params.extend([tg_platform, tg_version])

        query = (
            "SELECT user_id, fingerprint, canvas_hash, webgl_hash, ip_address, "
            "tg_platform, tg_version FROM verifications "
            f"WHERE ({' OR '.join(conditions)}) AND user_id != ?"
        )
        params.append(new_user_id)

        async with aiosqlite.connect(DB_PATH) as db:
            db.row_factory = aiosqlite.Row
            cur = await db.execute(query, params)
            candidates = await cur.fetchall()

        best_score, best_uid, best_matched = 0, None, []
        for row in candidates:
            score, matched = _category_match_score(
                fingerprint, fp_ok, canvas_hash, webgl_hash, hw_ok,
                client_ip, ip_ok, tg_platform, tg_version, tg_ok, dict(row)
            )
            if score > best_score:
                best_score, best_uid, best_matched = score, row["user_id"], matched

        if best_score >= CORRELATION_BAN_THRESHOLD:
            logger.warning(
                f"[FRAUD] Correlated clone: new_uid={new_user_id} matches "
                f"uid={best_uid} on {best_matched} (score={best_score})"
            )
            return True, "correlated_clone"
        elif best_score >= 1:
            logger.warning(
                f"[FRAUD-WARN] Partial signal match (not banning): "
                f"new_uid={new_user_id} matches uid={best_uid} on {best_matched} (score={best_score})"
            )
            await DataEngine.log_fraud_attempt(
                new_user_id, "partial_signal_match", client_ip,
                f"matches_uid={best_uid} categories={best_matched} score={best_score}"
            )

    # ── 3. Referrer device check ────────────────────────────────────────
    #    Needs fingerprint match PLUS (IP or hardware) match against the
    #    referrer specifically — a single matching signal with the referrer
    #    alone (e.g. just sharing IP, just sharing fingerprint) is normal
    #    for family/friends and is only logged.
    if referrer_id and (fp_ok or ip_ok or hw_ok):
        async with aiosqlite.connect(DB_PATH) as db:
            db.row_factory = aiosqlite.Row
            cur = await db.execute(
                "SELECT ip_address, fingerprint, canvas_hash, webgl_hash "
                "FROM verifications WHERE user_id = ?",
                (referrer_id,)
            )
            inv_row = await cur.fetchone()
            if inv_row:
                inv_ip = inv_row["ip_address"] or ""
                inv_fp = inv_row["fingerprint"] or ""
                is_real_ip = inv_ip not in ("", "127.0.0.1", "::1", "unknown", "BYPASS_ADMIN")

                fp_matches_ref = fp_ok and inv_fp and inv_fp == fingerprint
                ip_matches_ref = ip_ok and is_real_ip and inv_ip == client_ip
                hw_matches_ref = (
                    hw_ok and inv_row["canvas_hash"] == canvas_hash
                    and inv_row["webgl_hash"] == webgl_hash
                )

                ref_score = sum([fp_matches_ref, ip_matches_ref, hw_matches_ref])

                if fp_matches_ref and (ip_matches_ref or hw_matches_ref):
                    return True, "same_device_as_referrer"
                elif ref_score >= 1:
                    logger.warning(
                        f"[FRAUD-WARN] Single-signal match with referrer (not banning): "
                        f"ref={referrer_id} new={new_user_id} "
                        f"fp={fp_matches_ref} ip={ip_matches_ref} hw={hw_matches_ref}"
                    )
                    await DataEngine.log_fraud_attempt(
                        new_user_id, "referrer_signal_match", client_ip,
                        f"referrer={referrer_id} fp={fp_matches_ref} ip={ip_matches_ref} hw={hw_matches_ref}"
                    )

    # ── 4. IP farm detection — aware of shared-NAT / CGNAT networks ───────
    #    A high user count on one IP is, by itself, completely normal in
    #    Ethiopia where mobile carriers use CGNAT (many real customers
    #    share one public IP). We only treat it as a farm when the SAME IP
    #    also shows low fingerprint diversity — i.e. the same handful of
    #    device fingerprints being reused across many accounts, which is
    #    what a scripted farm looks like. Distinct real phones on a shared
    #    network are never banned for this alone.
    if ip_ok:
        ip_count = await DataEngine.count_ip_users(client_ip)
        if ip_count >= MAX_USERS_PER_IP:
            distinct_fp = await DataEngine.count_ip_distinct_fingerprints(client_ip)
            fp_ratio = (distinct_fp / ip_count) if ip_count else 1.0
            logger.warning(
                f"[FRAUD-WARN] High IP usage: ip={client_ip} count={ip_count} "
                f"distinct_fp={distinct_fp} ratio={fp_ratio:.2f} new_uid={new_user_id}"
            )
            await DataEngine.log_fraud_attempt(
                new_user_id, "high_ip_usage", client_ip,
                f"users={ip_count} distinct_fp={distinct_fp} ratio={fp_ratio:.2f}"
            )
            if ip_count >= MAX_USERS_PER_IP_BAN and fp_ratio < IP_FARM_MIN_FP_RATIO:
                return True, "ip_farm"

    return False, ""


def extract_real_ip(request: Request) -> str:
    cf_ip = request.headers.get("CF-Connecting-IP", "").strip()
    if cf_ip:
        return cf_ip
    real_ip = request.headers.get("X-Real-IP", "").strip()
    if real_ip:
        return real_ip
    forwarded = request.headers.get("X-Forwarded-For", "")
    if forwarded:
        parts = [p.strip() for p in forwarded.split(",") if p.strip()]
        if parts:
            return parts[0]
    if request.client:
        return request.client.host
    return "unknown"


# ─────────────────────────────────────────────────────────────────────────────
# WORKFLOW STATES
# ─────────────────────────────────────────────────────────────────────────────
class UserWithdrawalWorkflow(StatesGroup):
    select_payout_gateway = State()
    input_cash_volume     = State()
    provide_mobile_digits = State()
    provide_account_title = State()
    payout_final_approval = State()

class AdminConsoleWorkflow(StatesGroup):
    modify_referral_bounty   = State()
    modify_minimum_cashout   = State()
    append_mandatory_id      = State()
    append_mandatory_title   = State()
    append_mandatory_url     = State()
    append_noadmin_link      = State()
    append_noadmin_title     = State()
    direct_balance_target_id = State()
    direct_balance_volume    = State()
    broadcast_intel_payload  = State()
    broadcast_confirmation   = State()
    lookup_individual_id     = State()
    ban_individual_id        = State()
    banish_individual_id     = State()
    pardon_individual_full   = State()
    pardon_individual_std    = State()
    write_reject_reason      = State()

bot         = Bot(token=BOT_TOKEN, parse_mode=ParseMode.HTML)
dp          = Dispatcher(storage=MemoryStorage())
core_router = Router()

# ── Shared "invite card" builder — used both by /api/invite/share_card
#    (sends it straight into the user's own chat with the bot) and by the
#    inline_query handler below (lets the user pick a friend/group from
#    Telegram's native chat list and have it delivered there directly).
_bot_photo_file_id: str | None = None  # cached after first lookup


async def _get_bot_photo_file_id() -> str | None:
    global _bot_photo_file_id
    if _bot_photo_file_id:
        return _bot_photo_file_id
    try:
        photos = await bot.get_user_profile_photos(BOT_ID or (await bot.get_me()).id, limit=1)
        if photos.total_count > 0:
            _bot_photo_file_id = photos.photos[0][-1].file_id  # largest size
    except Exception:
        pass
    return _bot_photo_file_id


async def _build_invite_card(uid: int):
    uname = BOT_USERNAME or (await bot.get_me()).username
    referral_link = f"https://t.me/{uname}?start={uid}"
    caption = (
        "🎉 <b>I'm earning real money with this bot — and you can too!</b>\n\n"
        "✅ Complete simple tasks\n"
        "✅ Watch short ads\n"
        "✅ Invite friends for bonus rewards\n"
        "✅ Withdraw straight to Telebirr\n\n"
        "Tap the button below to join — it only takes a minute 👇"
    )
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🎁 Join & Start Earning", url=referral_link)],
    ])
    photo_id = await _get_bot_photo_file_id()
    return caption, kb, photo_id


@core_router.inline_query()
async def handle_invite_inline_query(inline_query: InlineQuery):
    """
    Powers "Share with Friends": the Mini App calls tg.switchInlineQuery(),
    the user picks a friend/group from Telegram's native chat picker, and
    Telegram calls this handler to ask what to actually send there.

    This matters because a manually-forwarded copy of a bot message loses
    its inline keyboard — Telegram only keeps buttons on messages sent
    live by the bot. Answering an inline query IS the bot sending the
    message directly into that chat (just triggered through the picker
    instead of a /start), so the photo + button both survive. This is the
    same mechanism most invite/referral bots rely on for exactly that reason.
    """
    caption, kb, photo_id = await _build_invite_card(inline_query.from_user.id)
    if photo_id:
        result = InlineQueryResultCachedPhoto(
            id=str(inline_query.from_user.id), photo_file_id=photo_id,
            caption=caption, reply_markup=kb,
        )
    else:
        result = InlineQueryResultArticle(
            id=str(inline_query.from_user.id), title="📤 Share your invite",
            description="Tap to send your invite card with a Join button",
            input_message_content=InputTextMessageContent(message_text=caption),
            reply_markup=kb,
        )
    try:
        await bot.answer_inline_query(inline_query.id, results=[result], cache_time=0, is_personal=True)
    except Exception as e:
        logger.warning(f"answer_inline_query failed: {e}")

# ─────────────────────────────────────────────────────────────────────────────
# DEBUG: catch-all callback logger
#
# Registered as a plain middleware-style outer handler so EVERY incoming
# callback_query is logged before any filter-specific handler runs. If a
# button tap produces zero output in Railway logs, this proves the update
# never reached the bot process at all (Telegram delivery / polling issue,
# not a code-logic bug) — vs. seeing this log line but no further handler
# log, which would point at a filter mismatch instead.
# ─────────────────────────────────────────────────────────────────────────────
@core_router.callback_query.middleware()
async def debug_log_all_callbacks(handler, event: CallbackQuery, data):
    logger.info(f"[CALLBACK-IN] uid={event.from_user.id} data={event.data!r}")
    try:
        return await handler(event, data)
    except Exception as e:
        logger.exception(f"[CALLBACK-ERROR] uid={event.from_user.id} data={event.data!r}: {e}")
        try:
            await event.answer("⚠️ Internal error, please try again.", show_alert=True)
        except Exception:
            pass

# ─────────────────────────────────────────────────────────────────────────────
# FORCE JOIN LOGIC
# ─────────────────────────────────────────────────────────────────────────────
async def inspect_compulsory_memberships(user_id: int) -> list:
    channels = await DataEngine.get_force_channels()
    unjoined = []
    for ch in channels:
        if ch["bot_added"] == 1:
            continue
        try:
            m = await bot.get_chat_member(chat_id=ch["channel_id"], user_id=user_id)
            if m.status in (ChatMemberStatus.LEFT, ChatMemberStatus.KICKED, ChatMemberStatus.RESTRICTED):
                unjoined.append(dict(ch))
        except Exception as e:
            # IMPORTANT: if the bot itself isn't an admin in this channel
            # (or the channel ID is wrong), get_chat_member() always throws
            # — and treating that as "user hasn't joined" locks EVERY
            # regular user out of the bot forever, on every button, while
            # admins (who bypass this gate via BYPASS_ADMIN verification)
            # never notice. So a misconfigured channel must NOT block
            # users; it's logged instead so it's visible to the admin.
            logger.warning(
                f"[GATE] Could not check membership for channel={ch['channel_id']} "
                f"user={user_id}: {e} — skipping this channel's check "
                f"(bot may not be admin there)."
            )
    return unjoined

async def enforce_membership_gate(event, user_id: int) -> bool:
    unjoined = await inspect_compulsory_memberships(user_id)
    is_callback  = isinstance(event, CallbackQuery)
    current_data = event.data if is_callback else ""

    if not is_callback or current_data in ("ui_return_home", ""):
        already_seen_fake = await DataEngine.has_seen_fake_join(user_id)
        if not already_seen_fake:
            all_channels = await DataEngine.get_force_channels()
            for ch in all_channels:
                if ch["bot_added"] == 1:
                    if not any(x['channel_id'] == ch['channel_id'] for x in unjoined):
                        unjoined.append(dict(ch))

    if not unjoined:
        return True

    if any(x.get('bot_added') == 1 for x in unjoined):
        await DataEngine.mark_fake_join_seen(user_id)

    buttons = []
    for ch in unjoined:
        buttons.append([InlineKeyboardButton(text=f"➕ Join: {ch['channel_name']}", url=ch["invite_link"])])
    buttons.append([InlineKeyboardButton(text="✅ Joined / ተቀላቅያለሁ", callback_data="ui_revalidate_channels")])

    txt = (
        "👋 <b>Welcome!</b>\n\n"
        "እባክዎ ከታች ያሉትን ሁሉንም ቻናሎች ይቀላቀሉ፣ ከዚያም <b>'Joined'</b> የሚለውን በተን ይጫኑ።\n\n"
        "Please join all channels and continue."
    )

    if isinstance(event, Message):
        await event.answer(txt, reply_markup=InlineKeyboardMarkup(inline_keyboard=buttons))
    elif isinstance(event, CallbackQuery):
        await event.message.answer(txt, reply_markup=InlineKeyboardMarkup(inline_keyboard=buttons))
        await event.answer()
    return False

@core_router.callback_query(F.data == "ui_revalidate_channels")
async def process_channel_revalidation(callback: CallbackQuery, state: FSMContext):
    uid      = callback.from_user.id
    channels = await DataEngine.get_force_channels()
    real_unjoined = []
    for ch in channels:
        if ch["bot_added"] == 0:
            try:
                m = await bot.get_chat_member(chat_id=ch["channel_id"], user_id=uid)
                if m.status in (ChatMemberStatus.LEFT, ChatMemberStatus.KICKED, ChatMemberStatus.RESTRICTED):
                    real_unjoined.append(ch)
            except Exception as e:
                logger.warning(
                    f"[GATE] Could not check membership for channel={ch['channel_id']} "
                    f"user={uid}: {e} — skipping this channel's check "
                    f"(bot may not be admin there)."
                )

    if real_unjoined:
        return await callback.answer("❌ Please join all channels and continue.", show_alert=True)

    try:
        await callback.message.delete()
    except Exception:
        pass

    s   = await state.get_data()
    ref = s.get("stashed_referrer_id", 0)
    await state.clear()

    if await DataEngine.is_verified(uid):
        await callback.message.answer("✅ Identity clear!", reply_markup=generate_dashboard_matrix(uid))
    else:
        acc = await DataEngine.get_user(uid)
        if acc and acc["last_verify_msg_id"]:
            try:
                await bot.delete_message(chat_id=uid, message_id=acc["last_verify_msg_id"])
            except Exception:
                pass

        sent = await callback.message.answer(
            f"{BOT_RULES_CAPTION}\n\n🔐 <b>Attestation Step:</b> Launch Mini App verification:",
            reply_markup=generate_verification_widget(uid, ref, 0)
        )
        await sent.edit_reply_markup(reply_markup=generate_verification_widget(uid, ref, sent.message_id))
        await DataEngine.set_last_verify_msg(uid, sent.message_id)

# ─────────────────────────────────────────────────────────────────────────────
# CORE BOT HANDLERS
# ─────────────────────────────────────────────────────────────────────────────
@core_router.message(CommandStart())
async def process_start_command(message: Message, state: FSMContext):
    await state.clear()
    uid  = message.from_user.id
    args = message.text.split()
    arg  = args[1] if len(args) > 1 else ""
    ref  = int(arg) if arg.isdigit() and int(arg) != uid else 0

    acc = await DataEngine.get_user(uid)
    if acc and acc["is_banned"]:
        return await message.answer("🚫 <b>Banned:</b> Your profile has been blacklisted.")

    if not await enforce_membership_gate(message, uid):
        if ref:
            await state.update_data(stashed_referrer_id=ref)
        return

    if await DataEngine.is_verified(uid):
        return await message.answer("✅ <b>Welcome back!</b> Access granted.", reply_markup=generate_dashboard_matrix(uid))

    # ── Clean up any stale, unfinished verification widget ────────────────
    # If the user restarts the bot (or taps an old shared /start link)
    # before completing verification, the previous "Open Mini App" message
    # is deleted first and a brand-new one is sent in its place. This stops
    # someone from passing around / re-using an old verification link and
    # keeps the chat from filling up with duplicate widgets.
    if acc and acc["last_verify_msg_id"]:
        try:
            await bot.delete_message(chat_id=uid, message_id=acc["last_verify_msg_id"])
        except Exception:
            pass

    sent = await message.answer(
        f"{BOT_RULES_CAPTION}\n\n🔐 <b>Next Step:</b> Verify identity via Mini App:",
        reply_markup=generate_verification_widget(uid, ref, 0)
    )
    await sent.edit_reply_markup(reply_markup=generate_verification_widget(uid, ref, sent.message_id))
    await DataEngine.set_last_verify_msg(uid, sent.message_id)

@core_router.callback_query(F.data == "ui_return_home")
async def process_navigation_home(callback: CallbackQuery, state: FSMContext):
    await state.clear()
    uid = callback.from_user.id
    if not await DataEngine.is_verified(uid):
        if not await enforce_membership_gate(callback, uid):
            return
    await callback.message.edit_text(
        "🏠 <b>Main Dashboard Menu / ዋና ማውጫ</b>",
        reply_markup=generate_dashboard_matrix(uid)
    )

@core_router.callback_query(F.data == "ui_fetch_balance")
async def process_balance_query(callback: CallbackQuery):
    uid = callback.from_user.id
    # Already-verified users joined the required channels at verification
    # time. Re-checking membership (one Telegram API call per channel) on
    # every single button tap is what makes the bot look "stuck" once many
    # users are tapping buttons concurrently — this skips that re-check.
    if not await DataEngine.is_verified(uid):
        if not await enforce_membership_gate(callback, uid):
            return
    acc = await DataEngine.get_user(uid)
    if acc is None:
        # Self-heal: this account has a verifications row (so is_verified
        # was True) but somehow never got a users row — most commonly
        # caused by the admin "Full Unban" path before this fix. Create
        # the missing row instead of crashing.
        await DataEngine.create_user(
            uid, callback.from_user.username or "", callback.from_user.full_name or ""
        )
        acc = await DataEngine.get_user(uid)
    min_w = await DataEngine.get_setting("min_withdrawal", "50")
    await callback.message.edit_text(
        f"💰 <b>Your Available Balance:</b>\n\n"
        f"• Assets: <code>{float(acc['balance']):.2f} Birr</code>\n"
        f"• Minimum Withdrawal: <code>{min_w} Birr</code>",
        reply_markup=generate_fallback_navigation()
    )

@core_router.callback_query(F.data == "ui_fetch_referrals")
async def process_referral_query(callback: CallbackQuery):
    uid = callback.from_user.id
    if not await DataEngine.is_verified(uid):
        if not await enforce_membership_gate(callback, uid):
            return
    direct, _    = await DataEngine.get_paid_referral_metrics(uid)
    rate         = float(await DataEngine.get_setting("reward_per_referral", "10"))
    me           = await bot.get_me()
    link         = f"https://t.me/{me.username}?start={uid}"
    await callback.message.edit_text(
        f"👥 <b>Your Referral Network:</b>\n\n"
        f"• Total Referrals: <b>{direct} users</b>\n"
        f"• Earnings per Referral: <b>{rate:.2f} Birr</b>\n"
        f"• Total Earned: <b>{direct * rate:.2f} Birr</b>\n\n"
        f"🔗 Your link:\n<code>{link}</code>",
        reply_markup=generate_fallback_navigation()
    )

@core_router.callback_query(F.data == "ui_fetch_link")
async def process_link_generation(callback: CallbackQuery):
    uid = callback.from_user.id
    if not await DataEngine.is_verified(uid):
        if not await enforce_membership_gate(callback, uid):
            return
    me = await bot.get_me()
    await callback.message.edit_text(
        f"🔗 <b>Your Invite Link:</b>\n\n"
        f"<code>https://t.me/{me.username}?start={callback.from_user.id}</code>",
        reply_markup=generate_fallback_navigation()
    )

@core_router.message(F.photo)
async def process_get_file_id(message: Message):
    if not evaluate_admin_access(message.from_user.id):
        return
    file_id = message.photo[-1].file_id
    await message.answer(
        f"📸 <b>File ID Captured:</b>\n\n<code>{file_id}</code>\n\n"
        f"⚠️ Copy this value and replace <code>TELEBIRR_PROOF_IMAGE</code> in the code."
    )

# ─────────────────────────────────────────────────────────────────────────────
# HELPERS
# ─────────────────────────────────────────────────────────────────────────────
def evaluate_admin_access(user_id: int) -> bool:
    return user_id in ADMIN_IDS

def parse_telegram_webapp_handshake(init_data: str) -> dict | None:
    try:
        parsed = dict(urllib.parse.parse_qsl(init_data, strict_parsing=True))
        vh     = parsed.pop("hash", "")
        check_str = "\n".join(f"{k}={v}" for k, v in sorted(parsed.items()))
        key    = hmac.new(b"WebAppData", BOT_TOKEN.encode(), hashlib.sha256).digest()
        sig    = hmac.new(key, check_str.encode(), hashlib.sha256).hexdigest()
        if not hmac.compare_digest(sig, vh):
            return None

        # Reject stale payloads. initData carries a unix `auth_date` set by
        # Telegram at the moment the Mini App was opened — if it's older
        # than our allowed window, treat it as invalid rather than trusting
        # a copy-pasted link opened outside Telegram / hours later.
        try:
            auth_date = int(parsed.get("auth_date", "0"))
        except ValueError:
            return None
        age = time.time() - auth_date
        if age < 0 or age > MAX_INIT_DATA_AGE_SECONDS:
            return None

        return json.loads(parsed.get("user", "{}"))
    except Exception:
        return None

async def execute_network_vpn_lookup(client_ip: str) -> bool:
    """
    VPN CHECK:
    'operator' field (ISP name) is intentionally ignored — every legitimate
    Ethiopian user is on an ISP like Ethio Telecom / Safaricom, so keying off
    that field would ban normal users. Only an explicit VPN/TOR `type` from
    the lookup service counts as a VPN hit.
    """
    if not client_ip or client_ip in ("127.0.0.1", "::1", "unknown"):
        return False
    try:
        param = f"&key={PROXYCHECK_API_KEY}" if PROXYCHECK_API_KEY else ""
        url = f"https://proxycheck.io/v2/{client_ip}?vpn=1&asn=1{param}"
        async with httpx.AsyncClient(timeout=5) as c:
            r = await c.get(url)
            payload = r.json()
            d = payload.get(client_ip, {})
            ptype = (d.get("type") or "").upper()
            logger.info(f"proxycheck result ip={client_ip} type={ptype}")
            return ptype in ("VPN", "TOR")
    except Exception:
        logger.warning(f"proxycheck lookup failed for ip={client_ip}")
        return False

def generate_verification_widget(user_id: int, ref: int, msg_id: int = 0):
    # index.html (verify screen) is served from the FRONTEND (Vercel), NOT
    # from this backend, so this must point at FRONTEND_URL, not WEBAPP_URL.
    url = f"{FRONTEND_URL}/index.html?uid={user_id}&ref={ref}&msg_id={msg_id}"
    return InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="🔐 Open Mini App & Verify", web_app=WebAppInfo(url=url))
    ]])

def generate_app_webapp_button(user_id: int, admin: bool = False) -> InlineKeyboardMarkup:
    url = f"{FRONTEND_URL}/app.html?uid={user_id}" + ("&admin=1" if admin else "")
    return InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="📱 Open Mini App / አፑን ክፈት", web_app=WebAppInfo(url=url))
    ]])

def generate_dashboard_matrix(user_id: int) -> InlineKeyboardMarkup:
    rows = [
        [InlineKeyboardButton(
            text="📱 Open Mini App / አፑን ክፈት",
            web_app=WebAppInfo(url=f"{FRONTEND_URL}/app.html?uid={user_id}")
        )],
        [
            InlineKeyboardButton(text="💰 Balance / ሒሳብ",    callback_data="ui_fetch_balance"),
            InlineKeyboardButton(text="👥 Referrals / ጋባዦች", callback_data="ui_fetch_referrals"),
        ],
        [
            InlineKeyboardButton(text="🔗 My Link / ሊንኬ",       callback_data="ui_fetch_link"),
            InlineKeyboardButton(text="💸 Withdraw / ብር ማውጫ", callback_data="ui_initiate_withdrawal"),
        ],
    ]
    if evaluate_admin_access(user_id):
        rows.append([InlineKeyboardButton(text="⚙️ Admin Control Center", callback_data="ui_admin_core")])
    return InlineKeyboardMarkup(inline_keyboard=rows)

def generate_admin_dashboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(
            text="🧩 Tasks & Full Admin (Mini App)",
            web_app=WebAppInfo(url=f"{FRONTEND_URL}/app.html?admin=1")
        )],
        [
            InlineKeyboardButton(text="💎 Set Referral Reward",  callback_data="adm_cmd_reward"),
            InlineKeyboardButton(text="💵 Set Min Withdrawal",   callback_data="adm_cmd_min_wd"),
        ],
        [
            InlineKeyboardButton(text="✍️ Edit User Balance",    callback_data="adm_cmd_edit_bal"),
            InlineKeyboardButton(text="📊 Bot Statistics",       callback_data="adm_cmd_stats"),
        ],
        [
            InlineKeyboardButton(text="🔴 Force Join (Real Admin)", callback_data="adm_cmd_add_mand"),
            InlineKeyboardButton(text="🟡 Fake Join (No Admin)",    callback_data="adm_cmd_add_noadmin"),
        ],
        [InlineKeyboardButton(text="🗑 Remove Force Channel",   callback_data="adm_cmd_rm_node")],
        [InlineKeyboardButton(text="📋 List Force Channels",    callback_data="adm_cmd_list_channels")],
        [
            InlineKeyboardButton(text="📥 Pending Withdrawals", callback_data="adm_cmd_pending_tickets"),
            InlineKeyboardButton(text="📢 Broadcast Message",   callback_data="adm_cmd_broadcast"),
        ],
        [InlineKeyboardButton(text="🔍 Search User",            callback_data="adm_cmd_search")],
        [InlineKeyboardButton(text="⚠️ Fraud Log",              callback_data="adm_cmd_fraud_log")],
        [
            InlineKeyboardButton(text="🚫 Ban User",            callback_data="adm_cmd_ban"),
            InlineKeyboardButton(text="✅ Unban Dashboard",     callback_data="adm_cmd_unban_menu"),
        ],
        [InlineKeyboardButton(text="💾 Backup DB Now",         callback_data="adm_cmd_backup_now")],
        [InlineKeyboardButton(text="🛑 STOP BOT ENGINE",        callback_data="adm_stop_bot_confirm1")],
        [InlineKeyboardButton(text="🔙 Back to Main Menu",      callback_data="ui_return_home")],
    ])

def generate_fallback_navigation(target="ui_return_home") -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="🔙 Back / ተመለስ", callback_data=target)
    ]])

# ─────────────────────────────────────────────────────────────────────────────
# WITHDRAWAL
# ─────────────────────────────────────────────────────────────────────────────
@core_router.callback_query(F.data == "ui_initiate_withdrawal")
async def process_withdrawal_start(callback: CallbackQuery, state: FSMContext):
    uid = callback.from_user.id
    if not await DataEngine.is_verified(uid):
        if not await enforce_membership_gate(callback, uid):
            return
    user = await DataEngine.get_user(uid)
    if user is None:
        # Self-heal — see explanation in process_balance_query above.
        await DataEngine.create_user(
            uid, callback.from_user.username or "", callback.from_user.full_name or ""
        )
        user = await DataEngine.get_user(uid)
    min_w = float(await DataEngine.get_setting("min_withdrawal", "50"))
    current_bal = round(float(user["balance"]), 2)
    if current_bal < min_w:
        return await callback.answer(
            f"❌ Minimum payout baseline is {min_w:.2f} Birr. Your balance is {current_bal:.2f} Birr.",
            show_alert=True
        )
    await state.set_state(UserWithdrawalWorkflow.select_payout_gateway)
    await state.update_data(cached_balance=current_bal, cached_minimum=min_w)
    await callback.message.edit_text(
        "💸 <b>Select Payout Endpoint:</b>",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="📲 Telebirr / ቴሌብር", callback_data="gateway_telebirr")],
            [InlineKeyboardButton(text="❌ Cancel / ሰርዝ",     callback_data="ui_return_home")],
        ])
    )

@core_router.callback_query(F.data == "gateway_telebirr", UserWithdrawalWorkflow.select_payout_gateway)
async def process_telebirr_selection(callback: CallbackQuery, state: FSMContext):
    await state.set_state(UserWithdrawalWorkflow.input_cash_volume)
    await callback.message.edit_text(
        "<b>Specify the amount you wish to withdraw (Birr):</b>",
        reply_markup=generate_fallback_navigation()
    )

@core_router.message(UserWithdrawalWorkflow.input_cash_volume)
async def process_cashout_volume(message: Message, state: FSMContext):
    s = await state.get_data()
    try:
        val = round(float(message.text.strip()), 2)
        if val < s["cached_minimum"] or val > s["cached_balance"]:
            return await message.answer(
                f"❌ Invalid amount. Minimum withdrawal is {s['cached_minimum']:.2f} ETB.\n"
                f"⚠️ <b>Your balance is:</b> {s['cached_balance']:.2f} ETB."
            )
    except Exception:
        return await message.answer(
            f"❌ Please enter a valid number.\n"
            f"⚠️ <b>Your balance is:</b> {s['cached_balance']:.2f} ETB."
        )
    await state.update_data(validated_volume=val)
    await state.set_state(UserWithdrawalWorkflow.provide_mobile_digits)
    await message.answer("📱 <b>Provide Destination Account Mobile Number:</b>")

@core_router.message(UserWithdrawalWorkflow.provide_mobile_digits)
async def process_mobile_digits(message: Message, state: FSMContext):
    phone = message.text.strip()
    if len(phone) < 9:
        return await message.answer("❌ Provide a valid mobile number.")
    await state.update_data(validated_phone=phone)
    await state.set_state(UserWithdrawalWorkflow.provide_account_title)
    await message.answer("📝 <b>Enter Full Name of Account Holder:</b>")

@core_router.message(UserWithdrawalWorkflow.provide_account_title)
async def process_account_title(message: Message, state: FSMContext):
    title = message.text.strip()
    if len(title) < 3:
        return await message.answer("❌ Name is too short.")
    await state.update_data(validated_title=title)
    s = await state.get_data()
    safe_title = sanitize_html(title)
    await message.answer(
        f"⚠️ <b>Review Settlement Details</b>\n\n"
        f"• Platform: <code>Telebirr</code>\n"
        f"• Amount: <code>{s['validated_volume']:.2f} ETB</code>\n"
        f"• Holder: <code>{safe_title}</code>\n"
        f"• Number: <code>{sanitize_html(s['validated_phone'])}</code>\n\n"
        f"Authorization requested.",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=[[
            InlineKeyboardButton(text="✅ Transact Payout",  callback_data="action_payout_dispatch"),
            InlineKeyboardButton(text="❌ Abort / ሰርዝ",     callback_data="ui_return_home"),
        ]])
    )
    await state.set_state(UserWithdrawalWorkflow.payout_final_approval)

async def dispatch_withdrawal_core(uid: int, amount: float, full_name: str, phone: str) -> dict:
    """
    Shared withdrawal-submission logic used by BOTH the bot-chat flow and
    the Mini App REST endpoint (/api/withdraw), so there's exactly one
    place that creates the ledger row and notifies admins.
    """
    tid, ok = await DataEngine.create_withdrawal_atomic(uid, amount, full_name, phone)
    if not ok:
        return {"status": "error", "reason": "insufficient_funds"}

    user = await DataEngine.get_user(uid)
    me   = await bot.get_me()
    proof_channel_keyboard = InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="🚀 Invite Now", url=f"https://t.me/{me.username}?start={uid}")
    ]])

    post_id = 0
    if PAYMENT_LOG_CHANNEL:
        try:
            txt = (
                f"━━━━━━━━━━━━━━━━━━━━━━\n\n"
                f"📥 <b>NEW WITHDRAWAL REQUEST</b>\n\n"
                f"━━━━━━━━━━━━━━━━━━━━━━\n\n"
                f"👤 <b>Account Holder Name:</b> {sanitize_html(full_name)}\n\n"
                f"🆔 <b>User ID:</b> <code>{uid}</code>\n\n"
                f"💰 <b>Requested Amount:</b> ETB {amount:.2f}\n\n"
                f"📱 <b>Method:</b> Telebirr Portal\n\n"
                f"📊 <b>Status:</b> Pending Verification ⏳\n\n"
                f"⏰ <b>Timestamp:</b> {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n"
                f"━━━━━━━━━━━━━━━━━━━━━━"
            )
            receipt = await bot.send_message(PAYMENT_LOG_CHANNEL, txt, reply_markup=proof_channel_keyboard)
            post_id = receipt.message_id
            await DataEngine.update_withdrawal_status(tid, "pending", post_id)
        except Exception as e:
            logger.error(f"Log Channel Post Error: {e}")

    direct_ref, tier2_ref = await DataEngine.get_referral_metrics(uid)
    alias_str  = f"@{sanitize_html(user['username'])}" if user["username"] else "None"
    admin_txt = (
        f"📥 <b>Incoming Ticket #{tid}</b>\n"
        f"━━━━━━━━━━━━━━━━━━━━━━\n"
        f"👤 <b>Holder Name:</b> {sanitize_html(full_name)}\n"
        f"🆔 <b>User ID:</b> <code>{uid}</code>\n"
        f"👤 <b>Username:</b> {alias_str}\n"
        f"📲 <b>Phone:</b> <code>{sanitize_html(phone)}</code>\n"
        f"💰 <b>Amount:</b> <b>{amount:.2f} Birr</b>\n"
        f"━━━━━━━━━━━━━━━━━━━━━━\n"
        f"📊 <b>NETWORK INTEGRITY REPORT:</b>\n"
        f"• Direct Referrals: <b>{direct_ref} ሰዎችን</b>\n"
        f"• Tier-2 Network Activity: <b>{tier2_ref} ሰዎችን</b>"
    )
    markup = InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text="✅ Approve (Both)",  callback_data=f"adm_payout_ap_{tid}"),
        ],
        [
            InlineKeyboardButton(text="📢 Approve (Channel Only)", callback_data=f"adm_payout_apco_{tid}"),
        ],
        [
            InlineKeyboardButton(text="❌ Deny (ውድቅ አድርግ)", callback_data=f"adm_payout_rjmenu_{tid}"),
        ],
        [InlineKeyboardButton(text="👥 View Referrals", callback_data=f"adm_view_invites_{uid}")]
    ])
    for aid in ADMIN_IDS:
        try:
            await bot.send_message(aid, admin_txt, reply_markup=markup)
        except Exception:
            pass

    return {"status": "submitted", "ticket_id": tid}


@core_router.callback_query(F.data == "action_payout_dispatch", UserWithdrawalWorkflow.payout_final_approval)
async def process_payout_dispatch(callback: CallbackQuery, state: FSMContext):
    s   = await state.get_data()
    uid = callback.from_user.id

    result = await dispatch_withdrawal_core(
        uid, s["validated_volume"], s["validated_title"], s["validated_phone"]
    )
    if result["status"] == "error":
        return await callback.answer("❌ Insufficient funds.", show_alert=True)

    await state.clear()
    await callback.message.edit_text(
        "📨 <b>Withdrawal Submitted!</b> Processing within 2-24 hours.",
        reply_markup=generate_dashboard_matrix(uid)
    )

# ─────────────────────────────────────────────────────────────────────────────
# ADMIN — VIEW REFERRALS
# ─────────────────────────────────────────────────────────────────────────────
@core_router.callback_query(F.data.startswith("adm_view_invites_"))
async def process_admin_view_invites(callback: CallbackQuery):
    if not evaluate_admin_access(callback.from_user.id):
        return
    target_uid    = int(callback.data.split("_")[3])
    invited_nodes = await DataEngine.get_all_invited_users(target_uid)
    if not invited_nodes:
        return await callback.answer("📭 This user has not invited anyone yet.", show_alert=True)
    lines = []
    for idx, node in enumerate(invited_nodes, 1):
        uname = f"@{node['username']}" if node['username'] else "No Username"
        lines.append(
            f"{idx}. {sanitize_html(node['full_name'])} ({sanitize_html(uname)}) — ID: <code>{node['user_id']}</code>\n"
            f"📅 Joined: {node['joined_at']}"
        )
    chunk_txt = f"👥 <b>Invited Users for ID {target_uid}:</b>\n\n" + "\n\n".join(lines)
    if len(chunk_txt) > 4000:
        chunk_txt = chunk_txt[:4000] + "\n\n⚠️...List truncated."
    await bot.send_message(
        chat_id=callback.from_user.id,
        text=chunk_txt,
        reply_markup=generate_fallback_navigation("ui_admin_core")
    )
    await callback.answer()

# ─────────────────────────────────────────────────────────────────────────────
# ADMIN — FRAUD LOG
# ─────────────────────────────────────────────────────────────────────────────
@core_router.callback_query(F.data == "adm_cmd_fraud_log")
async def process_fraud_log(callback: CallbackQuery):
    if not evaluate_admin_access(callback.from_user.id):
        return
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute(
            "SELECT * FROM fraud_log ORDER BY logged_at DESC LIMIT 20"
        )
        rows = await cur.fetchall()
    if not rows:
        return await callback.message.edit_text(
            "📭 No fraud attempts logged.", reply_markup=generate_fallback_navigation("ui_admin_core")
        )
    lines = []
    for r in rows:
        lines.append(
            f"⚠️ <code>{r['reason']}</code>\n"
            f"   uid=<code>{r['user_id']}</code> ip=<code>{r['ip_address']}</code>\n"
            f"   {r['details']}\n"
            f"   🕐 {r['logged_at']}"
        )
    await callback.message.edit_text(
        f"⚠️ <b>Fraud Log (last 20):</b>\n\n" + "\n\n".join(lines),
        reply_markup=generate_fallback_navigation("ui_admin_core")
    )

# ─────────────────────────────────────────────────────────────────────────────
# ADMIN — APPROVE WITHDRAWAL
# ─────────────────────────────────────────────────────────────────────────────
async def approve_withdrawal_core(tid: int, notify_mode: str = "both") -> dict:
    """
    Shared approval logic used by BOTH the bot-chat inline button and the
    Mini App REST endpoint (/api/admin/withdrawals/approve), so there's
    exactly one place that posts the Telebirr proof photo and notifies
    the user.

    notify_mode:
      "both"          — post proof to the channel AND DM the user (default)
      "channel_only"  — post proof to the channel only, no DM to the user
    """
    ticket = await DataEngine.get_withdrawal(tid)
    if not ticket or ticket["status"] != "pending":
        return {"ok": False, "reason": "already_processed"}
    await DataEngine.update_withdrawal_status(tid, "approved", ticket["channel_post_id"])
    me = await bot.get_me()
    proof_channel_keyboard = InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="🚀 Invite Now", url=f"https://t.me/{me.username}?start={ticket['user_id']}")
    ]])
    if PAYMENT_LOG_CHANNEL and ticket["channel_post_id"]:
        txt = (
            f"━━━━━━━━━━━━━━━━━━━━━━\n\n"
            f"✅ <b>WITHDRAWAL COMPLETED</b>\n\n"
            f"━━━━━━━━━━━━━━━━━━━━━━\n\n"
            f"👤 <b>Recipient:</b> {sanitize_html(ticket['full_name'])}\n\n"
            f"💰 <b>Amount:</b> ETB {ticket['amount']:.2f}\n\n"
            f"🚀 <b>Operational Registry:</b> Success ✅\n\n"
            f"━━━━━━━━━━━━━━━━━━━━━━"
        )
        try:
            await bot.send_photo(
                chat_id=PAYMENT_LOG_CHANNEL,
                photo=TELEBIRR_PROOF_IMAGE,
                caption=txt,
                reply_to_message_id=ticket["channel_post_id"],
                reply_markup=proof_channel_keyboard
            )
        except Exception as e:
            logger.error(f"Proof Photo Error: {e}")
            try:
                await bot.send_message(
                    chat_id=PAYMENT_LOG_CHANNEL,
                    text=txt,
                    reply_to_message_id=ticket["channel_post_id"],
                    reply_markup=proof_channel_keyboard
                )
            except Exception as e2:
                logger.error(f"Proof Text Fallback Error: {e2}")
    if notify_mode != "channel_only":
        try:
            await bot.send_message(
                ticket["user_id"],
                f"🎉 Your cashout of {ticket['amount']:.2f} Birr has been approved and sent via Telebirr!"
            )
        except Exception:
            pass
    return {"ok": True}

@core_router.callback_query(F.data.startswith("adm_payout_ap_"))
async def process_admin_approval(callback: CallbackQuery):
    if not evaluate_admin_access(callback.from_user.id):
        return
    tid    = int(callback.data.split("_")[3])
    result = await approve_withdrawal_core(tid, notify_mode="both")
    if not result["ok"]:
        return await callback.answer("Already processed.")
    await callback.message.edit_text(callback.message.text + "\n\n✅ Ticket Approved (Both notified).")
    await callback.answer()


@core_router.callback_query(F.data.startswith("adm_payout_apco_"))
async def process_admin_approval_channel_only(callback: CallbackQuery):
    if not evaluate_admin_access(callback.from_user.id):
        return
    tid    = int(callback.data.split("_")[3])
    result = await approve_withdrawal_core(tid, notify_mode="channel_only")
    if not result["ok"]:
        return await callback.answer("Already processed.")
    await callback.message.edit_text(callback.message.text + "\n\n✅ Ticket Approved (Channel only — user not DMed).")
    await callback.answer()

# ─────────────────────────────────────────────────────────────────────────────
# ADMIN — REJECT WITHDRAWAL
# ─────────────────────────────────────────────────────────────────────────────
@core_router.callback_query(F.data.startswith("adm_payout_rjmenu_"))
async def process_admin_rejection_menu(callback: CallbackQuery):
    if not evaluate_admin_access(callback.from_user.id):
        return
    tid = int(callback.data.split("_")[3])
    markup = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🤖 Multi-bot / Clone Account",      callback_data=f"rj_select_{tid}_multi_bot")],
        [InlineKeyboardButton(text="❌ Fake Activity / Emulators",       callback_data=f"rj_select_{tid}_fake_activity")],
        [InlineKeyboardButton(text="👥 No Organic Invites",              callback_data=f"rj_select_{tid}_no_invites")],
        [InlineKeyboardButton(text="✍️ Write Custom Reason",             callback_data=f"rj_select_{tid}_write_custom")],
        [InlineKeyboardButton(text="🔙 Cancel",                          callback_data="ui_admin_core")],
    ])
    await callback.message.edit_text("❌ <b>Select Rejection Reason:</b>", reply_markup=markup)

@core_router.callback_query(F.data.startswith("rj_select_"))
async def process_reason_selection(callback: CallbackQuery, state: FSMContext):
    if not evaluate_admin_access(callback.from_user.id):
        return
    parts  = callback.data.split("_")
    tid    = int(parts[2])
    choice = "_".join(parts[3:])
    ticket = await DataEngine.get_withdrawal(tid)
    if not ticket or ticket["status"] != "pending":
        return await callback.answer("Already processed.")
    if choice == "write_custom":
        await state.set_state(AdminConsoleWorkflow.write_reject_reason)
        await state.update_data(active_reject_tid=tid)
        return await callback.message.edit_text("✍️ <b>Write the rejection reason to send to user:</b>")
    reason_map = {
        "multi_bot":     "Multi-account / Clone system detected.",
        "fake_activity": "Fake verification / Fraudulent activity detected.",
        "no_invites":    "Insufficient organic or active referrals.",
    }
    reason = reason_map.get(choice, "Violated bot usage policies.")
    await execute_withdrawal_rejection(callback.message, tid, ticket, reason)

@core_router.message(AdminConsoleWorkflow.write_reject_reason)
async def process_custom_written_reason(message: Message, state: FSMContext):
    s = await state.get_data()
    await state.clear()
    tid    = s["active_reject_tid"]
    ticket = await DataEngine.get_withdrawal(tid)
    if not ticket or ticket["status"] != "pending":
        return await message.answer("Ticket already processed.")
    await execute_withdrawal_rejection(message, tid, ticket, message.text.strip())

async def execute_withdrawal_rejection(msg_obj, tid, ticket, reason):
    await DataEngine.update_withdrawal_status(tid, "rejected", ticket["channel_post_id"], reason)
    # Refund the reserved balance back to the user — it was deducted
    # atomically at request time in create_withdrawal_atomic().
    await DataEngine.add_balance(ticket["user_id"], float(ticket["amount"]))
    warning_notice = (
        f"❌ <b>Your Withdrawal Request has been Rejected!</b>\n\n"
        f"💰 <b>Amount:</b> <code>{ticket['amount']:.2f} Birr</code>\n"
        f"⚠️ <b>Reason:</b> <code>{sanitize_html(reason)}</code>\n\n"
        f"━━━━━━━━━━━━━━━━━━━━━━\n"
        f"📢 <b>IMPORTANT NOTICE:</b>\n"
        f"🇬🇧 Please invite real, organic, and active users.\n\n"
        f"🇪🇹 እባክዎ እውነተኛ ተጠቃሚዎችን ብቻ ይጋብዙ።\n"
        f"━━━━━━━━━━━━━━━━━━━━━━"
    )
    try:
        await bot.send_message(chat_id=ticket["user_id"], text=warning_notice)
    except Exception:
        pass
    reply_text = f"✅ Ticket #{tid} rejected. User notified."
    if msg_obj is None:
        return
    if isinstance(msg_obj, Message):
        await msg_obj.answer(reply_text, reply_markup=generate_admin_dashboard())
    else:
        await msg_obj.edit_text(reply_text, reply_markup=generate_admin_dashboard())

# ─────────────────────────────────────────────────────────────────────────────
# ADMIN — PANEL & SETTINGS
# ─────────────────────────────────────────────────────────────────────────────
@core_router.callback_query(F.data == "ui_admin_core")
async def process_admin_panel(callback: CallbackQuery):
    if not evaluate_admin_access(callback.from_user.id): return
    await callback.message.edit_text("⚙️ <b>Operational Admin Master Engine</b>", reply_markup=generate_admin_dashboard())

@core_router.callback_query(F.data == "adm_cmd_add_mand")
async def process_add_channel_start(callback: CallbackQuery, state: FSMContext):
    if not evaluate_admin_access(callback.from_user.id): return
    await state.set_state(AdminConsoleWorkflow.append_mandatory_id)
    await callback.message.edit_text(
        "🔴 <b>Force Join — Real Check</b>\nEnter Channel ID (e.g. <code>-1001234567890</code>):",
        reply_markup=generate_fallback_navigation("ui_admin_core")
    )

@core_router.message(AdminConsoleWorkflow.append_mandatory_id)
async def process_add_channel_id(message: Message, state: FSMContext):
    await state.update_data(ch_id=message.text.strip())
    await state.set_state(AdminConsoleWorkflow.append_mandatory_title)
    await message.answer("📝 <b>Enter Channel Display Title:</b>")

@core_router.message(AdminConsoleWorkflow.append_mandatory_title)
async def process_add_channel_title(message: Message, state: FSMContext):
    await state.update_data(ch_title=message.text.strip())
    await state.set_state(AdminConsoleWorkflow.append_mandatory_url)
    await message.answer("🔗 <b>Enter Channel Invite Link:</b>")

@core_router.message(AdminConsoleWorkflow.append_mandatory_url)
async def process_add_channel_finalize(message: Message, state: FSMContext):
    s = await state.get_data()
    await state.clear()
    await DataEngine.add_force_channel(s["ch_id"], s["ch_title"], message.text.strip(), bot_added=0)
    await message.answer(f"✅ <b>Force channel added!</b>\n📌 {sanitize_html(s['ch_title'])}", reply_markup=generate_admin_dashboard())

@core_router.callback_query(F.data == "adm_cmd_add_noadmin")
async def process_add_noadmin_start(callback: CallbackQuery, state: FSMContext):
    if not evaluate_admin_access(callback.from_user.id): return
    await state.set_state(AdminConsoleWorkflow.append_noadmin_link)
    await callback.message.edit_text(
        "🟡 <b>Fake Join (No Admin Required)</b>\n\nየቻናሉን ሊንክ አስገባ:",
        reply_markup=generate_fallback_navigation("ui_admin_core")
    )

@core_router.message(AdminConsoleWorkflow.append_noadmin_link)
async def process_noadmin_link(message: Message, state: FSMContext):
    await state.update_data(na_link=message.text.strip())
    await state.set_state(AdminConsoleWorkflow.append_noadmin_title)
    await message.answer("📝 <b>Enter Display Name:</b>")

@core_router.message(AdminConsoleWorkflow.append_noadmin_title)
async def process_noadmin_title(message: Message, state: FSMContext):
    s = await state.get_data()
    await state.clear()
    fake_key = "fake_" + hashlib.md5(s["na_link"].encode()).hexdigest()[:8]
    await DataEngine.add_force_channel(
        channel_id=fake_key, channel_name=message.text.strip(), invite_link=s["na_link"], bot_added=1
    )
    await message.answer(f"✅ <b>Fake ቻናል ተጨምሯል!</b>\n📌 {sanitize_html(message.text.strip())}", reply_markup=generate_admin_dashboard())

@core_router.callback_query(F.data == "adm_cmd_list_channels")
async def process_list_channels(callback: CallbackQuery):
    if not evaluate_admin_access(callback.from_user.id): return
    channels = await DataEngine.get_force_channels()
    if not channels:
        return await callback.message.edit_text("📭 No channels.", reply_markup=generate_fallback_navigation("ui_admin_core"))
    lines = []
    for ch in channels:
        mode = "🟡 Fake" if ch["bot_added"] else "🔴 Real"
        lines.append(f"{mode} — <b>{sanitize_html(ch['channel_name'])}</b>\n🔗 {ch['invite_link']}")
    await callback.message.edit_text(
        f"📋 <b>Force Channels ({len(channels)})</b>\n\n" + "\n\n".join(lines),
        reply_markup=generate_fallback_navigation("ui_admin_core")
    )

@core_router.callback_query(F.data == "adm_cmd_rm_node")
async def process_rm_channel_menu(callback: CallbackQuery):
    if not evaluate_admin_access(callback.from_user.id): return
    channels = await DataEngine.get_force_channels()
    if not channels:
        return await callback.message.edit_text("📭 No channels.", reply_markup=generate_fallback_navigation("ui_admin_core"))
    buttons = []
    for ch in channels:
        mode = "🟡" if ch["bot_added"] else "🔴"
        buttons.append([InlineKeyboardButton(text=f"🗑 {mode} {sanitize_html(ch['channel_name'])}", callback_data=f"execute_rm_node_{ch['id']}")])
    buttons.append([InlineKeyboardButton(text="🔙 Back", callback_data="ui_admin_core")])
    await callback.message.edit_text("<b>Select channel to remove:</b>", reply_markup=InlineKeyboardMarkup(inline_keyboard=buttons))

@core_router.callback_query(F.data.startswith("execute_rm_node_"))
async def process_rm_channel_action(callback: CallbackQuery):
    if not evaluate_admin_access(callback.from_user.id): return
    row_id = int(callback.data.replace("execute_rm_node_", ""))
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute("DELETE FROM force_channels WHERE id = ?", (row_id,))
        await db.commit()
    await callback.message.edit_text("✅ Channel removed.", reply_markup=generate_admin_dashboard())

# ─────────────────────────────────────────────────────────────────────────────
# ADMIN — STOP / RESUME BOT ENGINE
#
# Stopping the bot ONLY stops Telegram long-polling (no new /start, button
# taps, or admin replies are processed). It does NOT touch the SQLite
# database, the Mini App, or any stored balances/verifications/withdrawals —
# all of that data is safe on disk the entire time. The "Resume Polling"
# button below restarts the polling task in the same running process, so an
# admin can pause and resume the bot without losing anything or having to
# redeploy — as long as the underlying process/server itself stays alive.
# ─────────────────────────────────────────────────────────────────────────────
_polling_task: asyncio.Task | None = None
BOT_USERNAME: str = ""
BOT_ID: int = 0

@core_router.callback_query(F.data == "adm_stop_bot_confirm1")
async def stop_bot_first_confirmation(callback: CallbackQuery):
    if not evaluate_admin_access(callback.from_user.id): return
    markup = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="⚠️ ኃላፊነቱን እወስዳለሁ - ቀጥል", callback_data="adm_stop_bot_confirm2")],
        [InlineKeyboardButton(text="❌ አቁም/ተመለስ",               callback_data="ui_admin_core")],
    ])
    await callback.message.edit_text(
        "🚨 <b>FIRST WARNING!</b>\n\n"
        "ቦቱን ማቆም ከፈለጉ እርግጠኛ ነዎት? (ይህ የ chat polling ብቻ ያቆማል — መረጃ/ሒሳብ አይጠፋም)",
        reply_markup=markup
    )

@core_router.callback_query(F.data == "adm_stop_bot_confirm2")
async def stop_bot_final_confirmation(callback: CallbackQuery):
    if not evaluate_admin_access(callback.from_user.id): return
    markup = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🛑 አሁኑኑ ቦቱ ይቁም!", callback_data="adm_stop_bot_execute")],
        [InlineKeyboardButton(text="❌ ተመለስ",          callback_data="ui_admin_core")],
    ])
    await callback.message.edit_text("🛑 <b>FINAL CONFIRMATION!</b>", reply_markup=markup)

@core_router.callback_query(F.data == "adm_stop_bot_execute")
async def execute_bot_shutdown(callback: CallbackQuery):
    if not evaluate_admin_access(callback.from_user.id): return
    await callback.message.edit_text(
        "🛑 <b>Bot polling stopped.</b>\n\n"
        "✅ All data, balances, and Mini App verification are safe and untouched.\n"
        "▶️ Tap below to resume any time (process must still be running).",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=[[
            InlineKeyboardButton(text="▶️ Resume Polling / ቀጥል", callback_data="adm_resume_bot_execute")
        ]])
    )
    await dp.stop_polling()

@core_router.callback_query(F.data == "adm_resume_bot_execute")
async def execute_bot_resume(callback: CallbackQuery):
    global _polling_task
    if not evaluate_admin_access(callback.from_user.id): return
    if _polling_task is None or _polling_task.done():
        _polling_task = asyncio.create_task(dp.start_polling(bot, skip_updates=True))
    await callback.message.edit_text(
        "✅ <b>Bot polling resumed.</b> All data is intact.",
        reply_markup=generate_admin_dashboard()
    )

@core_router.callback_query(F.data == "adm_cmd_edit_bal")
async def process_edit_balance_start(callback: CallbackQuery, state: FSMContext):
    if not evaluate_admin_access(callback.from_user.id): return
    await state.set_state(AdminConsoleWorkflow.direct_balance_target_id)
    await callback.message.edit_text("<b>Enter Targeted Telegram User ID:</b>", reply_markup=generate_fallback_navigation("ui_admin_core"))

@core_router.message(AdminConsoleWorkflow.direct_balance_target_id)
async def process_edit_balance_id(message: Message, state: FSMContext):
    await state.update_data(target_uid=int(message.text.strip()))
    await state.set_state(AdminConsoleWorkflow.direct_balance_volume)
    await message.answer("<b>Enter Adjustment Volume (e.g. 50 or -50):</b>")

@core_router.message(AdminConsoleWorkflow.direct_balance_volume)
async def process_edit_balance_final(message: Message, state: FSMContext):
    s = await state.get_data()
    await state.clear()
    await DataEngine.add_balance(s["target_uid"], float(message.text.strip()))
    await message.answer("✅ Balance adjusted.", reply_markup=generate_admin_dashboard())

@core_router.callback_query(F.data == "adm_cmd_stats")
async def process_stats(callback: CallbackQuery):
    if not evaluate_admin_access(callback.from_user.id): return
    async with aiosqlite.connect(DB_PATH) as db:
        cur  = await db.execute("SELECT COUNT(*), SUM(balance) FROM users")
        row  = await cur.fetchone()
        cur2 = await db.execute("SELECT COUNT(*) FROM banned_ips")
        ip_count = (await cur2.fetchone())[0] or 0
        cur3 = await db.execute("SELECT COUNT(*) FROM fraud_log")
        fraud_count = (await cur3.fetchone())[0] or 0
    await callback.message.edit_text(
        f"📊 <b>Bot Analytics:</b>\n\n"
        f"• Registered Users: <b>{row[0] or 0}</b>\n"
        f"• Outstanding Liabilities: <b>{float(row[1] or 0.0):.2f} ETB</b>\n"
        f"• Banned IPs: <b>{ip_count}</b>\n"
        f"• Fraud Log Entries: <b>{fraud_count}</b>",
        reply_markup=generate_fallback_navigation("ui_admin_core")
    )

@core_router.callback_query(F.data == "adm_cmd_backup_now")
async def process_backup_now(callback: CallbackQuery):
    if not evaluate_admin_access(callback.from_user.id): return
    if not DB_BACKUP_CHANNEL_ID:
        await callback.answer("⚠️ DB_BACKUP_CHANNEL_ID is not set in Railway Variables.", show_alert=True)
        return
    await callback.answer("📤 Sending backup…")
    await send_db_backup()
    await callback.message.edit_text(
        "✅ <b>Backup sent</b> to your private backup channel.",
        reply_markup=generate_fallback_navigation("ui_admin_core")
    )

@core_router.callback_query(F.data == "adm_cmd_search")
async def process_search_start(callback: CallbackQuery, state: FSMContext):
    if not evaluate_admin_access(callback.from_user.id): return
    await state.set_state(AdminConsoleWorkflow.lookup_individual_id)
    await callback.message.edit_text("🔍 <b>Enter Target User Telegram ID:</b>", reply_markup=generate_fallback_navigation("ui_admin_core"))

@core_router.message(AdminConsoleWorkflow.lookup_individual_id)
async def process_search_execute(message: Message, state: FSMContext):
    await state.clear()
    try:
        target = int(message.text.strip())
    except ValueError:
        return await message.answer("❌ Invalid ID.", reply_markup=generate_admin_dashboard())
    user = await DataEngine.get_user(target)
    if not user:
        return await message.answer("❌ User not found.", reply_markup=generate_admin_dashboard())
    direct, tier2 = await DataEngine.get_referral_metrics(target)
    verif    = await DataEngine.get_verification(target)
    ip_info  = f"<code>{verif['ip_address']}</code>"  if verif else "Not verified"
    ref_ip   = f"<code>{verif['referrer_ip']}</code>" if (verif and verif['referrer_ip']) else "N/A"
    tg_plat  = (verif['tg_platform']    or "N/A") if verif else "N/A"
    tg_ver   = (verif['tg_version']     or "N/A") if verif else "N/A"
    tg_app   = (verif['tg_app_version'] or "N/A") if verif else "N/A"
    canvas   = (verif['canvas_hash'][:16] + "…" if verif and verif.get('canvas_hash') else "N/A")
    webgl    = (verif['webgl_hash'][:16]  + "…" if verif and verif.get('webgl_hash')  else "N/A")

    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute(
            "SELECT reason, logged_at FROM fraud_log WHERE user_id = ? ORDER BY logged_at DESC LIMIT 3",
            (target,)
        )
        fraud_rows = await cur.fetchall()
    fraud_txt = ""
    if fraud_rows:
        fraud_txt = "\n⚠️ <b>Fraud Flags:</b>\n" + "\n".join(
            f"  • <code>{r['reason']}</code> @ {r['logged_at']}" for r in fraud_rows
        )

    await message.answer(
        f"👤 <b>User Profile:</b>\n\n"
        f"• Name: {sanitize_html(user['full_name'])}\n"
        f"• Alias: @{sanitize_html(user['username'] or 'N/A')}\n"
        f"• Balance: <b>{float(user['balance']):.2f} Birr</b>\n"
        f"• Direct Invites: <b>{direct}</b>\n"
        f"• Tier-2 Network: <b>{tier2}</b>\n"
        f"• Banned: <b>{'Yes' if user['is_banned'] else 'No'}</b>\n"
        f"• IP Address: {ip_info}\n"
        f"• Referrer IP: {ref_ip}\n"
        f"• TG Platform: <b>{tg_plat}</b>\n"
        f"• TG Version: <b>{tg_ver}</b>\n"
        f"• TG App Version: <b>{tg_app}</b>\n"
        f"• Canvas Hash: <code>{canvas}</code>\n"
        f"• WebGL Hash: <code>{webgl}</code>\n"
        f"• Joined: {user['joined_at']}"
        f"{fraud_txt}",
        reply_markup=generate_admin_dashboard()
    )

@core_router.callback_query(F.data == "adm_cmd_ban")
async def process_ban_start(callback: CallbackQuery, state: FSMContext):
    if not evaluate_admin_access(callback.from_user.id): return
    await state.set_state(AdminConsoleWorkflow.ban_individual_id)
    await callback.message.edit_text(
        "🚫 <b>Ban User</b>\n\nEnter the Telegram User ID to ban:",
        reply_markup=generate_fallback_navigation("ui_admin_core")
    )

@core_router.message(AdminConsoleWorkflow.ban_individual_id)
async def process_ban_execute(message: Message, state: FSMContext):
    await state.clear()
    try:
        target = int(message.text.strip())
    except ValueError:
        return await message.answer("❌ Invalid ID.", reply_markup=generate_admin_dashboard())
    await DataEngine.ban_user(target, 1)
    try:
        await bot.send_message(target, "🚫 <b>Your account has been banned from this bot.</b>")
    except Exception:
        pass
    await message.answer(f"✅ User <code>{target}</code> has been banned.", reply_markup=generate_admin_dashboard())

@core_router.callback_query(F.data == "adm_cmd_reward")
async def process_reward_start(callback: CallbackQuery, state: FSMContext):
    if not evaluate_admin_access(callback.from_user.id): return
    await state.set_state(AdminConsoleWorkflow.modify_referral_bounty)
    await callback.message.edit_text("<b>Enter New Reward Per Referral (Birr):</b>", reply_markup=generate_fallback_navigation("ui_admin_core"))

@core_router.message(AdminConsoleWorkflow.modify_referral_bounty)
async def process_reward_execute(message: Message, state: FSMContext):
    await DataEngine.set_setting("reward_per_referral", message.text.strip())
    await state.clear()
    await message.answer("✅ Bounty updated.", reply_markup=generate_admin_dashboard())

@core_router.callback_query(F.data == "adm_cmd_min_wd")
async def process_min_wd_start(callback: CallbackQuery, state: FSMContext):
    if not evaluate_admin_access(callback.from_user.id): return
    await state.set_state(AdminConsoleWorkflow.modify_minimum_cashout)
    await callback.message.edit_text("<b>Enter New Minimum Cashout Threshold (Birr):</b>", reply_markup=generate_fallback_navigation("ui_admin_core"))

@core_router.message(AdminConsoleWorkflow.modify_minimum_cashout)
async def process_min_wd_execute(message: Message, state: FSMContext):
    await DataEngine.set_setting("min_withdrawal", message.text.strip())
    await state.clear()
    await message.answer("✅ Minimum withdrawal updated.", reply_markup=generate_admin_dashboard())

@core_router.callback_query(F.data == "adm_cmd_pending_tickets")
async def process_pending_inventory(callback: CallbackQuery):
    if not evaluate_admin_access(callback.from_user.id): return
    pending = await DataEngine.get_pending_withdrawals()
    if not pending:
        return await callback.message.edit_text("📭 No pending withdrawals.", reply_markup=generate_fallback_navigation("ui_admin_core"))
    lines = [f"• <b>#{t['id']}</b> — {sanitize_html(t['full_name'])} — <code>{float(t['amount']):.2f} ETB</code>" for t in pending]
    await callback.message.edit_text(
        f"📥 <b>Pending Withdrawals ({len(pending)})</b>\n\n" + "\n".join(lines),
        reply_markup=generate_fallback_navigation("ui_admin_core")
    )

@core_router.callback_query(F.data == "adm_cmd_broadcast")
async def process_broadcast_start(callback: CallbackQuery, state: FSMContext):
    if not evaluate_admin_access(callback.from_user.id): return
    await state.set_state(AdminConsoleWorkflow.broadcast_intel_payload)
    await callback.message.edit_text("📢 <b>Enter Broadcast Message:</b>", reply_markup=generate_fallback_navigation("ui_admin_core"))

@core_router.message(AdminConsoleWorkflow.broadcast_intel_payload)
async def process_broadcast_preview(message: Message, state: FSMContext):
    text = message.text
    await state.update_data(bc_payload=text)
    await state.set_state(AdminConsoleWorkflow.broadcast_confirmation)
    markup = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🚀 Send Now",  callback_data="bc_action_confirm")],
        [InlineKeyboardButton(text="✍️ Edit",       callback_data="adm_cmd_broadcast")],
        [InlineKeyboardButton(text="❌ Cancel",     callback_data="ui_admin_core")],
    ])
    await message.answer(f"📝 <b>Preview:</b>\n\n{text}\n\n⚠️ Send to all users?", reply_markup=markup)

@core_router.callback_query(F.data == "bc_action_confirm", AdminConsoleWorkflow.broadcast_confirmation)
async def process_broadcast_execute(callback: CallbackQuery, state: FSMContext):
    s    = await state.get_data()
    text = s["bc_payload"]
    await state.clear()
    progress = await callback.message.edit_text("⏳ Sending broadcast...")
    async with aiosqlite.connect(DB_PATH) as db:
        cur   = await db.execute("SELECT user_id FROM users")
        nodes = await cur.fetchall()
    sent_count = 0
    fail_count = 0
    for (uid,) in nodes:
        try:
            await bot.send_message(uid, text)
            sent_count += 1
            await asyncio.sleep(0.05)
        except Exception as e:
            err_str = str(e)
            if "RetryAfter" in err_str:
                try:
                    wait = int(''.join(filter(str.isdigit, err_str))) + 1
                except Exception:
                    wait = 30
                await asyncio.sleep(wait)
                try:
                    await bot.send_message(uid, text)
                    sent_count += 1
                except Exception:
                    fail_count += 1
            else:
                fail_count += 1
    try:
        await progress.delete()
    except Exception:
        pass
    await callback.message.answer(
        f"✅ Broadcast complete.\n• Sent: {sent_count}\n• Failed: {fail_count}",
        reply_markup=generate_admin_dashboard()
    )

@core_router.callback_query(F.data == "adm_cmd_unban_menu")
async def process_unban_dashboard(callback: CallbackQuery):
    if not evaluate_admin_access(callback.from_user.id): return
    markup = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✅ Standard Unban (Requires MiniApp)", callback_data="unban_trigger_std")],
        [InlineKeyboardButton(text="🔥 Full Unban (Bypass MiniApp)",       callback_data="unban_trigger_full")],
        [InlineKeyboardButton(text="🔙 Back",                               callback_data="ui_admin_core")],
    ])
    await callback.message.edit_text("🔓 <b>Select Unban Method:</b>", reply_markup=markup)

@core_router.callback_query(F.data == "unban_trigger_std")
async def process_std_unban_start(callback: CallbackQuery, state: FSMContext):
    if not evaluate_admin_access(callback.from_user.id): return
    await state.set_state(AdminConsoleWorkflow.pardon_individual_std)
    await callback.message.edit_text(
        "👤 <b>[Standard Unban]</b> Enter Telegram User ID:",
        reply_markup=generate_fallback_navigation("adm_cmd_unban_menu")
    )

@core_router.message(AdminConsoleWorkflow.pardon_individual_std)
async def process_std_unban_execute(message: Message, state: FSMContext):
    try:
        target = int(message.text.strip())
        await DataEngine.ban_user(target, 0)
        await DataEngine.full_clear_verification(target)
        await state.clear()
        await message.answer(
            f"✅ Standard Unban done. User <code>{target}</code> must reverify via Mini App.",
            reply_markup=generate_admin_dashboard()
        )
    except ValueError:
        await message.answer("❌ Invalid ID.")

@core_router.callback_query(F.data == "unban_trigger_full")
async def process_full_unban_start(callback: CallbackQuery, state: FSMContext):
    if not evaluate_admin_access(callback.from_user.id): return
    await state.set_state(AdminConsoleWorkflow.pardon_individual_full)
    await callback.message.edit_text(
        "🔥 <b>[Full Unban]</b> Enter Telegram User ID:",
        reply_markup=generate_fallback_navigation("adm_cmd_unban_menu")
    )

@core_router.message(AdminConsoleWorkflow.pardon_individual_full)
async def process_full_unban_execute(message: Message, state: FSMContext):
    try:
        target = int(message.text.strip())
        # IMPORTANT: inject_fake_verification() writes straight into the
        # verifications table, which makes is_verified(target)=True even
        # though the user never actually completed the Mini App fingerprint
        # flow. This is intentionally scoped to ONLY the target user_id
        # passed in here — it must never be applied in bulk, since it
        # bypasses fraud/fingerprint checks for whoever it's used on.
        await DataEngine.ban_user(target, 0)
        await DataEngine.inject_fake_verification(target)
        await state.clear()
        await message.answer(
            f"🔥 Full Unban done. User <code>{target}</code> is unbanned and "
            f"marked verified — they will NOT be asked to open the Mini App again.",
            reply_markup=generate_admin_dashboard()
        )
    except ValueError:
        await message.answer("❌ Invalid ID.")


# ═════════════════════════════════════════════════════════════════════════
# WIRING — attach all @core_router handlers to the Dispatcher
#
# CRITICAL FIX: this call was missing entirely. Every @core_router.message
# and @core_router.callback_query handler defined above (process_start_
# command, the whole admin panel, withdrawals, everything) was NEVER
# reachable, because a Router only does anything once it's registered on
# the Dispatcher that's actually polling Telegram.
# ═════════════════════════════════════════════════════════════════════════
dp.include_router(core_router)

# ═════════════════════════════════════════════════════════════════════════
# WEB API — Mini App REST backend (FastAPI)
#
# CRITICAL FIX: fastapi/uvicorn were imported at the top of this file and
# referenced in comments ("...the Mini App REST endpoint (/api/withdraw)")
# as if this layer already existed, but no FastAPI app, no routes, and no
# uvicorn server were ever defined anywhere in the file. frontend/app.html
# was written entirely against this contract, so none of it could work
# until now.
#
# Every route is called by app.html's api() helper, which POSTs
# { initData, ...extra } as JSON. initData is Telegram's signed WebApp
# payload — validated below via parse_telegram_webapp_handshake() so a
# user cannot spoof another user's Telegram ID from the browser.
# ═════════════════════════════════════════════════════════════════════════
api_app = FastAPI()

api_app.add_middleware(
    CORSMiddleware,
    allow_origins=[ALLOWED_ORIGIN] if ALLOWED_ORIGIN else ["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)


@api_app.middleware("http")
async def _no_store_cache_headers(request, call_next):
    """Every /api/* response carries per-user data (balance, referrals,
    withdrawal history, ...). Without explicit no-store headers, some
    mobile browsers/webviews will happily serve a cached copy of a
    previous response — which on a shared device could mean showing one
    Telegram account's balance to whoever opens the Mini App next. This
    guarantees every response is always freshly fetched."""
    response = await call_next(request)
    response.headers["Cache-Control"] = "no-store, no-cache, must-revalidate"
    response.headers["Pragma"] = "no-cache"
    return response


class ApiBase(BaseModel):
    initData: str = ""


async def _authenticate(body: ApiBase) -> dict:
    """Validates Telegram WebApp initData and returns the users-table row
    as a plain dict. Creates the user row on first contact (mirrors what
    /start does on the bot side) and bumps last_seen for the online-users
    stat. Raises 401 for a bad signature and 403 for a banned account."""
    tg_user = parse_telegram_webapp_handshake(body.initData)
    if not tg_user or "id" not in tg_user:
        raise HTTPException(status_code=401, detail="invalid_init_data")
    user_id = int(tg_user["id"])
    row = await DataEngine.get_user(user_id)
    if not row:
        full_name = (
            f"{tg_user.get('first_name', '')} {tg_user.get('last_name', '')}".strip()
            or tg_user.get("username", "") or str(user_id)
        )
        await DataEngine.create_user(user_id, tg_user.get("username", "") or "", full_name)
        row = await DataEngine.get_user(user_id)
    await DataEngine.touch_last_seen(user_id)
    if row["is_banned"]:
        raise HTTPException(status_code=403, detail="banned")
    return dict(row)


def _require_admin(user: dict):
    if not evaluate_admin_access(user["user_id"]):
        raise HTTPException(status_code=403, detail="not_admin")


async def broadcast_to_all_users(text: str, reply_markup: InlineKeyboardMarkup | None = None) -> tuple[int, int]:
    """Shared broadcast sender — used by /api/admin/broadcast (free-text
    announcements) and /api/admin/tasks/broadcast (new-task announcements
    with an Open App button)."""
    async with aiosqlite.connect(DB_PATH) as db:
        cur = await db.execute("SELECT user_id FROM users")
        rows = await cur.fetchall()
    sent, failed = 0, 0
    for (uid,) in rows:
        try:
            await bot.send_message(uid, text, reply_markup=reply_markup)
            sent += 1
            await asyncio.sleep(0.05)
        except Exception as e:
            err_str = str(e)
            if "RetryAfter" in err_str:
                try:
                    wait = int("".join(filter(str.isdigit, err_str))) + 1
                except Exception:
                    wait = 30
                await asyncio.sleep(wait)
                try:
                    await bot.send_message(uid, text, reply_markup=reply_markup)
                    sent += 1
                except Exception:
                    failed += 1
            else:
                failed += 1
    return sent, failed


@api_app.get("/health")
async def health_check():
    return {"ok": True}


# ── /api/verify — identity/fingerprint verification (index.html) ────────
#
# CRITICAL FIX #2: this endpoint was ALSO completely missing. It's not
# part of the app.html contract — it's the fraud-detection intake used by
# index.html (the "Security Check" screen linked from generate_verifica-
# tion_widget()). This is where evaluate_clone_risk(), the IP cooldown,
# the VPN check, and the referral payout all actually run. Without this
# route, /start would send a "Verify identity" button whose Mini App link
# posted to /api/verify and got a 404 forever — which is exactly what
# showed up in the Railway logs.
#
# Response contract (matches index.html exactly):
#   200 {"status": "verified"}            → new account created & passed
#   200 {"status": "already_verified"}     → idempotent replay of an old link
#   200 {"status": "blocked", "reason": X} → soft or hard block, NOT an
#                                            HTTP error (index.html only
#                                            treats non-2xx as "server
#                                            error", so blocks must be 200)
#   429                                    → per-user rate limit hit
class VerifyRequest(BaseModel):
    uid: int
    refId: int = 0
    msgId: int = 0
    initData: str = ""
    ua: str = ""
    fingerprint: str = ""
    canvasHash: str = ""
    webglHash: str = ""
    screenSig: str = ""
    tgPlatform: str = ""
    tgVersion: str = ""
    tgAppVersion: str = ""


@api_app.post("/api/verify")
async def api_verify(body: VerifyRequest, request: Request):
    # The uid comes from a URL query param on index.html (?uid=...), which
    # is user-editable — so it must be cross-checked against the
    # cryptographically signed initData, which always reflects whoever is
    # ACTUALLY logged into the current Telegram session.
    tg_user = parse_telegram_webapp_handshake(body.initData)
    if not tg_user or "id" not in tg_user or int(tg_user["id"]) != body.uid:
        raise HTTPException(status_code=401, detail="invalid_init_data")

    uid = body.uid
    ref = body.refId if body.refId and body.refId != uid else 0

    if await DataEngine.is_verified(uid):
        return {"status": "already_verified"}

    if not await verify_limiter.is_allowed(str(uid)):
        raise HTTPException(status_code=429, detail="too_many_attempts")

    client_ip = extract_real_ip(request)

    on_cooldown, remaining = await ip_cooldown.is_on_cooldown(client_ip)
    if on_cooldown:
        return {"status": "blocked", "reason": "ip_cooldown", "retry_after": remaining}

    fp_ok = bool(body.fingerprint) and body.fingerprint not in ("undefined", "null", "")
    if not fp_ok:
        return {"status": "blocked", "reason": "no_fingerprint"}

    if await DataEngine.is_ip_banned(client_ip):
        await DataEngine.log_fraud_attempt(uid, "banned_ip_attempt", client_ip)
        return {"status": "blocked", "reason": "banned_ip"}

    if await execute_network_vpn_lookup(client_ip):
        return {"status": "blocked", "reason": "vpn"}

    should_ban, reason = await evaluate_clone_risk(
        uid, ref, client_ip, body.fingerprint,
        body.tgPlatform, body.tgVersion, body.tgAppVersion,
        body.canvasHash, body.webglHash, body.screenSig,
    )
    if should_ban:
        await DataEngine.log_fraud_attempt(uid, reason, client_ip, "auto-blocked at verification")
        if reason == "ip_farm":
            await DataEngine.ban_ip(client_ip, reason)
        return {"status": "blocked", "reason": reason}

    # Passed every check — create the account (linking the referrer only
    # on first creation), save the verification fingerprint, start the IP
    # cooldown window, and pay the referrer's bonus.
    referrer_row = await DataEngine.get_user(ref) if ref else None
    referred_by = ref if referrer_row else None

    existing = await DataEngine.get_user(uid)
    if not existing:
        full_name = (
            f"{tg_user.get('first_name', '')} {tg_user.get('last_name', '')}".strip()
            or tg_user.get("username", "") or str(uid)
        )
        await DataEngine.create_user(uid, tg_user.get("username", "") or "", full_name, referred_by)

    await DataEngine.save_verification(
        uid, client_ip, body.ua, body.fingerprint,
        referrer_ip="", tg_platform=body.tgPlatform, tg_version=body.tgVersion,
        tg_app_version=body.tgAppVersion, canvas_hash=body.canvasHash,
        webgl_hash=body.webglHash, screen_sig=body.screenSig,
    )
    await ip_cooldown.mark_verified(client_ip)

    if referred_by:
        direct_count, _ = await DataEngine.get_referral_metrics(referred_by)
        # direct_count already includes the referral we just created above,
        # so it IS this referral's 1-indexed position for this referrer.
        skipped = await DataEngine.is_referral_skipped(referred_by, direct_count)
        if not skipped:
            rate = float(await DataEngine.get_setting("reward_per_referral", "10"))
            await DataEngine.add_balance(referred_by, rate)
            try:
                await bot.send_message(
                    referred_by,
                    f"🎉 Someone joined using your referral link! +{rate:.2f} Birr credited to your balance."
                )
            except Exception:
                pass
        else:
            # Not paid — and hidden from the referrer's own "Direct" count
            # too (get_paid_referral_metrics), so the skip pattern stays
            # invisible to them in every number they can see, not just in
            # the missing payout message.
            await DataEngine.mark_referral_unpaid(uid)

    if body.msgId:
        try:
            await bot.delete_message(chat_id=uid, message_id=body.msgId)
        except Exception:
            pass
    try:
        await bot.send_message(
            uid, "✅ <b>Verified!</b> Welcome in.",
            reply_markup=generate_dashboard_matrix(uid)
        )
    except Exception:
        pass

    return {"status": "verified"}


# ── /api/me ──────────────────────────────────────────────────────────────
@api_app.post("/api/me")
async def api_me(body: ApiBase):
    user = await _authenticate(body)
    direct, tier2 = await DataEngine.get_paid_referral_metrics(user["user_id"])
    rate = float(await DataEngine.get_setting("reward_per_referral", "10"))
    min_w = float(await DataEngine.get_setting("min_withdrawal", "50"))
    uname = BOT_USERNAME or (await bot.get_me()).username
    return {
        "user_id": user["user_id"],
        "balance": float(user["balance"]),
        "referrals": direct,
        "tier2_referrals": tier2,
        "reward_per_referral": rate,
        "min_withdrawal": min_w,
        "total_earned_refs": round(direct * rate, 2),
        "referral_link": f"https://t.me/{uname}?start={user['user_id']}",
        "is_admin": evaluate_admin_access(user["user_id"]),
        "support_username": (await DataEngine.get_setting("support_username", "") or "").lstrip("@"),
    }


# ── /api/invite/share_card — sends the user a ready-to-forward invite
#    message (bot's photo + a written invite caption + an inline button
#    holding their referral link) in their own chat with the bot, so they
#    can just long-press → Forward it straight to friends. ────────────────
SHARE_CARD_COOLDOWN_SECONDS = 25 * 60


@api_app.post("/api/invite/share_card")
async def api_invite_share_card(body: ApiBase):
    user = await _authenticate(body)
    uid = user["user_id"]

    last_at = await DataEngine.get_last_ad_event(uid, "share_card")
    if last_at:
        try:
            elapsed = (datetime.utcnow() - datetime.strptime(last_at, "%Y-%m-%d %H:%M:%S")).total_seconds()
            remaining = int(SHARE_CARD_COOLDOWN_SECONDS - elapsed)
            if remaining > 0:
                raise HTTPException(status_code=400, detail=f"cooldown:{remaining}")
        except HTTPException:
            raise
        except Exception:
            pass  # bad timestamp format — don't block the user over it

    caption, kb, photo_id = await _build_invite_card(uid)
    try:
        if photo_id:
            await bot.send_photo(chat_id=uid, photo=photo_id, caption=caption, reply_markup=kb)
        else:
            await bot.send_message(chat_id=uid, text=caption, reply_markup=kb)
    except Exception:
        raise HTTPException(status_code=503, detail="send_failed")
    await DataEngine.record_ad_event(uid, "share_card", 0)
    return {"ok": True}


# ── /api/gate/* — force-join gate ────────────────────────────────────────
@api_app.post("/api/gate/status")
async def api_gate_status(body: ApiBase):
    user = await _authenticate(body)
    uid = user["user_id"]
    force_unjoined = []
    if not evaluate_admin_access(uid):
        force_unjoined = await inspect_compulsory_memberships(uid)
    all_channels = await DataEngine.get_force_channels()
    fake_channels = [dict(c) for c in all_channels if c["bot_added"] == 1]
    fake_seen = await DataEngine.has_seen_fake_join(uid)
    return {
        "force_unjoined": [dict(c) for c in force_unjoined],
        "fake_channels": fake_channels,
        "fake_seen": fake_seen,
    }


@api_app.post("/api/gate/fake_seen")
async def api_gate_fake_seen(body: ApiBase):
    user = await _authenticate(body)
    await DataEngine.mark_fake_join_seen(user["user_id"])
    return {"ok": True}


# ── /api/ads/* — AdsGram rewarded video + Direct Link ────────────────────
AD_KIND_VIDEO  = "video"
AD_KIND_DIRECT = "direct_link"


class AdClickRequest(ApiBase):
    kind: str = "video"


@api_app.post("/api/ads/click")
async def api_ads_click(body: AdClickRequest):
    """Fire-and-forget analytics ping — called the instant the user taps
    'Watch Ad', before we know if they'll actually finish it. Purely for
    the admin 'clicks vs completions' dashboard; never affects rewards
    or daily limits."""
    user = await _authenticate(body)
    kind = body.kind if body.kind in (AD_KIND_VIDEO, AD_KIND_DIRECT) else AD_KIND_VIDEO
    await DataEngine.log_ad_click(user["user_id"], kind)
    return {"ok": True}


@api_app.post("/api/ads/status")
async def api_ads_status(body: ApiBase):
    user = await _authenticate(body)
    uid = user["user_id"]

    ads_enabled      = (await DataEngine.get_setting("ads_enabled", "0")) == "1"
    block_id         = await DataEngine.get_setting("adsgram_block_id", "") or ""
    reward_amount    = float(await DataEngine.get_setting("ad_reward_amount", "0.5"))
    daily_limit      = int(await DataEngine.get_setting("ad_daily_limit", "10"))
    cooldown_seconds = int(await DataEngine.get_setting("ad_cooldown_seconds", "30"))

    watched_today = await DataEngine.count_ad_events_today(uid, AD_KIND_VIDEO)
    seconds_left = 0
    last_at = await DataEngine.get_last_ad_event(uid, AD_KIND_VIDEO)
    if last_at:
        try:
            elapsed = (datetime.utcnow() - datetime.strptime(last_at, "%Y-%m-%d %H:%M:%S")).total_seconds()
            seconds_left = max(0, int(cooldown_seconds - elapsed))
        except Exception:
            pass

    direct_link         = (await DataEngine.get_setting("adsgram_direct_link", "") or "").strip()
    dl_reward           = float(await DataEngine.get_setting("direct_link_reward_amount", "0.3"))
    dl_daily_limit       = int(await DataEngine.get_setting("direct_link_daily_limit", "10"))
    dl_wait_seconds      = int(await DataEngine.get_setting("direct_link_wait_seconds", "15"))
    dl_cooldown_seconds  = int(await DataEngine.get_setting("direct_link_cooldown_seconds", "30"))
    dl_watched_today     = await DataEngine.count_ad_events_today(uid, AD_KIND_DIRECT)
    dl_seconds_left = 0
    dl_last_at = await DataEngine.get_last_ad_event(uid, AD_KIND_DIRECT)
    if dl_last_at:
        try:
            elapsed = (datetime.utcnow() - datetime.strptime(dl_last_at, "%Y-%m-%d %H:%M:%S")).total_seconds()
            dl_seconds_left = max(0, int(dl_cooldown_seconds - elapsed))
        except Exception:
            pass

    # Monetag — fallback rewarded network, tried client-side only when
    # AdsGram reports no fill. Doesn't have its own limit/cooldown; it
    # shares the video ad's daily_limit/cooldown/reward above.
    monetag_zone_id = (await DataEngine.get_setting("monetag_zone_id", "") or "").strip()
    monetag_sdk_url = (await DataEngine.get_setting("monetag_sdk_url", "") or "").strip()

    return {
        "enabled": ads_enabled and bool(block_id or monetag_zone_id),
        "block_id": block_id,
        "reward_amount": reward_amount,
        "daily_limit": daily_limit,
        "watched_today": watched_today,
        "seconds_left": seconds_left,
        "monetag": {
            "zone_id": monetag_zone_id,
            "sdk_url": monetag_sdk_url,
        },
        "direct_link": {
            "enabled": ads_enabled and bool(direct_link),
            "url": direct_link,
            "reward_amount": dl_reward,
            "daily_limit": dl_daily_limit,
            "watched_today": dl_watched_today,
            "seconds_left": dl_seconds_left,
            "wait_seconds": dl_wait_seconds,
        },
    }


@api_app.post("/api/ads/claim")
async def api_ads_claim(body: ApiBase):
    """Rewarded video — the AdsGram SDK promise on the frontend already
    confirmed the ad played to completion before this is ever called, so
    we only need to re-check the daily cap / cooldown server-side (the
    SDK promise resolving is not, by itself, something to trust for
    payouts — a compromised client could call this directly)."""
    user = await _authenticate(body)
    uid = user["user_id"]

    ads_enabled = (await DataEngine.get_setting("ads_enabled", "0")) == "1"
    block_id = (await DataEngine.get_setting("adsgram_block_id", "") or "").strip()
    monetag_zone_id = (await DataEngine.get_setting("monetag_zone_id", "") or "").strip()
    if not ads_enabled or not (block_id or monetag_zone_id):
        raise HTTPException(status_code=400, detail="ads_disabled")

    daily_limit      = int(await DataEngine.get_setting("ad_daily_limit", "10"))
    cooldown_seconds = int(await DataEngine.get_setting("ad_cooldown_seconds", "30"))
    reward_amount    = float(await DataEngine.get_setting("ad_reward_amount", "0.5"))

    watched_today = await DataEngine.count_ad_events_today(uid, AD_KIND_VIDEO)
    if watched_today >= daily_limit:
        raise HTTPException(status_code=400, detail="daily_limit_reached")

    last_at = await DataEngine.get_last_ad_event(uid, AD_KIND_VIDEO)
    if last_at:
        try:
            elapsed = (datetime.utcnow() - datetime.strptime(last_at, "%Y-%m-%d %H:%M:%S")).total_seconds()
            if elapsed < cooldown_seconds:
                raise HTTPException(status_code=400, detail="cooldown_active")
        except HTTPException:
            raise
        except Exception:
            pass

    await DataEngine.record_ad_event(uid, AD_KIND_VIDEO, reward_amount)
    await DataEngine.add_balance(uid, reward_amount)
    return {"credited": reward_amount}


@api_app.post("/api/ads/direct-link/open")
async def api_ads_direct_link_open(body: ApiBase):
    """Direct Link has no SDK callback to confirm anything happened, so
    the reward is gated behind a server-timed wait (same trust model as
    the 'fake' task type already used for unverifiable channel joins)."""
    user = await _authenticate(body)
    uid = user["user_id"]

    ads_enabled = (await DataEngine.get_setting("ads_enabled", "0")) == "1"
    direct_link = (await DataEngine.get_setting("adsgram_direct_link", "") or "").strip()
    if not ads_enabled or not direct_link:
        raise HTTPException(status_code=400, detail="direct_link_disabled")

    daily_limit      = int(await DataEngine.get_setting("direct_link_daily_limit", "10"))
    cooldown_seconds = int(await DataEngine.get_setting("direct_link_cooldown_seconds", "30"))
    wait_seconds     = int(await DataEngine.get_setting("direct_link_wait_seconds", "15"))

    watched_today = await DataEngine.count_ad_events_today(uid, AD_KIND_DIRECT)
    if watched_today >= daily_limit:
        raise HTTPException(status_code=400, detail="daily_limit_reached")

    last_at = await DataEngine.get_last_ad_event(uid, AD_KIND_DIRECT)
    if last_at:
        try:
            elapsed = (datetime.utcnow() - datetime.strptime(last_at, "%Y-%m-%d %H:%M:%S")).total_seconds()
            if elapsed < cooldown_seconds:
                raise HTTPException(status_code=400, detail="cooldown_active")
        except HTTPException:
            raise
        except Exception:
            pass

    event_id = await DataEngine.start_ad_event(uid, AD_KIND_DIRECT)
    return {"url": direct_link, "event_id": event_id, "wait_seconds": wait_seconds}


class AdDirectLinkClaimRequest(ApiBase):
    event_id: int


@api_app.post("/api/ads/direct-link/claim")
async def api_ads_direct_link_claim(body: AdDirectLinkClaimRequest):
    user = await _authenticate(body)
    uid = user["user_id"]

    wait_seconds  = int(await DataEngine.get_setting("direct_link_wait_seconds", "15"))
    reward_amount = float(await DataEngine.get_setting("direct_link_reward_amount", "0.3"))

    event = await DataEngine.get_ad_event(body.event_id, uid)
    if not event or event["kind"] != AD_KIND_DIRECT or event["status"] == "completed":
        raise HTTPException(status_code=400, detail="not_claimable")

    try:
        started_dt = datetime.strptime(event["started_at"], "%Y-%m-%d %H:%M:%S")
        elapsed = (datetime.utcnow() - started_dt).total_seconds()
    except Exception:
        elapsed = wait_seconds

    if elapsed < wait_seconds:
        raise HTTPException(status_code=400, detail=f"wait:{int(wait_seconds - elapsed)}")

    await DataEngine.complete_ad_event(body.event_id, reward_amount)
    await DataEngine.add_balance(uid, reward_amount)
    fresh = await DataEngine.get_user(uid)
    return {"credited": reward_amount, "balance": float(fresh["balance"])}


# ── /api/tasks — user-facing task list + join/check/claim ───────────────
async def _build_task_view(user_id: int) -> list:
    tasks = await DataEngine.get_tasks(active_only=True)
    progress = await DataEngine.get_all_task_progress_for_user(user_id)
    out = []
    for row in tasks:
        t = dict(row)
        p = progress.get(t["id"])
        if p is None:
            t["status"] = "none"
        elif p["status"] == "completed":
            t["status"] = "completed"
        else:
            try:
                joined_dt = datetime.strptime(p["joined_at"], "%Y-%m-%d %H:%M:%S")
                elapsed = (datetime.utcnow() - joined_dt).total_seconds()
            except Exception:
                elapsed = TASK_JOIN_WAIT_SECONDS
            wait_left = max(0, int(TASK_JOIN_WAIT_SECONDS - elapsed))
            t["status"] = "waiting" if wait_left > 0 else "claimable"
            t["wait_left"] = wait_left
        out.append(t)
    return out


@api_app.post("/api/tasks")
async def api_tasks(body: ApiBase):
    user = await _authenticate(body)
    return {
        "tasks": await _build_task_view(user["user_id"]),
        "user_task_config": {
            "enabled": (await DataEngine.get_setting("user_task_creation_enabled", "0")) == "1",
            "min_reward": float(await DataEngine.get_setting("user_task_min_reward", "1")),
            "max_reward": float(await DataEngine.get_setting("user_task_max_reward", "20")),
            "min_slots": int(await DataEngine.get_setting("user_task_min_slots", "5")),
            "max_slots": int(await DataEngine.get_setting("user_task_max_slots", "500")),
            "bot_username": BOT_USERNAME,
        },
    }


class TaskActionRequest(ApiBase):
    task_id: int


@api_app.post("/api/tasks/join")
async def api_tasks_join(body: TaskActionRequest):
    user = await _authenticate(body)
    task = await DataEngine.get_task(body.task_id)
    if not task or not task["is_active"]:
        raise HTTPException(status_code=404, detail="task_not_found")
    await DataEngine.mark_task_joined(user["user_id"], body.task_id)
    return {"wait_seconds": TASK_JOIN_WAIT_SECONDS}


@api_app.post("/api/tasks/check")
async def api_tasks_check(body: TaskActionRequest):
    user = await _authenticate(body)
    uid = user["user_id"]
    task = await DataEngine.get_task(body.task_id)
    if not task:
        raise HTTPException(status_code=404, detail="task_not_found")
    prog = await DataEngine.get_task_progress(uid, body.task_id)
    if not prog:
        raise HTTPException(status_code=400, detail="not_joined")
    try:
        joined_dt = datetime.strptime(prog["joined_at"], "%Y-%m-%d %H:%M:%S")
        elapsed = (datetime.utcnow() - joined_dt).total_seconds()
    except Exception:
        elapsed = TASK_JOIN_WAIT_SECONDS
    remaining = int(TASK_JOIN_WAIT_SECONDS - elapsed)
    if remaining > 0:
        raise HTTPException(status_code=400, detail=f"wait:{remaining}")
    if task["task_type"] == "force" and task["channel_id"]:
        try:
            m = await bot.get_chat_member(chat_id=task["channel_id"], user_id=uid)
            if m.status in (ChatMemberStatus.LEFT, ChatMemberStatus.KICKED, ChatMemberStatus.RESTRICTED):
                raise HTTPException(status_code=400, detail="not_member")
        except HTTPException:
            raise
        except Exception:
            # Bot isn't admin there / lookup failed — don't hard-block a
            # legitimate user over a misconfigured channel (same policy
            # as inspect_compulsory_memberships above).
            pass
    # Only reachable once the wait timer has elapsed AND (for a "force"
    # task) real membership has been confirmed above. Record that this
    # user has passed a genuine check — /api/tasks/claim will refuse to
    # pay out without this, so a reward is never handed out for free.
    await DataEngine.mark_task_checked(uid, body.task_id)
    return {"ok": True}


@api_app.post("/api/tasks/claim")
async def api_tasks_claim(body: TaskActionRequest):
    user = await _authenticate(body)
    uid = user["user_id"]
    task = await DataEngine.get_task(body.task_id)
    if not task:
        raise HTTPException(status_code=404, detail="task_not_found")
    prog = await DataEngine.get_task_progress(uid, body.task_id)
    if not prog or prog["status"] == "completed":
        raise HTTPException(status_code=400, detail="not_claimable")
    if prog["status"] != "checked":
        # Guards against calling /api/tasks/claim directly (skipping
        # /api/tasks/check) to collect a reward without ever actually
        # joining / passing verification.
        raise HTTPException(status_code=400, detail="not_checked")
    await DataEngine.mark_task_completed(uid, body.task_id)
    await DataEngine.add_balance(uid, float(task["reward"]))
    # If this is a user-created (escrow-funded) task, count the slot the
    # creator already paid for at creation time — the reward above came
    # from that escrow, not from a fresh mint of balance.
    if task["created_by"]:
        sold_out = await DataEngine.increment_task_slot(body.task_id)
        if sold_out:
            try:
                await bot.send_message(
                    task["created_by"],
                    f"🎯 Your task \"{task['title']}\" has reached its target — "
                    f"all {task['budget_slots']} people have joined. It's now removed from the task list."
                )
            except Exception:
                pass
    fresh = await DataEngine.get_user(uid)
    return {"status": "completed", "reward": float(task["reward"]), "balance": float(fresh["balance"])}


# ── /api/tasks/create — users pay from their own balance to advertise
#    their own channel as a task other users can complete ─────────────────
class UserTaskCreateRequest(ApiBase):
    title: str
    invite_link: str
    reward: float = Field(gt=0)
    budget_slots: int = Field(gt=0)
    channel_id: str = ""  # if set, we re-verify bot-admin status server-side


# ── /api/tasks/verify_admin — step 1 of self-serve task creation: confirm
#    the bot has actually been made admin in the user's channel before
#    letting them create a real ("force") verified task ───────────────────
class VerifyAdminRequest(ApiBase):
    channel_id: str


@api_app.post("/api/tasks/verify_admin")
async def api_tasks_verify_admin(body: VerifyAdminRequest):
    await _authenticate(body)
    channel_id = body.channel_id.strip()
    if not channel_id:
        raise HTTPException(status_code=400, detail="missing_channel")
    bot_id = BOT_ID
    if not bot_id:
        try:
            bot_id = (await bot.get_me()).id
        except Exception:
            raise HTTPException(status_code=503, detail="bot_unavailable")
    try:
        member = await bot.get_chat_member(chat_id=channel_id, user_id=bot_id)
        is_admin = member.status in ("administrator", "creator")
    except Exception:
        # Channel not found, bot not in it at all, wrong ID format, etc.
        is_admin = False
    # Best-effort — works for any public channel regardless of admin
    # status, so the user never has to type the channel name themselves.
    title = None
    try:
        chat = await bot.get_chat(chat_id=channel_id)
        title = (chat.title or "").strip() or None
    except Exception:
        pass
    return {"is_admin": is_admin, "bot_username": BOT_USERNAME, "title": title}


@api_app.post("/api/tasks/create")
async def api_tasks_create(body: UserTaskCreateRequest):
    user = await _authenticate(body)
    uid = user["user_id"]

    if (await DataEngine.get_setting("user_task_creation_enabled", "0")) != "1":
        raise HTTPException(status_code=400, detail="feature_disabled")

    title = body.title.strip()[:80]
    link = body.invite_link.strip()
    channel_id = body.channel_id.strip()
    if not title or not link:
        raise HTTPException(status_code=400, detail="missing_fields")
    if not link.lower().startswith(("https://t.me/", "http://t.me/", "tg://")):
        raise HTTPException(status_code=400, detail="invalid_link")

    min_reward = float(await DataEngine.get_setting("user_task_min_reward", "1"))
    max_reward = float(await DataEngine.get_setting("user_task_max_reward", "20"))
    min_slots  = int(await DataEngine.get_setting("user_task_min_slots", "5"))
    max_slots  = int(await DataEngine.get_setting("user_task_max_slots", "500"))
    if not (min_reward <= body.reward <= max_reward):
        raise HTTPException(status_code=400, detail="reward_out_of_range")
    if not (min_slots <= body.budget_slots <= max_slots):
        raise HTTPException(status_code=400, detail="slots_out_of_range")

    total_cost = round(body.reward * body.budget_slots, 2)
    fresh = await DataEngine.get_user(uid)
    if not fresh or float(fresh["balance"]) < total_cost:
        raise HTTPException(status_code=400, detail="insufficient_balance")

    # Re-verify bot-admin status ourselves — never trust the client's word
    # for whether the "Check" step passed. If it checks out, this becomes
    # a real "force" task (genuine membership check on every join);
    # otherwise it falls back to "fake" (wait-timer only), same as any
    # admin-made task for a channel the bot isn't in.
    task_type = "fake"
    if channel_id:
        bot_id = BOT_ID or (await bot.get_me()).id
        try:
            member = await bot.get_chat_member(chat_id=channel_id, user_id=bot_id)
            if member.status in ("administrator", "creator"):
                task_type = "force"
        except Exception:
            pass
    if task_type != "force":
        channel_id = ""

    # Escrow the full budget immediately — this is what lets us pay each
    # completer out of the same pool later without minting new balance.
    await DataEngine.add_balance(uid, -total_cost)
    task_id = await DataEngine.create_task(
        title, channel_id, link, task_type, body.reward,
        created_by=uid, budget_slots=body.budget_slots, review_status="pending",
    )
    return {"ok": True, "task_id": task_id, "total_cost": total_cost, "status": "pending_review", "task_type": task_type}


@api_app.post("/api/tasks/mine")
async def api_tasks_mine(body: ApiBase):
    user = await _authenticate(body)
    rows = await DataEngine.get_user_tasks(user["user_id"])
    return {"tasks": [dict(r) for r in rows]}


@api_app.post("/api/tasks/cancel")
async def api_tasks_cancel(body: TaskActionRequest):
    """
    Lets a creator pull their own task early and get back the escrow for
    whatever slots haven't been used yet. Can't touch anyone else's task.
    """
    user = await _authenticate(body)
    uid = user["user_id"]
    task = await DataEngine.get_task(body.task_id)
    if not task or task["created_by"] != uid:
        raise HTTPException(status_code=404, detail="task_not_found")
    if task["review_status"] not in ("pending", "approved"):
        raise HTTPException(status_code=400, detail="nothing_to_cancel")
    unused_slots = max(0, int(task["budget_slots"]) - int(task["slots_used"]))
    if unused_slots == 0:
        raise HTTPException(status_code=400, detail="nothing_to_cancel")
    refund = round(unused_slots * float(task["reward"]), 2)
    if refund > 0:
        await DataEngine.add_balance(uid, refund)
    await DataEngine.update_task(body.task_id, is_active=0, review_status="cancelled")
    return {"ok": True, "refunded": refund}


# ── /api/withdraw ─────────────────────────────────────────────────────────
class WithdrawRequest(ApiBase):
    amount: float = Field(gt=0)
    phone: str
    full_name: str


@api_app.post("/api/withdraw")
async def api_withdraw(body: WithdrawRequest):
    user = await _authenticate(body)
    min_w = float(await DataEngine.get_setting("min_withdrawal", "50"))
    if body.amount < min_w:
        raise HTTPException(status_code=400, detail=f"min_withdrawal_is_{min_w:.2f}")
    result = await dispatch_withdrawal_core(
        user["user_id"], body.amount, body.full_name.strip(), body.phone.strip()
    )
    if result["status"] == "error":
        raise HTTPException(status_code=400, detail=result["reason"])
    return result


@api_app.post("/api/withdraw/history")
async def api_withdraw_history(body: ApiBase):
    user = await _authenticate(body)
    rows = await DataEngine.get_user_withdrawals(user["user_id"])
    return {"withdrawals": [dict(r) for r in rows]}


# ── /api/admin/stats/overview — total & online users ─────────────────────
@api_app.post("/api/admin/stats/overview")
async def api_admin_stats_overview(body: ApiBase):
    user = await _authenticate(body)
    _require_admin(user)
    total, online = await DataEngine.get_user_activity_stats()
    return {"total_users": total, "online_users": online}


# ── /api/admin/ads/analytics — clicks vs completions + daily-limit list ──
@api_app.post("/api/admin/ads/analytics")
async def api_admin_ads_analytics(body: ApiBase):
    user = await _authenticate(body)
    _require_admin(user)
    video_daily_limit = int(await DataEngine.get_setting("ad_daily_limit", "10"))
    dl_daily_limit     = int(await DataEngine.get_setting("direct_link_daily_limit", "10"))
    return await DataEngine.get_ads_admin_analytics(video_daily_limit, dl_daily_limit)


# ── /api/admin/tasks/review — approve/reject user-submitted (escrowed)
#    tasks before they go live to other users ───────────────────────────
@api_app.post("/api/admin/tasks/pending")
async def api_admin_tasks_pending(body: ApiBase):
    user = await _authenticate(body)
    _require_admin(user)
    rows = await DataEngine.get_pending_review_tasks()
    return {"tasks": [dict(r) for r in rows]}


class AdminTaskReviewRequest(ApiBase):
    id: int
    approve: bool


@api_app.post("/api/admin/tasks/review")
async def api_admin_tasks_review(body: AdminTaskReviewRequest):
    user = await _authenticate(body)
    _require_admin(user)
    task = await DataEngine.get_task(body.id)
    if not task or task["review_status"] != "pending":
        raise HTTPException(status_code=404, detail="task_not_found")
    if body.approve:
        await DataEngine.update_task(body.id, review_status="approved", is_active=1)
        note = "✅ Your task has been approved and is now live!"
    else:
        # Full refund — none of the escrowed slots were ever usable.
        refund = round(float(task["budget_slots"]) * float(task["reward"]), 2)
        if refund > 0 and task["created_by"]:
            await DataEngine.add_balance(task["created_by"], refund)
        await DataEngine.update_task(body.id, review_status="rejected", is_active=0)
        note = f"❌ Your submitted task was rejected. {refund:.2f} Birr has been refunded to your balance."
    if task["created_by"]:
        try:
            await bot.send_message(task["created_by"], note)
        except Exception:
            pass
    return {"ok": True}


# ── /api/admin/tasks/list ────────────────────────────────────────────────
@api_app.post("/api/admin/tasks/list")
async def api_admin_tasks_list(body: ApiBase):
    user = await _authenticate(body)
    _require_admin(user)
    tasks = await DataEngine.get_tasks(active_only=False)
    return {"tasks": [dict(t) for t in tasks]}


class AdminTaskCreateRequest(ApiBase):
    title: str
    task_type: str = "fake"
    channel_id: str = ""
    invite_link: str = ""
    reward: float = 0


@api_app.post("/api/admin/tasks/create")
async def api_admin_tasks_create(body: AdminTaskCreateRequest):
    user = await _authenticate(body)
    _require_admin(user)
    if not body.title.strip():
        raise HTTPException(status_code=400, detail="title_required")
    task_id = await DataEngine.create_task(
        body.title.strip(), body.channel_id.strip(), body.invite_link.strip(),
        body.task_type, body.reward,
    )
    return {"ok": True, "task_id": task_id}


class AdminIdRequest(ApiBase):
    id: int


@api_app.post("/api/admin/tasks/delete")
async def api_admin_tasks_delete(body: AdminIdRequest):
    user = await _authenticate(body)
    _require_admin(user)
    await DataEngine.delete_task(body.id)
    return {"ok": True}


class AdminTaskUpdateRequest(ApiBase):
    id: int
    is_active: int


@api_app.post("/api/admin/tasks/update")
async def api_admin_tasks_update(body: AdminTaskUpdateRequest):
    user = await _authenticate(body)
    _require_admin(user)
    await DataEngine.update_task(body.id, is_active=body.is_active)
    return {"ok": True}


class AdminTaskReorderRequest(ApiBase):
    order: List[int]


@api_app.post("/api/admin/tasks/reorder")
async def api_admin_tasks_reorder(body: AdminTaskReorderRequest):
    user = await _authenticate(body)
    _require_admin(user)
    await DataEngine.reorder_tasks(body.order)
    return {"ok": True}


# NEW FEATURE: after adding a task, the admin panel offers "Broadcast this
# new task to all users?" — this endpoint sends that announcement with an
# inline "Open App" button (a Telegram WebApp button) so users can jump
# straight into the Mini App and do the task.
class AdminTaskBroadcastRequest(ApiBase):
    task_id: int


@api_app.post("/api/admin/tasks/broadcast")
async def api_admin_tasks_broadcast(body: AdminTaskBroadcastRequest):
    user = await _authenticate(body)
    _require_admin(user)
    task = await DataEngine.get_task(body.task_id)
    if not task:
        raise HTTPException(status_code=404, detail="task_not_found")
    text = (
        f"🆕 <b>አዲስ ታስክ አለ! / New Task Available!</b>\n\n"
        f"📢 {sanitize_html(task['title'])}\n"
        f"💰 Reward: <b>{float(task['reward']):.2f} Birr</b>\n\n"
        f"👇 ገብታችሁ ስሩ! / Open the app and complete it now."
    )
    markup = InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(
            text="🚀 Open App / አፑን ክፈት",
            web_app=WebAppInfo(url=f"{FRONTEND_URL}/app.html"),
        )
    ]])
    sent, failed = await broadcast_to_all_users(text, markup)
    return {"ok": True, "sent": sent, "failed": failed}


# ── /api/admin/channels/* — force/fake gate channels ─────────────────────
@api_app.post("/api/admin/channels/list")
async def api_admin_channels_list(body: ApiBase):
    user = await _authenticate(body)
    _require_admin(user)
    channels = await DataEngine.get_force_channels()
    return {"channels": [dict(c) for c in channels]}


class AdminChannelCreateRequest(ApiBase):
    bot_added: int
    channel_id: str = ""
    channel_name: str
    invite_link: str


@api_app.post("/api/admin/channels/create")
async def api_admin_channels_create(body: AdminChannelCreateRequest):
    user = await _authenticate(body)
    _require_admin(user)
    if not body.channel_name.strip() or not body.invite_link.strip():
        raise HTTPException(status_code=400, detail="name_and_link_required")
    await DataEngine.add_force_channel(
        body.channel_id.strip(), body.channel_name.strip(), body.invite_link.strip(), body.bot_added
    )
    return {"ok": True}


@api_app.post("/api/admin/channels/delete")
async def api_admin_channels_delete(body: AdminIdRequest):
    user = await _authenticate(body)
    _require_admin(user)
    await DataEngine.remove_force_channel(body.id)
    return {"ok": True}


# ── /api/admin/withdrawals/* ──────────────────────────────────────────────
@api_app.post("/api/admin/withdrawals/list")
async def api_admin_withdrawals_list(body: ApiBase):
    user = await _authenticate(body)
    _require_admin(user)
    rows = await DataEngine.get_pending_withdrawals()
    return {"withdrawals": [dict(r) for r in rows]}


class AdminWithdrawalApproveRequest(ApiBase):
    id: int
    notify_mode: str = "both"  # "both" | "channel_only"


@api_app.post("/api/admin/withdrawals/approve")
async def api_admin_withdrawals_approve(body: AdminWithdrawalApproveRequest):
    user = await _authenticate(body)
    _require_admin(user)
    mode = body.notify_mode if body.notify_mode in ("both", "channel_only") else "both"
    result = await approve_withdrawal_core(body.id, notify_mode=mode)
    if not result["ok"]:
        raise HTTPException(status_code=400, detail=result["reason"])
    return {"ok": True}


class AdminWithdrawalRejectRequest(ApiBase):
    id: int
    reason: str = "No reason given."


@api_app.post("/api/admin/withdrawals/reject")
async def api_admin_withdrawals_reject(body: AdminWithdrawalRejectRequest):
    user = await _authenticate(body)
    _require_admin(user)
    ticket = await DataEngine.get_withdrawal(body.id)
    if not ticket or ticket["status"] != "pending":
        raise HTTPException(status_code=400, detail="already_processed")
    await execute_withdrawal_rejection(None, body.id, ticket, body.reason)
    return {"ok": True}


# ── /api/admin/users/* ────────────────────────────────────────────────────
class AdminUserIdRequest(ApiBase):
    user_id: int


@api_app.post("/api/admin/users/search")
async def api_admin_users_search(body: AdminUserIdRequest):
    user = await _authenticate(body)
    _require_admin(user)
    target = await DataEngine.get_user(body.user_id)
    if not target:
        raise HTTPException(status_code=404, detail="not_found")
    direct, _ = await DataEngine.get_referral_metrics(body.user_id)
    return {
        "user_id": target["user_id"],
        "username": target["username"],
        "full_name": target["full_name"],
        "balance": float(target["balance"]),
        "referrals": direct,
        "is_banned": bool(target["is_banned"]),
    }


class AdminUserBanRequest(ApiBase):
    user_id: int
    banned: int


@api_app.post("/api/admin/users/ban")
async def api_admin_users_ban(body: AdminUserBanRequest):
    user = await _authenticate(body)
    _require_admin(user)
    await DataEngine.ban_user(body.user_id, body.banned)
    return {"ok": True}


class AdminUserBalanceRequest(ApiBase):
    user_id: int
    amount: float


@api_app.post("/api/admin/users/balance")
async def api_admin_users_balance(body: AdminUserBalanceRequest):
    user = await _authenticate(body)
    _require_admin(user)
    await DataEngine.add_balance(body.user_id, body.amount)
    return {"ok": True}


# ── /api/admin/settings ───────────────────────────────────────────────────
@api_app.post("/api/admin/settings")
async def api_admin_settings(body: ApiBase):
    user = await _authenticate(body)
    _require_admin(user)
    rate = await DataEngine.get_setting("reward_per_referral", "10")
    min_w = await DataEngine.get_setting("min_withdrawal", "50")
    return {
        "reward_per_referral": float(rate),
        "min_withdrawal": float(min_w),
        # AdsGram — rewarded video
        "ads_enabled": (await DataEngine.get_setting("ads_enabled", "0")) == "1",
        "adsgram_block_id": await DataEngine.get_setting("adsgram_block_id", "") or "",
        "ad_reward_amount": float(await DataEngine.get_setting("ad_reward_amount", "0.5")),
        "ad_daily_limit": int(await DataEngine.get_setting("ad_daily_limit", "10")),
        "ad_cooldown_seconds": int(await DataEngine.get_setting("ad_cooldown_seconds", "30")),
        # AdsGram — Direct Link
        "adsgram_direct_link": await DataEngine.get_setting("adsgram_direct_link", "") or "",
        "direct_link_reward_amount": float(await DataEngine.get_setting("direct_link_reward_amount", "0.3")),
        "direct_link_daily_limit": int(await DataEngine.get_setting("direct_link_daily_limit", "10")),
        "direct_link_wait_seconds": int(await DataEngine.get_setting("direct_link_wait_seconds", "15")),
        "direct_link_cooldown_seconds": int(await DataEngine.get_setting("direct_link_cooldown_seconds", "30")),
        # Monetag — fallback rewarded network when AdsGram has no fill
        "monetag_zone_id": await DataEngine.get_setting("monetag_zone_id", "") or "",
        "monetag_sdk_url": await DataEngine.get_setting("monetag_sdk_url", "") or "",
        # Referral skip — silently withhold payment for some referrals
        "referral_skip_enabled": (await DataEngine.get_setting("referral_skip_enabled", "0")) == "1",
        "referral_skip_batch_size": int(await DataEngine.get_setting("referral_skip_batch_size", "6")),
        "referral_skip_min": int(await DataEngine.get_setting("referral_skip_min", "1")),
        "referral_skip_max": int(await DataEngine.get_setting("referral_skip_max", "3")),
        # User self-serve task creation (users advertise their own channel,
        # paid from their own balance)
        "user_task_creation_enabled": (await DataEngine.get_setting("user_task_creation_enabled", "0")) == "1",
        "user_task_min_reward": float(await DataEngine.get_setting("user_task_min_reward", "1")),
        "user_task_max_reward": float(await DataEngine.get_setting("user_task_max_reward", "20")),
        "user_task_min_slots": int(await DataEngine.get_setting("user_task_min_slots", "5")),
        "user_task_max_slots": int(await DataEngine.get_setting("user_task_max_slots", "500")),
        # Support contact — shown as a floating support button in the dashboard
        "support_username": (await DataEngine.get_setting("support_username", "") or "").lstrip("@"),
    }


class AdminSettingsUpdateRequest(ApiBase):
    reward_per_referral: float
    min_withdrawal: float
    ads_enabled: bool = False
    adsgram_block_id: str = ""
    ad_reward_amount: float = 0.5
    ad_daily_limit: int = 10
    ad_cooldown_seconds: int = 30
    adsgram_direct_link: str = ""
    direct_link_reward_amount: float = 0.3
    direct_link_daily_limit: int = 10
    direct_link_wait_seconds: int = 15
    direct_link_cooldown_seconds: int = 30
    monetag_zone_id: str = ""
    monetag_sdk_url: str = ""
    referral_skip_enabled: bool = False
    referral_skip_batch_size: int = 6
    referral_skip_min: int = 1
    referral_skip_max: int = 3
    user_task_creation_enabled: bool = False
    user_task_min_reward: float = 1
    user_task_max_reward: float = 20
    user_task_min_slots: int = 5
    user_task_max_slots: int = 500
    support_username: str = ""


@api_app.post("/api/admin/settings/update")
async def api_admin_settings_update(body: AdminSettingsUpdateRequest):
    user = await _authenticate(body)
    _require_admin(user)
    await DataEngine.set_setting("reward_per_referral", str(body.reward_per_referral))
    await DataEngine.set_setting("min_withdrawal", str(body.min_withdrawal))
    await DataEngine.set_setting("ads_enabled", "1" if body.ads_enabled else "0")
    await DataEngine.set_setting("adsgram_block_id", body.adsgram_block_id.strip())
    await DataEngine.set_setting("ad_reward_amount", str(body.ad_reward_amount))
    await DataEngine.set_setting("ad_daily_limit", str(body.ad_daily_limit))
    await DataEngine.set_setting("ad_cooldown_seconds", str(body.ad_cooldown_seconds))
    await DataEngine.set_setting("adsgram_direct_link", body.adsgram_direct_link.strip())
    await DataEngine.set_setting("direct_link_reward_amount", str(body.direct_link_reward_amount))
    await DataEngine.set_setting("direct_link_daily_limit", str(body.direct_link_daily_limit))
    await DataEngine.set_setting("direct_link_wait_seconds", str(body.direct_link_wait_seconds))
    await DataEngine.set_setting("direct_link_cooldown_seconds", str(body.direct_link_cooldown_seconds))
    await DataEngine.set_setting("monetag_zone_id", body.monetag_zone_id.strip())
    await DataEngine.set_setting("monetag_sdk_url", body.monetag_sdk_url.strip())
    await DataEngine.set_setting("referral_skip_enabled", "1" if body.referral_skip_enabled else "0")
    await DataEngine.set_setting("referral_skip_batch_size", str(max(2, body.referral_skip_batch_size)))
    await DataEngine.set_setting("referral_skip_min", str(max(0, body.referral_skip_min)))
    await DataEngine.set_setting("referral_skip_max", str(max(body.referral_skip_min, body.referral_skip_max)))
    await DataEngine.set_setting("user_task_creation_enabled", "1" if body.user_task_creation_enabled else "0")
    await DataEngine.set_setting("user_task_min_reward", str(body.user_task_min_reward))
    await DataEngine.set_setting("user_task_max_reward", str(body.user_task_max_reward))
    await DataEngine.set_setting("user_task_min_slots", str(body.user_task_min_slots))
    await DataEngine.set_setting("user_task_max_slots", str(body.user_task_max_slots))
    await DataEngine.set_setting("support_username", body.support_username.strip().lstrip("@"))
    return {"ok": True}


# ── /api/admin/ads/verify — connection check shown in the dashboard ─────
@api_app.post("/api/admin/ads/verify")
async def api_admin_ads_verify(body: ApiBase):
    user = await _authenticate(body)
    _require_admin(user)
    block_id     = (await DataEngine.get_setting("adsgram_block_id", "") or "").strip()
    direct_link  = (await DataEngine.get_setting("adsgram_direct_link", "") or "").strip()
    monetag_zone = (await DataEngine.get_setting("monetag_zone_id", "") or "").strip()
    monetag_url  = (await DataEngine.get_setting("monetag_sdk_url", "") or "").strip()
    ads_enabled  = (await DataEngine.get_setting("ads_enabled", "0")) == "1"
    video_ready  = ads_enabled and bool(block_id)
    link_ready   = ads_enabled and direct_link.lower().startswith(("http://", "https://"))
    monetag_ready = ads_enabled and bool(monetag_zone) and monetag_url.lower().startswith(("http://", "https://"))
    return {
        "sdk_script_present": True,  # sad.min.js is loaded in frontend/app.html <head>
        "ads_enabled": ads_enabled,
        "block_id_configured": bool(block_id),
        "direct_link_configured": bool(direct_link),
        "direct_link_valid_url": link_ready,
        "video_ready": video_ready,
        "direct_link_ready": link_ready,
        "monetag_configured": bool(monetag_zone) and bool(monetag_url),
        "monetag_ready": monetag_ready,
    }


# ── /api/admin/broadcast — free-text announcement to all users ──────────
class AdminBroadcastRequest(ApiBase):
    text: str


@api_app.post("/api/admin/broadcast")
async def api_admin_broadcast(body: AdminBroadcastRequest):
    user = await _authenticate(body)
    _require_admin(user)
    if not body.text.strip():
        raise HTTPException(status_code=400, detail="text_required")
    sent, failed = await broadcast_to_all_users(body.text.strip())
    return {"sent": sent, "failed": failed}


# ═════════════════════════════════════════════════════════════════════════
# DATABASE BACKUPS — periodically ships a copy of the SQLite file to a
# private Telegram channel (only you should be a member of it). This is
# a safety net in case the Railway Volume itself is ever lost/corrupted;
# it does NOT replace the Volume, it's a second, independent copy.
# ═════════════════════════════════════════════════════════════════════════
async def send_db_backup():
    if not DB_BACKUP_CHANNEL_ID:
        return
    if not os.path.exists(DB_PATH):
        logger.warning(f"DB backup skipped — {DB_PATH} does not exist yet")
        return
    try:
        stamp = datetime.utcnow().strftime("%Y-%m-%d_%H-%M-UTC")
        await bot.send_document(
            chat_id=DB_BACKUP_CHANNEL_ID,
            document=FSInputFile(DB_PATH, filename=f"referral_bot_{stamp}.db"),
            caption=f"🗄 Automatic DB backup — {stamp}",
        )
        logger.info(f"DB backup sent to {DB_BACKUP_CHANNEL_ID}")
    except Exception as e:
        logger.warning(f"DB backup failed: {e}")


async def db_backup_loop():
    # Send one right away at startup so there's always a fresh copy, then
    # repeat on the configured interval for as long as the process runs.
    await send_db_backup()
    while True:
        await asyncio.sleep(DB_BACKUP_INTERVAL_HOURS * 3600)
        await send_db_backup()


# ═════════════════════════════════════════════════════════════════════════
# ENTRYPOINT — runs the Telegram long-poller AND the Mini App web server
# in the same process (this is what Railway's "web: python bot.py" and
# healthcheckPath "/health" in railway.toml expect).
# ═════════════════════════════════════════════════════════════════════════
async def _run_web_server():
    port = int(os.getenv("PORT", "8000"))
    config = uvicorn.Config(api_app, host="0.0.0.0", port=port, log_level="info")
    server = uvicorn.Server(config)
    await server.serve()


async def _main():
    global _polling_task, BOT_USERNAME, BOT_ID
    await DataEngine.init_database()
    try:
        me = await bot.get_me()
        BOT_USERNAME = me.username
        BOT_ID = me.id
    except Exception as e:
        logger.warning(f"Could not fetch bot identity at startup: {e}")
    # Pre-warm the invite-card photo cache so the very first time someone
    # taps "Share with Friends", Telegram's inline query gets answered
    # instantly instead of waiting on a first-time get_user_profile_photos
    # round-trip (which is what made it feel like a slow "search").
    try:
        await _get_bot_photo_file_id()
    except Exception as e:
        logger.warning(f"Could not pre-cache bot photo at startup: {e}")
    _polling_task = asyncio.create_task(dp.start_polling(bot, skip_updates=True))
    asyncio.create_task(db_backup_loop())
    await _run_web_server()


if __name__ == "__main__":
    asyncio.run(_main())
