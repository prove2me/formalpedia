-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_5_5_5_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:04:49.469495+00:00
-- url     : https://prove2.me/submissions/88e6f838-2268-4c25-ac15-314f39e11496

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 5 5 5 (rows[5]!) = (52813174350218993123795 / 536870912 : ℚ) := by
  decide +kernel
