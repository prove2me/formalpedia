-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_8_1_5_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:03:46.935226+00:00
-- url     : https://prove2.me/submissions/8ea3671b-c9e5-4018-8fc4-9e2d162d7e4d

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 8 1 5 (rows[5]!) = (-142185036639416818007445/67108864 : ℚ) := by
  decide +kernel
