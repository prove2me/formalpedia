-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_5_5_3_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:04:52.058751+00:00
-- url     : https://prove2.me/submissions/4c0dff64-1b6e-4e40-86c3-c68d9aa5382d

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 5 5 3 (rows[6]!) = (-125595578390684976075 / 67108864 : ℚ) := by
  decide +kernel
