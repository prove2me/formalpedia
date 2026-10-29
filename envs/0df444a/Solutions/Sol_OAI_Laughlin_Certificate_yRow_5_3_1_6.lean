-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_3_1_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:05:38.525351+00:00
-- url     : https://prove2.me/submissions/d2d97437-5254-4f0a-82b4-d2f3570fa367

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 5 3 1 (rows[6]!) = (-26195139147988314471 / 8388608 : ℚ) := by
  decide +kernel
