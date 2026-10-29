-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_1_9_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:38:47.713005+00:00
-- url     : https://prove2.me/submissions/fe29e025-027d-4b0f-8b52-ee89742d8621

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 1 9 (RowCompute.rows[1]!) =
    (-2375093103361440978102279858156459536128585833352947302400000 : ℤ) := by
  decide +kernel
