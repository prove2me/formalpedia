-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_1_1_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:25:04.086459+00:00
-- url     : https://prove2.me/submissions/19b38e53-08db-414c-8dd3-08a038bbf4bc

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 1 1 (RowCompute.rows[3]!) =
    (-178569705950189023800978740278409703429516656059927756800000 : ℤ) := by
  decide +kernel
