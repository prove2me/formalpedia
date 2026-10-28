-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_1_3_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:31:38.574747+00:00
-- url     : https://prove2.me/submissions/611be93e-e26c-4fc4-b61f-219b2cbabcb7

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 1 3 (RowCompute.rows[4]!) =
    (-24008230324336158937040680586644171361887125491417088000000 : ℤ) := by
  decide +kernel
