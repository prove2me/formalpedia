-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_1_11_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:47:26.101903+00:00
-- url     : https://prove2.me/submissions/e3cd6da2-79cb-44d6-9f79-40ccaacd7cff

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 1 11 (RowCompute.rows[5]!) =
    (8275201226506829119811152193871192711051407817091911254016000000 : ℤ) := by
  decide +kernel
