-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_1_1_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:36:31.777104+00:00
-- url     : https://prove2.me/submissions/e8e9f9f6-cf6b-4500-b907-c382782ee59c

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 1 1 (RowCompute.rows[5]!) =
    (-21822395859574217546334128359210981370505963421427237388288000000 : ℤ) := by
  decide +kernel
