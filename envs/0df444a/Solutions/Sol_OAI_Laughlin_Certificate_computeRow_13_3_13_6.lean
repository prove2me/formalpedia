-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_3_13_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:31:53.13398+00:00
-- url     : https://prove2.me/submissions/003f0f1f-176d-4b94-87a8-cd4ed87486df

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 3 13 (RowCompute.rows[6]!) =
    (38626171510338484908104843027762789432314881506984067072000000 : ℤ) := by
  decide +kernel
