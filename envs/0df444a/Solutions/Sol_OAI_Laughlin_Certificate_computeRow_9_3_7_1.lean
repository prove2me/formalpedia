-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_3_7_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:48:26.96873+00:00
-- url     : https://prove2.me/submissions/195c2c77-0602-48b3-82ea-7e819095c920

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 3 7 (RowCompute.rows[1]!) =
    (-145292468838310563823610451380445022754954445292830720000 : ℤ) := by
  decide +kernel
