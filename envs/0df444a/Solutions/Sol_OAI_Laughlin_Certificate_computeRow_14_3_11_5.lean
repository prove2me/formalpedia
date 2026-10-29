-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_3_11_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:49:31.99847+00:00
-- url     : https://prove2.me/submissions/ab57b5e5-283d-45d9-a7c8-00cae7304208

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 3 11 (RowCompute.rows[5]!) =
    (-853784726122647710769494342146742476401064144281695944704000000 : ℤ) := by
  decide +kernel
