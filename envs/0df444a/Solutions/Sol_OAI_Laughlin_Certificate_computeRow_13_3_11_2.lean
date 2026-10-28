-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_3_11_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:10:34.478986+00:00
-- url     : https://prove2.me/submissions/8106a104-0b37-485a-95cc-1299c34ecdaf

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 3 11 (RowCompute.rows[2]!) =
    (75551441615707971851324110196079600656095357256790441984000000 : ℤ) := by
  decide +kernel
