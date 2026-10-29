-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_1_7_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:39:55.270422+00:00
-- url     : https://prove2.me/submissions/f7382901-0cea-4790-9022-d429c2ecc4d2

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 1 7 (RowCompute.rows[0]!) =
    (-1453486210601879109700488090932264990808967063699395182592000000 : ℤ) := by
  decide +kernel
