-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_5_13_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:37:28.407514+00:00
-- url     : https://prove2.me/submissions/c03898d2-4b1b-4e47-bd32-97bb58ab4cc7

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 5 13 (RowCompute.rows[6]!) =
    (-73112653546748883929277972781056731696695570804884111360000000 : ℤ) := by
  decide +kernel
