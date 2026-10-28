-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_1_5_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:10:44.320756+00:00
-- url     : https://prove2.me/submissions/2f1ab679-c4c8-4121-af22-03050fef56bb

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 10 1 5 (RowCompute.rows[5]!) =
    (-764070925347254403766892822473297727764870101083357184000000 : ℤ) := by
  decide +kernel
