-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_5_7_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:38:59.328783+00:00
-- url     : https://prove2.me/submissions/9cc93cc2-3baa-40ec-bf35-c75568be47bd

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 5 7 (RowCompute.rows[5]!) =
    (-111017439547267587426933018059501024931009412890378633216000000 : ℤ) := by
  decide +kernel
