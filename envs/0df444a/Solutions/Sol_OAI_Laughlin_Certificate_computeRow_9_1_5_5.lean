-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_1_5_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:38:57.698581+00:00
-- url     : https://prove2.me/submissions/23815d5a-ccea-4c68-bbbf-1e22762b6573

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 1 5 (RowCompute.rows[5]!) =
    (46576080143532248793028769123169977841188974384014950400000 : ℤ) := by
  decide +kernel
