-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_3_7_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:39:00.70769+00:00
-- url     : https://prove2.me/submissions/21624fef-9fc2-4fe5-8cc7-4ff20a76cc82

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 3 7 (RowCompute.rows[1]!) =
    (-1324224026741703645060512031285041186432931824658284544000000 : ℤ) := by
  decide +kernel
