-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_5_5_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:29:37.417985+00:00
-- url     : https://prove2.me/submissions/c4f72dae-711d-4611-938a-76e769291f92

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 12 5 5 (RowCompute.rows[0]!) =
    (-13568434452006916540742187907680340013022718377477537792000000 : ℤ) := by
  decide +kernel
