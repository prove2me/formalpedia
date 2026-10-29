-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_3_5_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:45:22.172979+00:00
-- url     : https://prove2.me/submissions/bf5db2f5-39be-4c22-b08b-effa7866ae93

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 3 5 (RowCompute.rows[5]!) =
    (342819835894285529676551328952073071407084694102811344896000000 : ℤ) := by
  decide +kernel
