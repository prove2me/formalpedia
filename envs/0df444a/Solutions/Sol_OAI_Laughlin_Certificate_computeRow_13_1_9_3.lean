-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_1_9_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:10:37.489093+00:00
-- url     : https://prove2.me/submissions/84013ea7-44b1-4792-84f1-d7e93e542428

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 1 9 (RowCompute.rows[3]!) =
    (65535227709101341296668377014445535166805862340372725760000000 : ℤ) := by
  decide +kernel
