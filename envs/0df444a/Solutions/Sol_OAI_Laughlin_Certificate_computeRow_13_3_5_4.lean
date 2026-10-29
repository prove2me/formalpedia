-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_3_5_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:36:37.989623+00:00
-- url     : https://prove2.me/submissions/30a06cda-f18c-4930-84a5-6fcf1d2fcf64

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 3 5 (RowCompute.rows[4]!) =
    (10741856964736505549976357468701971434225727836971335680000000 : ℤ) := by
  decide +kernel
