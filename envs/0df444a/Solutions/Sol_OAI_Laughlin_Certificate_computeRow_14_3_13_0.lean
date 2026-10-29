-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_3_13_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:47:18.491893+00:00
-- url     : https://prove2.me/submissions/e1d667b1-deb1-4e65-8067-cdfa3ef70bba

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 3 13 (RowCompute.rows[0]!) =
    (26773762481119412847969250846507533062566674867647793856512000000 : ℤ) := by
  decide +kernel
