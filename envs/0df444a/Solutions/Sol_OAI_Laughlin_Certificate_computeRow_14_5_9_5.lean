-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_5_9_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:25:00.286085+00:00
-- url     : https://prove2.me/submissions/05061eb4-3ac1-4d7f-93bc-1f908a68a6d0

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 5 9 (RowCompute.rows[5]!) =
    (177830384916223292069033552265968236933623164212806156288000000 : ℤ) := by
  decide +kernel
