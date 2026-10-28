-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_3_7_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:29:33.388417+00:00
-- url     : https://prove2.me/submissions/9b3d375d-3eae-4d2b-a45d-e734307ae94b

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 3 7 (RowCompute.rows[3]!) =
    (199164110635515111865433575652511850033138185278091952128000000 : ℤ) := by
  decide +kernel
