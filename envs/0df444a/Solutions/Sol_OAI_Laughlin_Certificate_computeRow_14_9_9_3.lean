-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_9_9_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:31:55.974533+00:00
-- url     : https://prove2.me/submissions/60a73243-76b9-4d6e-9e00-1eb7ff601a96

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 9 9 (RowCompute.rows[3]!) =
    (193164601076932116839368180192689796225397206376647753728000000 : ℤ) := by
  decide +kernel
