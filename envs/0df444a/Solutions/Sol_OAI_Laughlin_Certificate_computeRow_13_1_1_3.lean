-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_1_1_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:31:50.583231+00:00
-- url     : https://prove2.me/submissions/16c1be00-8f79-4691-bdb1-6818872dec59

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 1 1 (RowCompute.rows[3]!) =
    (-2861381921106199482460419159121878568463823770237943152640000000 : ℤ) := by
  decide +kernel
