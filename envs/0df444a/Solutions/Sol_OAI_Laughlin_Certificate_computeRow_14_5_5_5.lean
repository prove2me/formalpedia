-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_5_5_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:39:54.29345+00:00
-- url     : https://prove2.me/submissions/ad2fb397-fe55-44c4-a915-8b446b61868f

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 5 5 (RowCompute.rows[5]!) =
    (40018678828087017191266096631161646824892905899631312896000000 : ℤ) := by
  decide +kernel
