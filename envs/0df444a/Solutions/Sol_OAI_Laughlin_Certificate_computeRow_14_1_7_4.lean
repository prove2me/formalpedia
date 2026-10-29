-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_1_7_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:39:50.932436+00:00
-- url     : https://prove2.me/submissions/a27ee527-6230-4771-bddd-082679a02398

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 1 7 (RowCompute.rows[4]!) =
    (-645709163704764383709970387687768736395173834731097686016000000 : ℤ) := by
  decide +kernel
