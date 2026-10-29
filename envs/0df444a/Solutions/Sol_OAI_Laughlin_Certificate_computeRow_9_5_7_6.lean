-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_5_7_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:48:19.674291+00:00
-- url     : https://prove2.me/submissions/5dfc7347-740a-429f-95cf-956e4adac5f0

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 5 7 (RowCompute.rows[6]!) =
    (1266592853361175696920124646706138230670133092050534400000 : ℤ) := by
  decide +kernel
