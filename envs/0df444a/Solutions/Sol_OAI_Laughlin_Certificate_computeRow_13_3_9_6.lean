-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_3_9_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:31:42.217624+00:00
-- url     : https://prove2.me/submissions/34fd3535-f325-474a-8d13-45ed96d0bee5

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 3 9 (RowCompute.rows[6]!) =
    (1937749405837867467567693880979960988805680965099716608000000 : ℤ) := by
  decide +kernel
