-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_5_9_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:27:45.595726+00:00
-- url     : https://prove2.me/submissions/994a470c-5380-4b36-a6d0-c1078923d265

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 12 5 9 (RowCompute.rows[6]!) =
    (378448127366036042771156407714492783474008423237943296000000 : ℤ) := by
  decide +kernel
