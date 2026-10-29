-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_5_11_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:44:10.487+00:00
-- url     : https://prove2.me/submissions/d7f45253-0f15-42c3-be69-730330703541

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 5 11 (RowCompute.rows[1]!) =
    (-19367544845735385526975577162051985713642871233445888000000 : ℤ) := by
  decide +kernel
