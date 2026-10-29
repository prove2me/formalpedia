-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_3_13_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:34:30.594392+00:00
-- url     : https://prove2.me/submissions/61fd60e5-5b37-441c-82b8-6311d6e6103c

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 3 13 (RowCompute.rows[2]!) =
    (-1635575911867781037766516158525179414054957274344611381248000000 : ℤ) := by
  decide +kernel
