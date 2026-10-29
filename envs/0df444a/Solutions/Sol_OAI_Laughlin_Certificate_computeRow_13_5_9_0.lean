-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_5_9_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:46:21.368953+00:00
-- url     : https://prove2.me/submissions/c317d5b5-7d4f-4c02-8f09-fe27fc76bec4

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 5 9 (RowCompute.rows[0]!) =
    (-226801110699472313118984152294167869897119197477063360512000000 : ℤ) := by
  decide +kernel
