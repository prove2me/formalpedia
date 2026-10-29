-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_5_13_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:44:19.720007+00:00
-- url     : https://prove2.me/submissions/92615995-2521-47e2-bb4e-12e810698b61

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 5 13 (RowCompute.rows[2]!) =
    (-616423864770936184793748330451730608011578626441255845888000000 : ℤ) := by
  decide +kernel
