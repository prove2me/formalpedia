-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_5_9_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:47:21.44286+00:00
-- url     : https://prove2.me/submissions/cbb8f2f9-2988-4e60-8710-84b5bcd7a0e9

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 5 9 (RowCompute.rows[4]!) =
    (-73246488541879325228804965505152298770634536839964262400000 : ℤ) := by
  decide +kernel
