-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_5_9_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:46:23.37299+00:00
-- url     : https://prove2.me/submissions/0660b784-76c5-4c11-86ab-deb9bb6a7b75

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 5 9 (RowCompute.rows[4]!) =
    (26689729685146736192325985949489086711421153491462127616000000 : ℤ) := by
  decide +kernel
