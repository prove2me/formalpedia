-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_3_7_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:46:17.952145+00:00
-- url     : https://prove2.me/submissions/00be3574-3e7a-4a07-b0e7-952bcb86395a

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 3 7 (RowCompute.rows[3]!) =
    (-12168341844478710624799668568862693649116268050862047232000000 : ℤ) := by
  decide +kernel
