-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_1_1_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:36:29.79632+00:00
-- url     : https://prove2.me/submissions/3b197f8e-6a4d-4d3d-ab25-80018ee591fe

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 1 1 (RowCompute.rows[1]!) =
    (1609965306296335491318017681272154818517287513589022720000 : ℤ) := by
  decide +kernel
