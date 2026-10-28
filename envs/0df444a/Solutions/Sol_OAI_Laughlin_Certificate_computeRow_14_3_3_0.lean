-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_3_3_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:13:43.194132+00:00
-- url     : https://prove2.me/submissions/ac2eaf00-1158-4c40-b92f-15a25b1f524f

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 3 3 (RowCompute.rows[0]!) =
    (1171774144973318062921443699938857512246718122359192027136000000 : ℤ) := by
  decide +kernel
