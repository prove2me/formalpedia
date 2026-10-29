-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_5_5_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:39:58.087286+00:00
-- url     : https://prove2.me/submissions/2f1a57d6-635d-42af-9081-b50fac881a5a

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 5 5 (RowCompute.rows[2]!) =
    (-16170339017491520360931716018314174775257719865413206016000000 : ℤ) := by
  decide +kernel
