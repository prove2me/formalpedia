-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_9_9_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:47:27.574535+00:00
-- url     : https://prove2.me/submissions/f4d13c0c-a589-4478-8262-9eeb9b35da5d

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 12 9 9 (RowCompute.rows[2]!) =
    (-67025413333875599196748756023638880343576242487061957836800000 : ℤ) := by
  decide +kernel
