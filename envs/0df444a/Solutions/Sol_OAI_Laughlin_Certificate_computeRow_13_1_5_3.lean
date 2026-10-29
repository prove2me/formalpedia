-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_1_5_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:45:23.364986+00:00
-- url     : https://prove2.me/submissions/3b27c939-d9c8-4e7b-b27e-e3ae90624f3d

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 1 5 (RowCompute.rows[3]!) =
    (487213343748768278132196730391299424224153834462516346880000000 : ℤ) := by
  decide +kernel
