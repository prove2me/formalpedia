-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_3_3_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:33:12.749147+00:00
-- url     : https://prove2.me/submissions/36e12de5-e16e-48a1-8b8c-95a9c1a9b24a

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 3 3 (RowCompute.rows[3]!) =
    (-735921767610579744048872155919764376195820606014047125504000000 : ℤ) := by
  decide +kernel
