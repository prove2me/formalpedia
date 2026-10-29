-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_7_11_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:44:15.408508+00:00
-- url     : https://prove2.me/submissions/9901e809-c53b-436e-963b-d7abeb964277

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 7 11 (RowCompute.rows[6]!) =
    (-20032068846449947903404485471813777717216741268620574720000000 : ℤ) := by
  decide +kernel
