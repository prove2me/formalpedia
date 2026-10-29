-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_3_11_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:48:25.688646+00:00
-- url     : https://prove2.me/submissions/32b33704-1b26-450b-9e4f-9584694fe082

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 3 11 (RowCompute.rows[0]!) =
    (456780217502041738130150961728666318818502625702117900288000000 : ℤ) := by
  decide +kernel
