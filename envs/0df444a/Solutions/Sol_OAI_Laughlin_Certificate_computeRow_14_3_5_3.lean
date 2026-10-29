-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_3_5_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:48:24.317213+00:00
-- url     : https://prove2.me/submissions/6a20ddf5-7ebe-4eb3-b88d-479721b307da

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 3 5 (RowCompute.rows[3]!) =
    (436072067245675145445647918680526563932279777508731125760000000 : ℤ) := by
  decide +kernel
