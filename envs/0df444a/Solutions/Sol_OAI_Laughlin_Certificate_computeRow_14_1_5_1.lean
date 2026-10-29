-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_1_5_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:47:22.895071+00:00
-- url     : https://prove2.me/submissions/52e6f021-c66f-4371-b82c-70622e29c4ce

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 1 5 (RowCompute.rows[1]!) =
    (-634092321763120278763058158198516739721699559018070016000000 : ℤ) := by
  decide +kernel
