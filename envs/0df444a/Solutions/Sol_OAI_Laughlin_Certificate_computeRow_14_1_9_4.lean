-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_1_9_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:10:43.328432+00:00
-- url     : https://prove2.me/submissions/a7888279-4b6c-4650-b522-717306526ac7

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 1 9 (RowCompute.rows[4]!) =
    (-596447384440519859416364552700983245364104416626441453568000000 : ℤ) := by
  decide +kernel
