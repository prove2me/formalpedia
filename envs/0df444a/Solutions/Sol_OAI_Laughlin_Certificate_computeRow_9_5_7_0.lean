-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_5_7_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:39:03.520402+00:00
-- url     : https://prove2.me/submissions/7369e899-4008-4589-99fe-e6375b69ea29

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 5 7 (RowCompute.rows[0]!) =
    (37484588852647132890760534582881181405001812758704947200000 : ℤ) := by
  decide +kernel
