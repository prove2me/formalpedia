-- Prove2me | solution 2 for OAI.Laughlin.Certificate.computeRow_12_3_3_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:38:49.558424+00:00
-- url     : https://prove2.me/submissions/42a1d54b-0698-49d4-a61d-2eee2e8002f5

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 12 3 3 (RowCompute.rows[4]!) =
    (-381886403076071442777717796594028700365785532393009971200000 : ℤ) := by
  decide +kernel
