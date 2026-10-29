-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_1_7_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:42:54.377451+00:00
-- url     : https://prove2.me/submissions/afb8ea81-48e2-4abd-9959-0ceafce7d169

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 1 7 (RowCompute.rows[3]!) =
    (-10213361285448456111652197204765770559129671177129164800000 : ℤ) := by
  decide +kernel
