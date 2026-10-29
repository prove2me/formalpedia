-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_3_3_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:37:29.5427+00:00
-- url     : https://prove2.me/submissions/9979d40e-14ad-4f93-b94a-b49015012aac

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 3 3 (RowCompute.rows[2]!) =
    (-113287141829664706913953578000280158789819404542751539200000 : ℤ) := by
  decide +kernel
