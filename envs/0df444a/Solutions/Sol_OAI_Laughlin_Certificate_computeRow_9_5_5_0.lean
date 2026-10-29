-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_5_5_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:49:37.889763+00:00
-- url     : https://prove2.me/submissions/16519008-d573-4661-9f13-6fa82147e82a

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 5 5 (RowCompute.rows[0]!) =
    (98714204900768875117337071395502896058599824117936947200000 : ℤ) := by
  decide +kernel
