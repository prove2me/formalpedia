-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_9_13_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:39:56.384565+00:00
-- url     : https://prove2.me/submissions/e2d14188-e670-472a-aa21-dc9a9cf6f573

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 9 13 (RowCompute.rows[0]!) =
    (-4406470457374360348219469170358024023019824573108293992448000000 : ℤ) := by
  decide +kernel
