-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_9_9_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:47:17.164608+00:00
-- url     : https://prove2.me/submissions/c8b1f517-ec0e-4a7b-8850-23b8a45adb2a

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 9 9 (RowCompute.rows[5]!) =
    (341668456699896168814346959138440576703823100206590722048000000 : ℤ) := by
  decide +kernel
