-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_1_5_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:29:26.892695+00:00
-- url     : https://prove2.me/submissions/cebc9a93-680e-451c-8d64-d6caaefbff9e

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 1 5 (RowCompute.rows[2]!) =
    (9732573989302727334672116253191299087851537214262476800000 : ℤ) := by
  decide +kernel
