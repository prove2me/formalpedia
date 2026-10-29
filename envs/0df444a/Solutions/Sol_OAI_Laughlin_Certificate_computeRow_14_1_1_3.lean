-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_1_1_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:37:34.540792+00:00
-- url     : https://prove2.me/submissions/22020a4c-93de-4d66-9d59-167b7f5ffa04

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 1 1 (RowCompute.rows[3]!) =
    (40025201381448070011885895233367200869402471616021364998144000000 : ℤ) := by
  decide +kernel
