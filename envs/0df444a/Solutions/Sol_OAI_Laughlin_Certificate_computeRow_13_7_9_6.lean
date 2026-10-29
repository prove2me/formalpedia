-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_7_9_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:49:39.431372+00:00
-- url     : https://prove2.me/submissions/8ac28826-071e-457c-b5e9-14555292a4f7

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 7 9 (RowCompute.rows[6]!) =
    (-454832051163890622606137720164663204726020666795491328000000 : ℤ) := by
  decide +kernel
