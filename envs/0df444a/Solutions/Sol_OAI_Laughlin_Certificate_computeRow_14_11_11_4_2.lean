-- Prove2me | solution 2 for OAI.Laughlin.Certificate.computeRow_14_11_11_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:52:39.516336+00:00
-- url     : https://prove2.me/submissions/0610d9ca-34ca-4758-b34b-e366e37f85bf

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 11 11 (RowCompute.rows[4]!) =
    (250982975863268616699691847899858177431504311564598509568000000 : ℤ) := by
  decide +kernel
