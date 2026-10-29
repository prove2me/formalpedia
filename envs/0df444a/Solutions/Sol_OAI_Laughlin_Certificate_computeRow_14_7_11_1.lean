-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_7_11_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:44:16.370038+00:00
-- url     : https://prove2.me/submissions/f021afc4-0494-4f14-9e1d-c2d62a104271

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 7 11 (RowCompute.rows[1]!) =
    (-2716641102943785147977659282367174000730642951004225536000000 : ℤ) := by
  decide +kernel
