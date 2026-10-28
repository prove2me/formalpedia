-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_3_5_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:25:07.158532+00:00
-- url     : https://prove2.me/submissions/f2182fef-bc0a-43f4-9002-888bfe732ad2

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 3 5 (RowCompute.rows[0]!) =
    (-258915361619770370533600124938145316111888018239863652352000000 : ℤ) := by
  decide +kernel
