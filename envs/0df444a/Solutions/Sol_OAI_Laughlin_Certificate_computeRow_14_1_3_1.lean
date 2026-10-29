-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_1_3_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:49:33.480027+00:00
-- url     : https://prove2.me/submissions/69b2aac9-ec6b-48da-b0c6-794da6cc2e1a

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 1 3 (RowCompute.rows[1]!) =
    (-5447494351263095488572649494944711037803708356164059136000000 : ℤ) := by
  decide +kernel
