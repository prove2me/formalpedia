-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_3_11_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:39:59.365289+00:00
-- url     : https://prove2.me/submissions/8a95a2db-7476-419b-b820-c8951281d091

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 3 11 (RowCompute.rows[2]!) =
    (-1787133004366262833018500168655079817016273022196633305088000000 : ℤ) := by
  decide +kernel
