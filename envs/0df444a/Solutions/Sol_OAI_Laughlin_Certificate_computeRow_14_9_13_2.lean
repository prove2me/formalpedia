-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_9_13_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:27:36.074284+00:00
-- url     : https://prove2.me/submissions/d628487d-eb42-43e6-9e0a-dd71d6d147b2

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 9 13 (RowCompute.rows[2]!) =
    (-5952936135585692111600665842806291566363019080334170914816000000 : ℤ) := by
  decide +kernel
