-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_5_5_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:41:14.100409+00:00
-- url     : https://prove2.me/submissions/77c661a9-971a-4c9f-9250-f2d0fd837d26

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 5 5 (RowCompute.rows[5]!) =
    (-18289309518176691307649155172742367493339549880438226944000000 : ℤ) := by
  decide +kernel
