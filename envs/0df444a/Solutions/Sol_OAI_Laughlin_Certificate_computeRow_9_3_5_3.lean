-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_3_5_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:42:49.370755+00:00
-- url     : https://prove2.me/submissions/97c76078-83c5-4ed5-8cb1-3bbdcab0ee95

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 3 5 (RowCompute.rows[3]!) =
    (-45428231968076840608089889236946961965552350438988185600000 : ℤ) := by
  decide +kernel
