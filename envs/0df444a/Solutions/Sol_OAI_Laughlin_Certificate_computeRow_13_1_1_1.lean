-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_1_1_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:36:32.997859+00:00
-- url     : https://prove2.me/submissions/139a3558-2c9c-4055-867d-c06ad16a8a69

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 1 1 (RowCompute.rows[1]!) =
    (-6706373553862953531399451932947255971414237429723299840000000 : ℤ) := by
  decide +kernel
