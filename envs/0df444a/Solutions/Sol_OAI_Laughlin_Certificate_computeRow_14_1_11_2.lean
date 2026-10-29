-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_1_11_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:48:28.507792+00:00
-- url     : https://prove2.me/submissions/3a9381ea-0d41-4b08-ac49-3a257e83b467

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 1 11 (RowCompute.rows[2]!) =
    (-12529117593641329690488164059286910825569063059621498847232000000 : ℤ) := by
  decide +kernel
