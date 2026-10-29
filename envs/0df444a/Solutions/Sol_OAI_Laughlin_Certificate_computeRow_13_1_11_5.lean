-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_1_11_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:44:14.356704+00:00
-- url     : https://prove2.me/submissions/a4a38e36-3434-4fe5-936c-aa6881e1a63d

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 1 11 (RowCompute.rows[5]!) =
    (-766901012582903709425896492881274118024868524850470191104000000 : ℤ) := by
  decide +kernel
