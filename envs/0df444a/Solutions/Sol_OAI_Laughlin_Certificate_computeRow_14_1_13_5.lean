-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_1_13_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:36:34.368623+00:00
-- url     : https://prove2.me/submissions/04aec740-53a6-4a73-95cd-74847240679c

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 1 13 (RowCompute.rows[5]!) =
    (-2780349320534338364378466626910994207780002854120221310976000000 : ℤ) := by
  decide +kernel
