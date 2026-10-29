-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_5_7_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:48:20.880981+00:00
-- url     : https://prove2.me/submissions/1e9d4f7b-5138-4f40-a400-92f745a3c14b

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 5 7 (RowCompute.rows[0]!) =
    (-564696756682112598901362083284606364839609679621155454976000000 : ℤ) := by
  decide +kernel
