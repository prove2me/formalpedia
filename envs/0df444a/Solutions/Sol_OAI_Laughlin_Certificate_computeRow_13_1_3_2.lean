-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_1_3_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:13:46.930028+00:00
-- url     : https://prove2.me/submissions/3c798481-8444-4e1b-a13f-9930a0070989

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 1 3 (RowCompute.rows[2]!) =
    (274290367321280608056594003111261694013874779519107203072000000 : ℤ) := by
  decide +kernel
