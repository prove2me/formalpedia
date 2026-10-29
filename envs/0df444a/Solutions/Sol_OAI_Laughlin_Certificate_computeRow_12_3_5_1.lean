-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_3_5_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:33:03.149574+00:00
-- url     : https://prove2.me/submissions/7e4d533e-1e4f-4810-80d2-b5d1f383b59d

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 12 3 5 (RowCompute.rows[1]!) =
    (1350507864666514220651149017749683187705466499104768000000 : ℤ) := by
  decide +kernel
