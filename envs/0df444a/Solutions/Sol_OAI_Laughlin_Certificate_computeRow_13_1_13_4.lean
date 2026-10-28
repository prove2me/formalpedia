-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_1_13_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:29:34.560871+00:00
-- url     : https://prove2.me/submissions/bc23533c-3f71-476e-ac49-b31fa4d37e12

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 1 13 (RowCompute.rows[4]!) =
    (-6400212471207606938669843548672527701272397095277722337280000000 : ℤ) := by
  decide +kernel
