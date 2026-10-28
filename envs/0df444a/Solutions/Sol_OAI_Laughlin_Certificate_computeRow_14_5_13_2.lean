-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_5_13_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:13:48.752958+00:00
-- url     : https://prove2.me/submissions/b7d88f88-d77a-4bb2-8a75-49e6928d201e

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 5 13 (RowCompute.rows[2]!) =
    (-7447740185964785871549830025694730391226900953403811168256000000 : ℤ) := by
  decide +kernel
