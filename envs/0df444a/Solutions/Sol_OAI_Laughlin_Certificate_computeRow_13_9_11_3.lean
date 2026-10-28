-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_9_11_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:24:57.046714+00:00
-- url     : https://prove2.me/submissions/7bb184c0-e7b8-4fd0-84a9-fd610ab7cfcf

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 9 11 (RowCompute.rows[3]!) =
    (-602392458571025698800273181867365061637992237178460045312000000 : ℤ) := by
  decide +kernel
