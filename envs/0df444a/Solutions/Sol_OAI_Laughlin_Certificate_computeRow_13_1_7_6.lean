-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_1_7_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:33:14.126043+00:00
-- url     : https://prove2.me/submissions/dfd94e1a-c164-4de8-ad69-da0aa0799fec

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 1 7 (RowCompute.rows[6]!) =
    (9514226187553596692674010440300600907436886385076731904000000 : ℤ) := by
  decide +kernel
