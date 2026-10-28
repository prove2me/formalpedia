-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_7_7_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:31:40.823701+00:00
-- url     : https://prove2.me/submissions/06ee4fdd-4925-45dd-bbff-0c3aef8834fa

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 7 7 (RowCompute.rows[4]!) =
    (-14171658115507171948684957793767797136158427254777446400000 : ℤ) := by
  decide +kernel
