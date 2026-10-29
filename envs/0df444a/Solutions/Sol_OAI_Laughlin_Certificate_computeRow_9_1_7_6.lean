-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_1_7_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:33:04.651784+00:00
-- url     : https://prove2.me/submissions/dd78d0aa-82df-4546-ae57-8e5f219892f7

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 1 7 (RowCompute.rows[6]!) =
    (5294719750798158506947964440292297145217251667240550400000 : ℤ) := by
  decide +kernel
