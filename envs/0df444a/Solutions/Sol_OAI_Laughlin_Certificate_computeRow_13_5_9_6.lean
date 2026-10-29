-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_5_9_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:45:16.988399+00:00
-- url     : https://prove2.me/submissions/07836168-7027-4173-8109-397ff44a29ab

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 5 9 (RowCompute.rows[6]!) =
    (-187976986997897754343571026798512642099931634517147648000000 : ℤ) := by
  decide +kernel
