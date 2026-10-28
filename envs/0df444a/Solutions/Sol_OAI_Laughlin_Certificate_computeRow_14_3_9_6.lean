-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_3_9_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:10:35.532221+00:00
-- url     : https://prove2.me/submissions/c125febb-46fa-4823-a7d6-3ddfb6f44354

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 3 9 (RowCompute.rows[6]!) =
    (-9992986400033612658462379947620881056228494971773124608000000 : ℤ) := by
  decide +kernel
