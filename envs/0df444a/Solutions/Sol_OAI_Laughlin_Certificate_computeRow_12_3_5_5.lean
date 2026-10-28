-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_3_5_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:27:40.688195+00:00
-- url     : https://prove2.me/submissions/cf2d1dc8-d9f2-4584-87da-5858c8692b47

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 12 3 5 (RowCompute.rows[5]!) =
    (-235979336626917675230595559629532018289344394727260160000000 : ℤ) := by
  decide +kernel
