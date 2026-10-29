-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_1_9_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:48:21.803149+00:00
-- url     : https://prove2.me/submissions/66b2779a-249c-4c2b-a47d-cbcaae258b2f

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 1 9 (RowCompute.rows[6]!) =
    (51500321369543523006638231325007948174751162335808716800000 : ℤ) := by
  decide +kernel
