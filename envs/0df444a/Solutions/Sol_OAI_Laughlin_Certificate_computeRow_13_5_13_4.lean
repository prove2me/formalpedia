-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_5_13_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:49:40.59103+00:00
-- url     : https://prove2.me/submissions/6fab25e7-c0e3-483f-8e65-cc913b83b0c4

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 5 13 (RowCompute.rows[4]!) =
    (-569501384077715587174482879314825850361377172782028161024000000 : ℤ) := by
  decide +kernel
