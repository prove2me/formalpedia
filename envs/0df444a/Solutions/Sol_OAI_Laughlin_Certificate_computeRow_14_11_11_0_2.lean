-- Prove2me | solution 2 for OAI.Laughlin.Certificate.computeRow_14_11_11_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:52:36.871615+00:00
-- url     : https://prove2.me/submissions/51b6748d-a90f-4b26-9ded-5955a6f7e43f

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 11 11 (RowCompute.rows[0]!) =
    (3114614113404638483619287775425405160664194096513102643200000000 : ℤ) := by
  decide +kernel
