-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_3_7_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:44:17.805041+00:00
-- url     : https://prove2.me/submissions/c8008d03-deac-427f-9a94-cf2975b690ed

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 3 7 (RowCompute.rows[3]!) =
    (59010156571852229004491734230109817307197748932719411200000 : ℤ) := by
  decide +kernel
