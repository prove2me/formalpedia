-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_9_13_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:29:41.711992+00:00
-- url     : https://prove2.me/submissions/5b2fe750-3e3f-4fdb-a3d9-323b7464d679

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 9 13 (RowCompute.rows[0]!) =
    (-828780340612763102205301358970613431123726601932748357632000000 : ℤ) := by
  decide +kernel
