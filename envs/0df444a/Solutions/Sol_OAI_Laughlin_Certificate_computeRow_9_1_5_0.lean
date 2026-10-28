-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_1_5_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:25:01.773741+00:00
-- url     : https://prove2.me/submissions/cfd2d0bf-0d9a-4481-9d8f-9c654ea752a9

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 1 5 (RowCompute.rows[0]!) =
    (14787836285160721543724787969959397141990595790635008000000 : ℤ) := by
  decide +kernel
