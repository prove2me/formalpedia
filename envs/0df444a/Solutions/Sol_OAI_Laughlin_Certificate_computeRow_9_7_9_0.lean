-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_7_9_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:10:33.408223+00:00
-- url     : https://prove2.me/submissions/933b8c4f-f9bb-4ce4-b074-a176a9b125a7

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 7 9 (RowCompute.rows[0]!) =
    (3562825001501901300648502658808575751826706804215539302400000 : ℤ) := by
  decide +kernel
