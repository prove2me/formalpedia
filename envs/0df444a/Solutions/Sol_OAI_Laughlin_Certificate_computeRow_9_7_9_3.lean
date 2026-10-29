-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_7_9_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:49:34.686319+00:00
-- url     : https://prove2.me/submissions/cbae8e09-2eb2-4504-ad6f-519fa5a71362

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 7 9 (RowCompute.rows[3]!) =
    (1142445560049845048726881266987395242910823776841105408000000 : ℤ) := by
  decide +kernel
