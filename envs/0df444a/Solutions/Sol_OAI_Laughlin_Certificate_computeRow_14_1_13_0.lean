-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_1_13_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:27:38.513729+00:00
-- url     : https://prove2.me/submissions/91b89c0b-705d-4192-bcc2-6ba8ee3f0c86

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 1 13 (RowCompute.rows[0]!) =
    (75348251363015113910264851948389181947729734075398087507968000000 : ℤ) := by
  decide +kernel
