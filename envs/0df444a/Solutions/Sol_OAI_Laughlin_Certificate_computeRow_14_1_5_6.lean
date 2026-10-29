-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_1_5_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:38:56.266457+00:00
-- url     : https://prove2.me/submissions/f9f49866-5a8e-439c-bef8-da8a415f542c

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 1 5 (RowCompute.rows[6]!) =
    (8348999615416841572995862782132335074878484150002647040000000 : ℤ) := by
  decide +kernel
