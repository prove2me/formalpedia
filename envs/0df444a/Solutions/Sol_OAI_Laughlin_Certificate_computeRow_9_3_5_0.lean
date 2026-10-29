-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_3_5_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:33:07.147975+00:00
-- url     : https://prove2.me/submissions/fe11c16b-09b5-471f-94cc-2ffd44fd46aa

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 3 5 (RowCompute.rows[0]!) =
    (8943603016536055842852973607432799785981824725732556800000 : ℤ) := by
  decide +kernel
