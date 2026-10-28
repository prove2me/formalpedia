-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_5_9_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:27:43.222658+00:00
-- url     : https://prove2.me/submissions/dfafd6d9-bc66-41c3-9651-2a60896654c3

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 5 9 (RowCompute.rows[3]!) =
    (-247957083545747349086536852468567398441719472923269398528000000 : ℤ) := by
  decide +kernel
