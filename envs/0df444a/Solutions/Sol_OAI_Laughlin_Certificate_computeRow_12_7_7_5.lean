-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_7_7_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:29:38.754395+00:00
-- url     : https://prove2.me/submissions/cf07570f-0558-40f9-a1fb-fde34906e490

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 12 7 7 (RowCompute.rows[5]!) =
    (4851075457044814083629224785076392286413048331552948224000000 : ℤ) := by
  decide +kernel
