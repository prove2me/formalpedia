-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_7_9_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:27:39.735987+00:00
-- url     : https://prove2.me/submissions/32e29525-9972-4bc3-b92c-2582376be6de

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 7 9 (RowCompute.rows[4]!) =
    (4574168886427312092932663363781561666599716371415695360000000 : ℤ) := by
  decide +kernel
