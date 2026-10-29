-- Prove2me | solution 2 for OAI.Laughlin.Certificate.computeRow_12_5_7_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:45:32.050035+00:00
-- url     : https://prove2.me/submissions/dbe97168-fd2e-4d42-a2da-1d5da0808280

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 12 5 7 (RowCompute.rows[5]!) =
    (865670131159668610884971981834212485625140612673044480000000 : ℤ) := by
  decide +kernel
