-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_5_13_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:27:48.392745+00:00
-- url     : https://prove2.me/submissions/eac2fa5d-7af2-426e-9cc6-ac37c74c2b31

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 5 13 (RowCompute.rows[4]!) =
    (1782245692515524601055467413458403940320187128901355438080000000 : ℤ) := by
  decide +kernel
