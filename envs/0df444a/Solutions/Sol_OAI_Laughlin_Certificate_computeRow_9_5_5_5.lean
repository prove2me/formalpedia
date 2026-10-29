-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_5_5_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:45:29.94944+00:00
-- url     : https://prove2.me/submissions/595e216d-aabe-47d0-9ca2-5ba25bb02054

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 5 5 (RowCompute.rows[5]!) =
    (11159881340665062295596207785994754044082055200899072000000 : ℤ) := by
  decide +kernel
