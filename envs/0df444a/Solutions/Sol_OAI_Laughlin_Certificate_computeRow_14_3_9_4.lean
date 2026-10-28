-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_3_9_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:29:31.854411+00:00
-- url     : https://prove2.me/submissions/b251ab3b-0159-4df6-afda-bc8967a5d0a4

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 3 9 (RowCompute.rows[4]!) =
    (89839135133119685110396794100414798112906416646875250688000000 : ℤ) := by
  decide +kernel
