-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_3_7_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:34:29.156093+00:00
-- url     : https://prove2.me/submissions/f3089906-0377-43ce-8c50-c9be2f7364c2

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 3 7 (RowCompute.rows[1]!) =
    (440144837133325722226735611306267521968686886268436480000000 : ℤ) := by
  decide +kernel
