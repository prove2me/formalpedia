-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_1_13_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:42:57.000487+00:00
-- url     : https://prove2.me/submissions/78b18f4d-4476-45fb-a6ad-bab57423a786

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 1 13 (RowCompute.rows[6]!) =
    (413591714071034905251492991481622539383191000124829466624000000 : ℤ) := by
  decide +kernel
