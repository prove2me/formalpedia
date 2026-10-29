-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_7_13_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:43:00.497982+00:00
-- url     : https://prove2.me/submissions/bd18985e-1931-46b4-985a-17ca6c3f5b1f

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 7 13 (RowCompute.rows[3]!) =
    (2755808055777381188590468418082806102806419197847140302848000000 : ℤ) := by
  decide +kernel
