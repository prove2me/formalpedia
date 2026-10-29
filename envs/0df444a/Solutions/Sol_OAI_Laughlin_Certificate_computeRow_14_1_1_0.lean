-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_1_1_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:49:43.816021+00:00
-- url     : https://prove2.me/submissions/fcc22a95-2c61-456f-bd4a-97091dfa3c4d

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 1 1 (RowCompute.rows[0]!) =
    (16315519674746058267910070791097391958554069859481715474432000000 : ℤ) := by
  decide +kernel
