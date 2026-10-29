-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_5_11_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:42:45.199904+00:00
-- url     : https://prove2.me/submissions/6a3efa38-6288-4f46-b5a6-bef84308f216

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 5 11 (RowCompute.rows[6]!) =
    (-35545995011945394724795772535349081146097889497728417792000000 : ℤ) := by
  decide +kernel
