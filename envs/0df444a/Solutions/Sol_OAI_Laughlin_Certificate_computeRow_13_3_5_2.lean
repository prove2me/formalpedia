-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_3_5_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:36:28.365605+00:00
-- url     : https://prove2.me/submissions/4f6ed20f-1d8c-4e61-914e-ebf4b4d64bc2

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 3 5 (RowCompute.rows[2]!) =
    (-86799709385896199099433431960845398758892174177843806208000000 : ℤ) := by
  decide +kernel
