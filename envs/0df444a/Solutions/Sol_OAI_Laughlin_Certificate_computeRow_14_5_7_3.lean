-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_5_7_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:29:30.789828+00:00
-- url     : https://prove2.me/submissions/bc3ae953-e340-4741-9e82-44b612179b23

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 5 7 (RowCompute.rows[3]!) =
    (-91227671710107835601827811555054884073272800787040305152000000 : ℤ) := by
  decide +kernel
