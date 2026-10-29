-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_1_3_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:46:20.292024+00:00
-- url     : https://prove2.me/submissions/88d91ab8-47a1-419f-adbc-a97728c3b08f

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 1 3 (RowCompute.rows[0]!) =
    (-1398264617933207681373120558100319555075630133852946563072000000 : ℤ) := by
  decide +kernel
