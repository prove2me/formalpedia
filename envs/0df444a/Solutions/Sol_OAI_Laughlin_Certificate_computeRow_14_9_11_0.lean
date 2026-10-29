-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_9_11_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:37:36.662627+00:00
-- url     : https://prove2.me/submissions/ecba1913-e509-4fe6-9f32-e543f8f6a283

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 9 11 (RowCompute.rows[0]!) =
    (-1637469801603470733614468942180612465289899172634036273152000000 : ℤ) := by
  decide +kernel
