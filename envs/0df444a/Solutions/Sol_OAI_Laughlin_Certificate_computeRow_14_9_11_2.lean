-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_9_11_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:27:41.885836+00:00
-- url     : https://prove2.me/submissions/a888d91f-180e-474a-85e0-859699b91d0c

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 9 11 (RowCompute.rows[2]!) =
    (1108307524501887878897945109538678826475604775551352438784000000 : ℤ) := by
  decide +kernel
