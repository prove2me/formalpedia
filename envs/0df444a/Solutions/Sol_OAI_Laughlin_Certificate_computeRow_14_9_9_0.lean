-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_9_9_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:31:48.804847+00:00
-- url     : https://prove2.me/submissions/a2462203-1c34-40d1-a3a7-7703d730721a

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 9 9 (RowCompute.rows[0]!) =
    (-498746471454758551175451123127306913803424787446919856128000000 : ℤ) := by
  decide +kernel
