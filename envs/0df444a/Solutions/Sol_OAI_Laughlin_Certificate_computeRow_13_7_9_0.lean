-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_7_9_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:33:11.110747+00:00
-- url     : https://prove2.me/submissions/981dfcc9-d9fe-4680-997f-f5b8c137e29e

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 7 9 (RowCompute.rows[0]!) =
    (9497909122626491863930317482062336248265041893205737472000000 : ℤ) := by
  decide +kernel
