-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_7_13_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:37:33.229708+00:00
-- url     : https://prove2.me/submissions/3f6640b2-86e6-4779-bc06-d2cc2a97fb12

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 7 13 (RowCompute.rows[4]!) =
    (-158192066491452964116823863722507833619415827914300588032000000 : ℤ) := by
  decide +kernel
