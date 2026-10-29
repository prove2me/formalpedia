-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_9_11_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:41:20.715145+00:00
-- url     : https://prove2.me/submissions/acf0b939-e621-4e14-ae05-593c5e5d67ee

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 9 11 (RowCompute.rows[4]!) =
    (-130186342566688075889988242169901200520678002681622560768000000 : ℤ) := by
  decide +kernel
