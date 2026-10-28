-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_7_7_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:13:41.997358+00:00
-- url     : https://prove2.me/submissions/1f675340-192b-41f1-b66a-9c147c1541ae

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 7 7 (RowCompute.rows[1]!) =
    (374930508024946172181179426063395721225003259024900096000000 : ℤ) := by
  decide +kernel
