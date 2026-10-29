-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_1_7_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:40:02.061998+00:00
-- url     : https://prove2.me/submissions/91255eae-a848-4d6a-bf60-bd0e56aa77ce

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 1 7 (RowCompute.rows[0]!) =
    (-1717940113540435269170840538839215688651256377481206169600000 : ℤ) := by
  decide +kernel
