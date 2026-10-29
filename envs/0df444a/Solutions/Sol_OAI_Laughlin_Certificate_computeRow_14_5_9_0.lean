-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_5_9_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:44:04.6606+00:00
-- url     : https://prove2.me/submissions/87e7c790-c7ae-49b7-a6ab-1a9e26dfdd49

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 5 9 (RowCompute.rows[0]!) =
    (-795725759602789363590626675118666922987690843991879712768000000 : ℤ) := by
  decide +kernel
