-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_5_9_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:24:50.527184+00:00
-- url     : https://prove2.me/submissions/55a13c3f-8405-4d1c-a604-afec60e52753

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 12 5 9 (RowCompute.rows[0]!) =
    (32040035099900781455441906971521926173497545553529012224000000 : ℤ) := by
  decide +kernel
