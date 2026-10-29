-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_3_7_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:36:35.745831+00:00
-- url     : https://prove2.me/submissions/c7b70dc4-9793-4309-8a06-e82071a9723b

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 3 7 (RowCompute.rows[6]!) =
    (-109597039092866709613421037242889260519434291617680326656000000 : ℤ) := by
  decide +kernel
