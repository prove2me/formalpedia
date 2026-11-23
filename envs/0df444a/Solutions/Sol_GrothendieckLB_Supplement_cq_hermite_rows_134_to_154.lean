-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_hermite_rows_134_to_154
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:33:32.809359+00:00
-- url     : https://prove2.me/submissions/ccbe8e9c-3d08-430b-aa9f-a05358e12b14

import Theorems.Thm_GrothendieckLB_Supplement_cq_hermite_rows_134_to_144
import Theorems.Thm_GrothendieckLB_Supplement_cq_hermite_rows_144_to_154

open GrothendieckLB.Supplement

theorem solution : ∀ ini : Array CQHeadArithmetic.MomentCombination,
      CQHeadArithmetic.grid 251 ini 134 = CQHermite251.state 11 →
      CQHeadArithmetic.grid 251 ini 154 = CQHermite251.state 12 := by
  intro ini h
  exact cq_hermite_rows_144_to_154 ini (cq_hermite_rows_134_to_144 ini h)
