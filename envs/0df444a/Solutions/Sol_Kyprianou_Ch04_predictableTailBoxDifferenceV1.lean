-- Prove2me | solution 1 for Kyprianou.Ch04.predictableTailBoxDifferenceV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:38:06.742722+00:00
-- url     : https://prove2.me/submissions/d4df0745-683d-4b6a-9bfe-73b754e15475

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A finite time cell equals the difference of two predictable tail boxes. -/
theorem solution (a b T : ℝ) (hab : a ≤ b) (hbT : b ≤ T)
    (B : Set ℝ) (c : ℝ) (z : ℝ × ℝ) :
    (Ioc a b ×ˢ B).indicator (fun _ => c) z =
      (Ioc a T ×ˢ B).indicator (fun _ => c) z -
      (Ioc b T ×ˢ B).indicator (fun _ => c) z := by
  classical
  by_cases hm : z.2 ∈ B
  · by_cases ha : a < z.1
    · by_cases hb : b < z.1
      · have hnb : ¬ z.1 ≤ b := not_le.mpr hb
        simp [Set.indicator, Set.mem_prod, Set.mem_Ioc, hm, ha, hb, hnb]
      · have hzb : z.1 ≤ b := le_of_not_gt hb
        have hzT := hzb.trans hbT
        simp [Set.indicator, Set.mem_prod, Set.mem_Ioc, hm, ha, hb, hzb, hzT]
    · have hnb : ¬ b < z.1 := fun h => ha (lt_of_le_of_lt hab h)
      simp [Set.indicator, Set.mem_prod, Set.mem_Ioc, hm, ha, hnb]
  · simp [Set.indicator, Set.mem_prod, hm]
