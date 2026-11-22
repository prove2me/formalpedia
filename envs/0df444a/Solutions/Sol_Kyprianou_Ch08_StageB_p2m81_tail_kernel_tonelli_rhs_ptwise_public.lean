-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_tail_kernel_tonelli_rhs_ptwise_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T06:31:47.499798+00:00
-- url     : https://prove2.me/submissions/b247aef1-4058-49f0-ab20-8635cd6335cd

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (s : ℝ) (z : ℝ) :
    (∫⁻ y, (if 0 ≤ y ∧ y < z then ENNReal.ofReal (Real.exp (-s * y)) else 0) ∂volume) =
      ∫⁻ y in Ico (0 : ℝ) z, ENNReal.ofReal (Real.exp (-s * y)) ∂volume := by
  have h_eq : (fun y : ℝ => (if 0 ≤ y ∧ y < z then ENNReal.ofReal (Real.exp (-s * y)) else 0)) =
      (Ico (0 : ℝ) z).indicator (fun y : ℝ => ENNReal.ofReal (Real.exp (-s * y))) := by
    funext y
    by_cases hmem : y ∈ Ico (0 : ℝ) z
    · have h_and : 0 ≤ y ∧ y < z := mem_Ico.mp hmem
      rw [if_pos h_and, Set.indicator_of_mem hmem]
    · have hn_and : ¬ (0 ≤ y ∧ y < z) := fun h => hmem (mem_Ico.mpr h)
      rw [if_neg hn_and, Set.indicator_of_notMem hmem]
  rw [h_eq, lintegral_indicator measurableSet_Ico]
