-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_tail_kernel_tonelli_lhs_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T06:32:20.675502+00:00
-- url     : https://prove2.me/submissions/787b6009-e887-47f2-8042-52f8190d5299

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (s : ℝ) (ρ : Measure ℝ) (hprob : IsProbabilityMeasure ρ) :
    (∫⁻ y, ∫⁻ z, (if 0 ≤ y ∧ y < z then ENNReal.ofReal (Real.exp (-s * y)) else 0) ∂ρ ∂volume) =
      ∫⁻ y in Ici (0 : ℝ), (∫⁻ z in Ioi y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) ∂volume := by
  have hG_eq : (fun y : ℝ => ∫⁻ z : ℝ, (if 0 ≤ y ∧ y < z then ENNReal.ofReal (Real.exp (-s * y)) else 0) ∂ρ) =
      (Ici (0 : ℝ)).indicator (fun y : ℝ => ∫⁻ z in Ioi y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) := by
    funext y
    by_cases hy0 : 0 ≤ y
    · have hmem : y ∈ Ici (0 : ℝ) := mem_Ici.mpr hy0
      rw [Set.indicator_of_mem hmem]
      have hFy_eq : (fun z : ℝ => (if 0 ≤ y ∧ y < z then ENNReal.ofReal (Real.exp (-s * y)) else 0)) =
          (Ioi y).indicator (fun _ : ℝ => ENNReal.ofReal (Real.exp (-s * y))) := by
        funext z
        by_cases hz : y < z
        · have h_and : 0 ≤ y ∧ y < z := ⟨hy0, hz⟩
          rw [if_pos h_and]
          have hmem2 : z ∈ Ioi y := mem_Ioi.mpr hz
          rw [Set.indicator_of_mem hmem2]
        · have hn_and : ¬ (0 ≤ y ∧ y < z) := fun h => hz h.2
          rw [if_neg hn_and]
          have hnmem : z ∉ Ioi y := fun h => hz (mem_Ioi.mp h)
          rw [Set.indicator_of_notMem hnmem]
      rw [hFy_eq, lintegral_indicator measurableSet_Ioi]
    · have hnmem : y ∉ Ici (0 : ℝ) := fun h => hy0 (mem_Ici.mp h)
      rw [Set.indicator_of_notMem hnmem]
      have hFy0 : (fun z : ℝ => (if 0 ≤ y ∧ y < z then ENNReal.ofReal (Real.exp (-s * y)) else 0)) = fun _ : ℝ => 0 := by
        funext z
        have hn_and : ¬ (0 ≤ y ∧ y < z) := fun h => hy0 h.1
        rw [if_neg hn_and]
      rw [hFy0, lintegral_const, zero_mul]
  rw [hG_eq, lintegral_indicator measurableSet_Ici]
