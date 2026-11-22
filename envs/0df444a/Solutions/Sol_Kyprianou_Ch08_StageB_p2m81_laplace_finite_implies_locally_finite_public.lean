-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_laplace_finite_implies_locally_finite_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T06:18:20.197798+00:00
-- url     : https://prove2.me/submissions/89880c4c-1b6d-468a-a831-6353b2376f17

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ)
    (hfin1 : (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-(1:ℝ) * y)) ∂ν) < ⊤) :
    ∀ x : ℝ, 0 ≤ x → ν (Iic x) < ⊤ := by
  intro x _
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(1:ℝ) * x)) with hc
  have hc0 : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hle : (Iic x).indicator (fun _ : ℝ => c)
      ≤ fun y : ℝ => ENNReal.ofReal (Real.exp (-(1:ℝ) * y)) := by
    intro y
    by_cases hy : y ∈ Iic x
    · rw [Set.indicator_of_mem hy, hc]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      have hyx : y ≤ x := Set.mem_Iic.mp hy
      linarith
    · rw [Set.indicator_of_notMem hy]
      exact zero_le
  have heq : (∫⁻ y : ℝ, (Iic x).indicator (fun _ : ℝ => c) y ∂ν) = c * ν (Iic x) := by
    rw [lintegral_indicator measurableSet_Iic]
    exact setLIntegral_const _ _
  have hfin2 : c * ν (Iic x) < ⊤ := by
    rw [← heq]
    exact lt_of_le_of_lt (lintegral_mono hle) hfin1
  rcases eq_or_ne (ν (Iic x)) ⊤ with htop | hne
  · rw [htop, ENNReal.mul_top hc0] at hfin2
    exact absurd hfin2 (lt_irrefl _)
  · exact lt_top_iff_ne_top.mpr hne
