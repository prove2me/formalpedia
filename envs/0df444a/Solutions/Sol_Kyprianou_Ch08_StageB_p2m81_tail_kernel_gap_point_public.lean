-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_tail_kernel_gap_point_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T07:58:33.026805+00:00
-- url     : https://prove2.me/submissions/8015199a-72c1-4119-b7cd-671eeda75aa1

import Mathlib
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_tail_kernel_excess_laplace_public
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (d : ℝ) (hd : 0 < d) (ρ : Measure ℝ)
    (hprob : IsProbabilityMeasure ρ)
    (hsupp : ρ (Iio (0 : ℝ)) = 0) :
    ∃ s0 : ℝ, 0 < s0 ∧
      (∫⁻ y, ENNReal.ofReal (Real.exp (-s0 * y)) ∂(volume.withDensity (fun y => if 0 ≤ y then ENNReal.ofReal d * ρ (Ioi y) else 0))) < 1 := by
  haveI := hprob
  have hFirst : ∀ s : ℝ, 0 < s → (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂(volume.withDensity
      (fun y => if 0 ≤ y then ENNReal.ofReal d * ρ (Ioi y) else 0))) =
      ENNReal.ofReal d * (1 - (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ)) / ENNReal.ofReal s :=
    fun s hs => Kyprianou.Ch08.StageB.p2m81_tail_kernel_excess_laplace_public d ρ hprob hsupp s hs
  refine ⟨d + 1, by linarith, ?_⟩
  have hs0 : 0 < d + 1 := by linarith
  have hEq0 := hFirst (d + 1) hs0
  have hle1 : (1 - (∫⁻ y, ENNReal.ofReal (Real.exp (-(d + 1) * y)) ∂ρ)) ≤ 1 := tsub_le_self
  have hmul : ENNReal.ofReal d * (1 - (∫⁻ y, ENNReal.ofReal (Real.exp (-(d + 1) * y)) ∂ρ)) ≤ ENNReal.ofReal d := by
    have h : ENNReal.ofReal d * (1 - (∫⁻ y, ENNReal.ofReal (Real.exp (-(d + 1) * y)) ∂ρ)) ≤
        ENNReal.ofReal d * 1 :=
      mul_le_mul' le_rfl hle1
    rwa [mul_one] at h
  have hle2 : ENNReal.ofReal d * (1 - (∫⁻ y, ENNReal.ofReal (Real.exp (-(d + 1) * y)) ∂ρ)) / ENNReal.ofReal (d + 1) ≤
      ENNReal.ofReal d / ENNReal.ofReal (d + 1) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul' hmul le_rfl
  have hdiv : ENNReal.ofReal d / ENNReal.ofReal (d + 1) = ENNReal.ofReal (d / (d + 1)) :=
    (ENNReal.ofReal_div_of_pos hs0).symm
  have hlt1 : ENNReal.ofReal (d / (d + 1)) < 1 := ENNReal.ofReal_lt_one.mpr (by field_simp; linarith)
  have hlt2 : ENNReal.ofReal d / ENNReal.ofReal (d + 1) < 1 := by
    rw [hdiv]
    exact hlt1
  rw [hEq0]
  exact lt_of_le_of_lt hle2 hlt2
