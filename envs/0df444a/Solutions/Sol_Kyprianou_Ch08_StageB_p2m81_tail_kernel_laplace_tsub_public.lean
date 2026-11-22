-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_tail_kernel_laplace_tsub_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T07:10:33.864773+00:00
-- url     : https://prove2.me/submissions/a17aff87-62ee-438f-bc5c-746231ab5c6a

import Mathlib
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_rho_laplace_pos_le_one_public
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (s : ℝ) (hs : 0 < s) (ρ : Measure ℝ)
    (hprob : IsProbabilityMeasure ρ)
    (hsupp : ρ (Iio (0 : ℝ)) = 0) :
    (∫⁻ z, (1 - ENNReal.ofReal (Real.exp (-s * z))) ∂ρ) =
      1 - ∫⁻ z, ENNReal.ofReal (Real.exp (-s * z)) ∂ρ := by
  haveI := hprob
  have hRle : (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z)) ∂ρ) ≤ 1 :=
    (Kyprianou.Ch08.StageB.p2m81_rho_laplace_pos_le_one_public ρ hprob hsupp s hs).2
  have h_e_meas : Measurable (fun y : ℝ => ENNReal.ofReal (Real.exp (-s * y))) :=
    (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
      (by continuity : Continuous (fun y : ℝ => -s * y)))).measurable
  have h_ae_nonneg : ∀ᵐ y ∂ρ, 0 ≤ y := by
    have hmem : (Iio (0 : ℝ))ᶜ ∈ ae ρ := compl_mem_ae_iff.mpr hsupp
    filter_upwards [Filter.eventually_mem_set.mpr hmem] with y hy
    have hy' : y ∈ Ici (0 : ℝ) := by simpa [Set.compl_Iio] using hy
    exact Set.mem_Ici.mp hy'
  have h_ae_le : ∀ᵐ y ∂ρ, ENNReal.ofReal (Real.exp (-s * y)) ≤ 1 := by
    filter_upwards [h_ae_nonneg] with y hy
    have hle : Real.exp (-s * y) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have hnn : 0 ≤ s * y := mul_nonneg hs.le hy
      have heq : -s * y = -(s * y) := neg_mul s y
      linarith)
    simpa [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hle
  have h_add_ae : ∀ᵐ z ∂ρ, (ENNReal.ofReal (Real.exp (-s * z)) + (1 - ENNReal.ofReal (Real.exp (-s * z)))) = 1 :=
    Filter.Eventually.mono h_ae_le (fun z hz => add_tsub_cancel_of_le hz)
  have hL_ne : (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z)) ∂ρ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hRle
  have h_sum1 : (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z)) ∂ρ) + ∫⁻ z : ℝ, (1 - ENNReal.ofReal (Real.exp (-s * z))) ∂ρ = 1 := by
    have h1 : (∫⁻ _ : ℝ, (1 : ℝ≥0∞) ∂ρ) = 1 := by rw [lintegral_one, IsProbabilityMeasure.measure_univ]
    have h2 : (∫⁻ z : ℝ, (ENNReal.ofReal (Real.exp (-s * z)) + (1 - ENNReal.ofReal (Real.exp (-s * z)))) ∂ρ) = 1 := by
      rw [lintegral_congr_ae h_add_ae, h1]
    rwa [lintegral_add_left h_e_meas _] at h2
  have hcan := ENNReal.add_sub_cancel_left hL_ne (a := (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z)) ∂ρ)) (b := ∫⁻ z : ℝ, (1 - ENNReal.ofReal (Real.exp (-s * z))) ∂ρ)
  rw [h_sum1] at hcan
  exact hcan.symm
