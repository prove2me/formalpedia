-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_rho_laplace_pos_le_one_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T05:23:27.080936+00:00
-- url     : https://prove2.me/submissions/50c115a5-a769-4754-8a5f-f508e2d7e13d

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (ρ : Measure ℝ) (hprob : IsProbabilityMeasure ρ)
    (hsupp : ρ (Iio (0:ℝ)) = 0) :
    ∀ s : ℝ, 0 < s →
      0 < (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) ∧
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) ≤ 1 := by
  intro s hs
  haveI := hprob
  have h_univ : ρ Set.univ = 1 :=
    MeasureTheory.IsProbabilityMeasure.measure_univ
  have h_meas : Measurable (fun y : ℝ => ENNReal.ofReal (Real.exp (-s * y))) :=
    (ENNReal.continuous_ofReal.comp
      (Real.continuous_exp.comp (by continuity : Continuous fun y : ℝ => -s * y))).measurable
  have h_pos : ∀ y : ℝ, 0 < ENNReal.ofReal (Real.exp (-s * y)) :=
    fun y => ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have h_supp_eq : Function.support (fun y : ℝ => ENNReal.ofReal (Real.exp (-s * y))) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    rw [Function.mem_support]
    exact ne_of_gt (h_pos y)
  have h_supp_pos : 0 < ρ (Function.support (fun y : ℝ => ENNReal.ofReal (Real.exp (-s * y)))) := by
    rw [h_supp_eq, h_univ]
    exact zero_lt_one
  have h_int_pos : 0 < ∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ :=
    (MeasureTheory.lintegral_pos_iff_support h_meas).mpr h_supp_pos
  have h_compl_mem : (Set.Iio (0:ℝ))ᶜ ∈ MeasureTheory.ae ρ :=
    MeasureTheory.compl_mem_ae_iff.mpr hsupp
  have h_ae_mem : ∀ᵐ y ∂ρ, y ∈ (Set.Iio (0:ℝ))ᶜ :=
    Filter.eventually_mem_set.mpr h_compl_mem
  have h_ae_nonneg : ∀ᵐ y ∂ρ, 0 ≤ y := by
    filter_upwards [h_ae_mem] with y hy
    rw [Set.compl_Iio] at hy
    exact Set.mem_Ici.mp hy
  have h_ae_le_one : ∀ᵐ y ∂ρ, ENNReal.ofReal (Real.exp (-s * y)) ≤ 1 := by
    filter_upwards [h_ae_nonneg] with y hy
    have h_eq : -s * y = -(s * y) := neg_mul s y
    have h_nonneg : 0 ≤ s * y := mul_nonneg (le_of_lt hs) hy
    have h_neg_nonpos : -s * y ≤ 0 := by
      rw [h_eq]
      exact neg_nonpos.mpr h_nonneg
    have h_exp_le : Real.exp (-s * y) ≤ 1 := Real.exp_le_one_iff.mpr h_neg_nonpos
    calc ENNReal.ofReal (Real.exp (-s * y)) ≤ ENNReal.ofReal 1 :=
          ENNReal.ofReal_le_ofReal h_exp_le
      _ = 1 := ENNReal.ofReal_one
  have h_int_le : (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) ≤ 1 := by
    have h_mono : (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) ≤ ∫⁻ y, (1 : ℝ≥0∞) ∂ρ :=
      MeasureTheory.lintegral_mono_ae h_ae_le_one
    have h_one : (∫⁻ y, (1 : ℝ≥0∞) ∂ρ) = 1 := by
      rw [MeasureTheory.lintegral_one, h_univ]
    rw [h_one] at h_mono
    exact h_mono
  exact ⟨h_int_pos, h_int_le⟩
