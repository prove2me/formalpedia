-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_drawdown_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T03:18:15.871836+00:00
-- url     : https://prove2.me/submissions/1b7b82d3-3beb-44a2-8eb9-592f196ba85b

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (f : ℝ → ℝ) (hpos : ∀ s : ℝ, 0 < s → 0 < f s)
    (hdraw : ∀ d : ℝ, 0 < d → ∃ ρ : Measure ℝ,
      IsProbabilityMeasure ρ ∧ ρ (Iio (0 : ℝ)) = 0 ∧
      ∀ s : ℝ, 0 < s →
        (f d - f s) * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal =
          f d * (1 - s / d))
    (ρd : ℝ → Measure ℝ)
    (hρd : ∀ d : ℝ, 0 < d →
      IsProbabilityMeasure (ρd d) ∧ (ρd d) (Iio (0 : ℝ)) = 0 ∧
      ∀ s : ℝ, 0 < s →
        (f d - f s) * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂(ρd d)).toReal =
          f d * (1 - s / d))
    (d : ℝ) (hd1 : 1 ≤ d) : d / f d ≤ 1 / f 1 := by
  have hd_pos : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have hf1_pos : 0 < f 1 := hpos 1 zero_lt_one
  have hfd_pos : 0 < f d := hpos d hd_pos
  obtain ⟨hprob, hsupp, heq⟩ := hρd d hd_pos
  have heq1 := heq 1 zero_lt_one
  have h_ae_nonneg : ∀ᵐ y ∂(ρd d), 0 ≤ y :=
    MeasureTheory.ae_iff.mpr (by
      have hset : {y : ℝ | ¬ (0 : ℝ) ≤ y} = Iio (0 : ℝ) := by
        ext y
        simp [not_le]
      rw [hset]
      exact hsupp)
  have h_int_bound : ∀ s : ℝ, 0 < s →
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂(ρd d)) ≤ 1 := by
    intro s hs
    have h_le_ae : ∀ᵐ y ∂(ρd d), ENNReal.ofReal (Real.exp (-s * y)) ≤ 1 := by
      filter_upwards [h_ae_nonneg] with y hy
      have h_arg : -s * y ≤ 0 := by nlinarith [mul_nonneg hs.le hy]
      have h_exp : Real.exp (-s * y) ≤ 1 := Real.exp_le_one_iff.mpr h_arg
      exact ENNReal.ofReal_le_one.mpr h_exp
    have h_mono := MeasureTheory.lintegral_mono_ae h_le_ae
    have h_const : (∫⁻ _ : ℝ, (1 : ENNReal) ∂(ρd d)) = 1 := by
      haveI := hprob
      rw [MeasureTheory.lintegral_const, IsProbabilityMeasure.measure_univ, mul_one]
    simpa [h_const] using h_mono
  have h_toReal_bound : ∀ s : ℝ, 0 < s →
      ((∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂(ρd d)).toReal) ≤ 1 := by
    intro s hs
    have h_le_one := h_int_bound s hs
    have h_ne_top : (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂(ρd d)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top h_le_one
    have h_eq : (1 : ℝ) = (1 : ENNReal).toReal := ENNReal.toReal_one.symm
    rw [h_eq]
    exact (ENNReal.toReal_le_toReal h_ne_top ENNReal.one_ne_top).mpr h_le_one
  have h_toReal_nonneg : ∀ s : ℝ,
      0 ≤ ((∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂(ρd d)).toReal) :=
    fun s => ENNReal.toReal_nonneg
  have hL_le_one := h_toReal_bound 1 zero_lt_one
  have hL_nonneg := h_toReal_nonneg 1
  by_cases hd_eq : d = 1
  · subst hd_eq
    exact le_refl _
  · have hd_gt : 1 < d := lt_of_le_of_ne hd1 (Ne.symm hd_eq)
    have h_one_div_lt_one : (1 : ℝ) / d < 1 := (div_lt_one hd_pos).mpr hd_gt
    have h_sub_pos : 0 < (1 : ℝ) - 1 / d := by linarith
    have hR_pos : 0 < f d * (1 - 1 / d) := mul_pos hfd_pos h_sub_pos
    have hA_nonneg : 0 ≤ f d - f 1 := by
      by_contra h_neg
      push_neg at h_neg
      have h_le_zero :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_lt h_neg) hL_nonneg
      rw [heq1] at h_le_zero
      linarith
    have hR_le_A : f d * (1 - 1 / d) ≤ f d - f 1 := by
      have h1 := mul_le_mul_of_nonneg_left hL_le_one hA_nonneg
      rw [mul_one] at h1
      rw [heq1] at h1
      exact h1
    have hexpand : f d * (1 - 1 / d) = f d - f d / d := by ring
    have h_le : f 1 ≤ f d / d := by
      have h := hR_le_A
      rw [hexpand] at h
      linarith
    have h_fd_div_pos : 0 < f d / d := div_pos hfd_pos hd_pos
    have h_one_div_le : 1 / (f d / d) ≤ 1 / f 1 :=
      one_div_le_one_div_of_le hf1_pos h_le
    rw [one_div_div] at h_one_div_le
    exact h_one_div_le
