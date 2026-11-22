-- Prove2me | solution 1 for MultiplicationOperator.isLUB_norm_smul_L2_eq_norm_Linfty
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:51:42.367664+00:00
-- url     : https://prove2.me/submissions/37b19924-019a-478e-99d0-bcb60cb17444

import Mathlib

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

theorem solution
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (φ : Lp ℂ ∞ μ) :
    IsLUB {r : ℝ | ∃ g : Lp ℂ 2 μ, ‖g‖ ≤ 1 ∧ r = ‖φ • g‖} ‖φ‖ := by
  constructor
  · rintro r ⟨g, hg, rfl⟩
    calc ‖φ • g‖ ≤ ‖φ‖ * ‖g‖ := Lp.norm_smul_le φ g
      _ ≤ ‖φ‖ * 1 := mul_le_mul_of_nonneg_left hg (norm_nonneg _)
      _ = ‖φ‖ := mul_one _
  · intro b hb
    have hb0 : 0 ≤ b :=
      (norm_nonneg _).trans (hb (show ‖φ • (0 : Lp ℂ 2 μ)‖ ∈ _ from ⟨0, by simp, rfl⟩))
    by_contra hlt'
    have hlt : b < ‖φ‖ := lt_of_not_ge hlt'
    set c : ℝ := (b + ‖φ‖) / 2 with hc
    have hbc : b < c := by linarith
    have hcφ : c < ‖φ‖ := by linarith
    have hc0 : 0 < c := by linarith
    set A : Set α := {x | c < ‖φ x‖} with hA
    have hAm : MeasurableSet A :=
      measurableSet_lt measurable_const (Lp.stronglyMeasurable φ).measurable.norm
    have hApos : 0 < μ A := by
      rw [pos_iff_ne_zero]
      intro h0
      have hae : ∀ᵐ x ∂μ, ‖φ x‖ ≤ c := by
        rw [ae_iff]
        simpa [hA, not_le] using h0
      have : ‖φ‖ ≤ c := by
        rw [Lp.norm_def, eLpNorm_exponent_top]
        exact ENNReal.toReal_le_of_le_ofReal hc0.le (eLpNormEssSup_le_of_ae_bound hae)
      linarith
    obtain ⟨B, hBm, hBA, hBpos, hBfin⟩ := Measure.exists_subset_measure_lt_top hAm hApos
    have hBne : μ B ≠ ∞ := hBfin.ne
    have hBreal : 0 < μ.real B := ENNReal.toReal_pos hBpos.ne' hBne
    set s : ℝ := μ.real B ^ (1 / (2 : ℝ≥0∞).toReal) with hs
    have hspos : 0 < s := Real.rpow_pos_of_pos hBreal _
    set a : ℝ := s⁻¹ with ha
    have ha0 : 0 < a := inv_pos.mpr hspos
    let g : Lp ℂ 2 μ := indicatorConstLp 2 hBm hBne ((a : ℝ) : ℂ)
    let h : Lp ℂ 2 μ := indicatorConstLp 2 hBm hBne ((c * a : ℝ) : ℂ)
    have hg : ‖g‖ = 1 := by
      simp only [g]
      rw [norm_indicatorConstLp (by norm_num) (by norm_num), Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ha0, ← hs, ha, inv_mul_cancel₀ hspos.ne']
    have hh : ‖h‖ = c := by
      simp only [h]
      rw [norm_indicatorConstLp (by norm_num) (by norm_num), Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (mul_pos hc0 ha0), ← hs, ha, mul_assoc, inv_mul_cancel₀ hspos.ne', mul_one]
    have hle : ‖h‖ ≤ ‖φ • g‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hBm) (hμs := hBne)
          (c := ((c * a : ℝ) : ℂ)),
        indicatorConstLp_coeFn (p := 2) (hs := hBm) (hμs := hBne) (c := ((a : ℝ) : ℂ)),
        Lp.coeFn_lpSMul (r := 2) φ g] with x hx1 hx2 hx3
      rw [hx1, hx3, Pi.smul_apply', show (g : α → ℂ) x = _ from hx2]
      by_cases hxB : x ∈ B
      · simp only [Set.indicator_of_mem hxB, smul_eq_mul, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos ha0, abs_of_pos hc0]
        have : c < ‖φ x‖ := hBA hxB
        exact mul_le_mul_of_nonneg_right this.le ha0.le
      · simp [Set.indicator_of_notMem hxB]
    have hmem := hb (show ‖φ • g‖ ∈ _ from ⟨g, hg.le, rfl⟩)
    linarith
