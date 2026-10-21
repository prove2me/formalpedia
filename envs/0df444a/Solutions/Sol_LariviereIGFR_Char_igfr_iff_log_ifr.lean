-- Prove2me | solution 1 for LariviereIGFR.Char.igfr_iff_log_ifr
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:57:57.869415+00:00
-- url     : https://prove2.me/submissions/2bd2702d-6f3c-4820-a3e4-e684dc6b9696

import Mathlib
import Definitions.Def_LariviereIGFR_Char_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory LariviereIGFR.Char

theorem mu_Iic_zero (μ : Measure ℝ) (φ : ℝ → ℝ) (hnn : μ (Set.Iio 0) = 0)
    (hφ : IsRegDensity μ φ) : μ (Set.Iic 0) = 0 := by
  have hac : μ ≪ volume := by
    have h := withDensity_absolutelyContinuous (volume : Measure ℝ) (fun x => ENNReal.ofReal (φ x))
    rw [← hφ.2.1] at h
    exact h
  have h0 : μ {0} = 0 := hac Real.volume_singleton
  rw [← Set.Iio_union_right]
  exact measure_union_null hnn h0

theorem mu_congr_pos (μ : Measure ℝ) (h0 : μ (Set.Iic 0) = 0) {S T : Set ℝ}
    (h : S ∩ Set.Ioi 0 = T ∩ Set.Ioi 0) : μ S = μ T := by
  have key : ∀ S : Set ℝ, μ S = μ (S ∩ Set.Ioi 0) := by
    intro S
    apply le_antisymm
    · calc μ S ≤ μ ((S ∩ Set.Ioi 0) ∪ Set.Iic 0) := by
            apply measure_mono
            intro x hx
            by_cases hx0 : 0 < x
            · exact Or.inl ⟨hx, hx0⟩
            · exact Or.inr (not_lt.1 hx0)
        _ ≤ μ (S ∩ Set.Ioi 0) + μ (Set.Iic 0) := measure_union_le _ _
        _ = μ (S ∩ Set.Ioi 0) := by rw [h0, add_zero]
    · exact measure_mono Set.inter_subset_left
  rw [key S, key T, h]

theorem cdf_log (μ : Measure ℝ) [IsProbabilityMeasure μ] (h0 : μ (Set.Iic 0) = 0) (ξ : ℝ) :
    cdf (μ.map Real.log) ξ = cdf μ (Real.exp ξ) := by
  have : IsProbabilityMeasure (μ.map Real.log) :=
    Measure.isProbabilityMeasure_map Real.measurable_log.aemeasurable
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def,
    Measure.map_apply Real.measurable_log measurableSet_Iic]
  congr 1
  apply mu_congr_pos μ h0
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ioi]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(Real.log_le_iff_le_exp h2).1 h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(Real.log_le_iff_le_exp h2).2 h1, h2⟩

theorem map_log_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ : ℝ → ℝ)
    (h0 : μ (Set.Iic 0) = 0) (hd : μ = volume.withDensity (fun x => ENNReal.ofReal (φ x))) :
    μ.map Real.log = volume.withDensity (fun ξ => ENNReal.ofReal (Real.exp ξ * φ (Real.exp ξ))) := by
  ext A hA
  rw [Measure.map_apply Real.measurable_log hA, withDensity_apply _ hA]
  have hset : Real.log ⁻¹' A ∩ Set.Ioi 0 = Real.exp '' A := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi, Set.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨Real.log x, h1, Real.exp_log h2⟩
    · rintro ⟨ξ, hξ, rfl⟩
      exact ⟨by rwa [Real.log_exp], Real.exp_pos ξ⟩
  have hmeas : MeasurableSet (Real.exp '' A) := by
    rw [← hset]; exact (Real.measurable_log hA).inter measurableSet_Ioi
  have hsub : Real.exp '' A ∩ Set.Ioi 0 = Real.exp '' A := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioi]
    constructor
    · exact fun h => h.1
    · rintro ⟨ξ, _, rfl⟩
      exact ⟨⟨ξ, ‹_›, rfl⟩, Real.exp_pos ξ⟩
  rw [mu_congr_pos μ h0 (T := Real.exp '' A) (by rw [hset, hsub])]
  conv_lhs => rw [hd]
  rw [withDensity_apply _ hmeas,
    lintegral_image_eq_lintegral_abs_deriv_mul hA (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn]
  apply lintegral_congr
  intro x
  rw [abs_of_pos (Real.exp_pos x), ENNReal.ofReal_mul (Real.exp_pos x).le]

theorem isRegDensity_log (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ : ℝ → ℝ)
    (hnn : μ (Set.Iio 0) = 0) (hφ : IsRegDensity μ φ) :
    IsRegDensity (μ.map Real.log) (fun ξ => Real.exp ξ * φ (Real.exp ξ)) := by
  have h0 := mu_Iic_zero μ φ hnn hφ
  refine ⟨?_, map_log_eq μ φ h0 hφ.2.1, ?_, ?_⟩
  · intro x; exact mul_nonneg (Real.exp_pos x).le (hφ.1 _)
  · intro ξ h1 h2
    rw [cdf_log μ h0] at h1 h2
    have hd := hφ.2.2.1 (Real.exp ξ) h1 h2
    have he : HasDerivWithinAt Real.exp (Real.exp ξ) (Set.Ici ξ) ξ :=
      (Real.hasDerivAt_exp ξ).hasDerivWithinAt
    have := hd.comp ξ he (fun x hx => Real.exp_le_exp.2 hx)
    have e : (fun x => cdf (μ.map Real.log) x) = (fun x => cdf μ x) ∘ Real.exp :=
      funext (cdf_log μ h0)
    rw [e]
    exact this.congr_deriv (by ring)
  · intro ξ h
    rw [cdf_log μ h0] at h
    show Real.exp ξ * φ (Real.exp ξ) = 0
    rw [hφ.2.2.2 _ h]
    ring

theorem fr_log (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ : ℝ → ℝ)
    (hnn : μ (Set.Iio 0) = 0) (hφ : IsRegDensity μ φ) (ξ : ℝ) :
    failureRate (μ.map Real.log) (fun ξ => Real.exp ξ * φ (Real.exp ξ)) ξ =
      genFailureRate μ φ (Real.exp ξ) := by
  have h0 := mu_Iic_zero μ φ hnn hφ
  simp only [failureRate, genFailureRate, survival, cdf_log μ h0]
  rw [mul_div_assoc]

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ : ℝ → ℝ)
    (hnn : μ (Set.Iio 0) = 0) (hφ : IsRegDensity μ φ) :
    IsIGFR μ φ ↔ IsIFR (μ.map Real.log) (fun ξ => Real.exp ξ * φ (Real.exp ξ)) := by
  have h0 := mu_Iic_zero μ φ hnn hφ
  have hfr := fr_log μ φ hnn hφ
  have hcdf0 : ∀ x, x ≤ 0 → cdf μ x = 0 := by
    intro x hx
    apply le_antisymm _ (cdf_nonneg μ x)
    rw [cdf_eq_real, measureReal_def]
    have : μ (Set.Iic x) = 0 := measure_mono_null (Set.Iic_subset_Iic.2 hx) h0
    simp [this]
  have hg0 : ∀ x, x ≤ 0 → genFailureRate μ φ x = 0 := by
    intro x hx
    unfold genFailureRate failureRate
    rw [hφ.2.2.2 x (hcdf0 x hx)]
    simp
  have hgnn : ∀ x, 0 < x → 0 ≤ genFailureRate μ φ x := by
    intro x hx
    unfold genFailureRate failureRate survival
    exact mul_nonneg hx.le (div_nonneg (hφ.1 x) (by linarith [cdf_le_one μ x]))
  constructor
  · intro h ξ1 hξ1 ξ2 hξ2 hle
    simp only [Set.mem_setOf_eq] at hξ1 hξ2
    rw [cdf_log μ h0] at hξ1 hξ2
    rw [hfr, hfr]
    exact h hξ1 hξ2 (Real.exp_le_exp.2 hle)
  · intro h x hx y hy hxy
    simp only [Set.mem_setOf_eq] at hx hy
    rcases le_or_gt x 0 with hx0 | hx0
    · rw [hg0 x hx0]
      rcases le_or_gt y 0 with hy0 | hy0
      · rw [hg0 y hy0]
      · exact hgnn y hy0
    · have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
      have hxm : Real.log x ∈ {ξ | cdf (μ.map Real.log) ξ < 1} := by
        simp only [Set.mem_setOf_eq]
        rw [cdf_log μ h0, Real.exp_log hx0]
        exact hx
      have hym : Real.log y ∈ {ξ | cdf (μ.map Real.log) ξ < 1} := by
        simp only [Set.mem_setOf_eq]
        rw [cdf_log μ h0, Real.exp_log hy0]
        exact hy
      have := h hxm hym (Real.log_le_log hx0 hxy)
      rw [hfr, hfr, Real.exp_log hx0, Real.exp_log hy0] at this
      exact this
