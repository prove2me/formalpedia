-- Prove2me | solution 1 for LariviereIGFR.Char.genFailureRate_scale
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:00:01.186763+00:00
-- url     : https://prove2.me/submissions/9f542280-8b2b-4440-ac55-226b6ec3f2d9

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

theorem cdf_scale (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ) (hc : 0 < c) (ξ : ℝ) :
    cdf (μ.map (fun x => c * x)) ξ = cdf μ (ξ / c) := by
  have hm : Measurable (fun x : ℝ => c * x) := by fun_prop
  have : IsProbabilityMeasure (μ.map (fun x => c * x)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def,
    Measure.map_apply hm measurableSet_Iic]
  congr 2
  ext x
  simp only [Set.mem_preimage, Set.mem_Iic]
  rw [le_div_iff₀ hc, mul_comm]

theorem map_scale_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hd : μ = volume.withDensity (fun x => ENNReal.ofReal (φ x))) :
    μ.map (fun x => c * x) = volume.withDensity (fun ξ => ENNReal.ofReal (φ (ξ / c) / c)) := by
  have hm : Measurable (fun x : ℝ => c * x) := by fun_prop
  have hsurj : Function.Surjective (fun x : ℝ => c * x) := fun y => ⟨y / c, by field_simp⟩
  ext A hA
  have hAB : (fun x : ℝ => c * x) '' ((fun x : ℝ => c * x) ⁻¹' A) = A := Set.image_preimage_eq A hsurj
  rw [Measure.map_apply hm hA, withDensity_apply _ hA]
  conv_rhs => rw [← hAB]
  rw [lintegral_image_eq_lintegral_abs_deriv_mul (hm hA)
    (fun x _ => ((hasDerivAt_id' x).const_mul c).hasDerivWithinAt)
    (mul_right_injective₀ hc.ne').injOn]
  conv_lhs => rw [hd, withDensity_apply _ (hm hA)]
  apply lintegral_congr
  intro x
  have e1 : c * x / c = x := by field_simp
  rw [e1, mul_one, abs_of_pos hc, ← ENNReal.ofReal_mul hc.le]
  congr 1
  field_simp

theorem isRegDensity_scale (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ : ℝ → ℝ)
    (hφ : IsRegDensity μ φ) (c : ℝ) (hc : 0 < c) :
    IsRegDensity (μ.map (fun x => c * x)) (fun ξ => φ (ξ / c) / c) := by
  refine ⟨?_, map_scale_eq μ φ c hc hφ.2.1, ?_, ?_⟩
  · intro x; exact div_nonneg (hφ.1 _) hc.le
  · intro ξ h1 h2
    rw [cdf_scale μ c hc] at h1 h2
    have hd := hφ.2.2.1 (ξ / c) h1 h2
    have he : HasDerivWithinAt (fun x : ℝ => x / c) (1 / c) (Set.Ici ξ) ξ :=
      ((hasDerivAt_id' ξ).div_const c).hasDerivWithinAt
    have := hd.comp ξ he (fun x hx => div_le_div_of_nonneg_right hx hc.le)
    have e : (fun x => cdf (μ.map (fun x => c * x)) x) = (fun x => cdf μ x) ∘ (fun x => x / c) :=
      funext (cdf_scale μ c hc)
    rw [e]
    exact this.congr_deriv (by ring)
  · intro ξ h
    rw [cdf_scale μ c hc] at h
    show φ (ξ / c) / c = 0
    rw [hφ.2.2.2 _ h]
    simp

theorem gfr_scale (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (ξ : ℝ) :
    genFailureRate (μ.map (fun x => c * x)) (fun ξ => φ (ξ / c) / c) ξ =
      genFailureRate μ φ (ξ / c) := by
  simp only [genFailureRate, failureRate, survival, cdf_scale μ c hc]
  ring

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ : ℝ → ℝ)
    (hnn : μ (Set.Iio 0) = 0) (hφ : IsRegDensity μ φ)
    (c : ℝ) (hc : 0 < c) :
    (∀ ξ : ℝ, cdf (μ.map (fun x => c * x)) ξ = cdf μ (ξ / c)) ∧
      IsRegDensity (μ.map (fun x => c * x)) (fun ξ => φ (ξ / c) / c) ∧
      ∀ ξ : ℝ, genFailureRate (μ.map (fun x => c * x)) (fun ξ => φ (ξ / c) / c) ξ =
        genFailureRate μ φ (ξ / c) :=
  ⟨cdf_scale μ c hc, isRegDensity_scale μ φ hφ c hc, gfr_scale μ φ c hc⟩
