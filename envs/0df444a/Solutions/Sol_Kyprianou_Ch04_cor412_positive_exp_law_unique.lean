-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_positive_exp_law_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:40:38.132598+00:00
-- url     : https://prove2.me/submissions/1a65047e-b40a-45f3-abc6-7880af34c192

import Mathlib
import Theorems.Thm_AvramDividend_Classical_measure_eq_of_pos_mgf_on_ray
import Theorems.Thm_Kyprianou_Ch04_cor412_exp_tilt_transform
open MeasureTheory Set Filter AvramDividend.Classical
open scoped ENNReal
set_option autoImplicit false

/-- Exponential tilting reduces equality of finite positive-ray exponential integrals to probability MGF uniqueness. -/
theorem solution (μ ν : Measure ℝ)
    (hμ : ∀ s : ℝ, 0 < s → (∫⁻ x, ENNReal.ofReal (Real.exp (s*x)) ∂μ) ≠ ⊤)
    (he : ∀ s : ℝ, 0 < s → (∫⁻ x, ENNReal.ofReal (Real.exp (s*x)) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (Real.exp (s*x)) ∂ν)
    (hc0 : (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂μ) ≠ 0) : μ = ν := by
  let c := ∫⁻ x, ENNReal.ofReal (Real.exp x) ∂μ
  have hcT : c ≠ ⊤ := by simpa [c] using hμ 1 (by norm_num)
  have hcν : (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂ν) = c := by
    simpa [c] using (he 1 (by norm_num)).symm
  let f : ℝ → ℝ≥0∞ := fun x => c⁻¹ * ENNReal.ofReal (Real.exp x)
  let μ' := μ.withDensity f
  let ν' := ν.withDensity f
  have hf : Measurable f := measurable_const.mul Real.continuous_exp.measurable.ennreal_ofReal
  have hf0 (x : ℝ) : f x ≠ 0 := mul_ne_zero
    (ENNReal.inv_ne_zero.mpr hcT) (by simp [Real.exp_pos])
  have hfT (x : ℝ) : f x ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hc0) ENNReal.ofReal_ne_top
  have hp (η : Measure ℝ) (hη : (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂η) = c) :
      IsProbabilityMeasure (η.withDensity f) := by
    constructor
    rw [withDensity_apply f MeasurableSet.univ, Measure.restrict_univ]
    change (∫⁻ x, c⁻¹ * ENNReal.ofReal (Real.exp x) ∂η) = 1
    rw [lintegral_const_mul _ Real.continuous_exp.measurable.ennreal_ofReal, hη,
      ENNReal.inv_mul_cancel hc0 hcT]
  let : IsProbabilityMeasure μ' := hp μ rfl
  let : IsProbabilityMeasure ν' := hp ν hcν
  have hi (η : Measure ℝ)
      (hη : ∀ s : ℝ, 0 < s → (∫⁻ x, ENNReal.ofReal (Real.exp (s*x)) ∂η) ≠ ⊤)
      (s : ℝ) (hs : 0 < s) : Integrable (fun x => Real.exp (s*x)) (η.withDensity f) := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      ((measurable_const.mul measurable_id).exp.aestronglyMeasurable)
      (Eventually.of_forall fun x => (Real.exp_pos _).le)).mp
    change (∫⁻ x, ENNReal.ofReal (Real.exp (s*x)) ∂(η.withDensity f)) ≠ ⊤
    exact (Kyprianou.Ch04.cor412_exp_tilt_transform η c⁻¹ s).symm ▸
      ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hc0) (hη (s+1) (by linarith))
  have hν : ∀ s : ℝ, 0 < s → (∫⁻ x, ENNReal.ofReal (Real.exp (s*x)) ∂ν) ≠ ⊤ :=
    fun s hs => he s hs ▸ hμ s hs
  have hEq : μ' = ν' := by
    apply measure_eq_of_pos_mgf_on_ray (hi μ hμ) (hi ν hν)
    intro s hs
    have hm := Kyprianou.Ch04.cor412_exp_tilt_transform μ c⁻¹ s
    have hn := Kyprianou.Ch04.cor412_exp_tilt_transform ν c⁻¹ s
    rw [← ofReal_integral_eq_lintegral_ofReal (hi μ hμ s hs)
      (Eventually.of_forall fun x => (Real.exp_pos _).le)] at hm
    rw [← ofReal_integral_eq_lintegral_ofReal (hi ν hν s hs)
      (Eventually.of_forall fun x => (Real.exp_pos _).le)] at hn
    have heq := hm.trans ((congrArg (fun z => c⁻¹ * z) (he (s+1) (by linarith))).trans hn.symm)
    have hr := congrArg ENNReal.toReal heq
    simpa only [ENNReal.toReal_ofReal (integral_nonneg fun x => (Real.exp_pos _).le)] using hr
  rw [← withDensity_inv_same (μ := μ) hf (Eventually.of_forall hf0) (Eventually.of_forall hfT),
    ← withDensity_inv_same (μ := ν) hf (Eventually.of_forall hf0) (Eventually.of_forall hfT)]
  exact congrArg (fun η : Measure ℝ => η.withDensity (fun x => (f x)⁻¹)) hEq
