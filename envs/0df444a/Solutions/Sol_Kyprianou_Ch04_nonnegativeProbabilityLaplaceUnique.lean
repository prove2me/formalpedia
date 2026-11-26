-- Prove2me | solution 1 for Kyprianou.Ch04.nonnegativeProbabilityLaplaceUnique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:46:16.364421+00:00
-- url     : https://prove2.me/submissions/4850eeed-d6c5-4f1b-bc83-0ddbaa1a24b5

import Mathlib
import Theorems.Thm_AvramDividend_Classical_measure_eq_of_pos_mgf_on_ray
open MeasureTheory Set Filter
open scoped ENNReal
set_option autoImplicit false

/-- Nonnegative probability measures are identified by all positive Laplace transforms. -/
theorem solution (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hm : mu (Iio 0) = 0) (hn : nu (Iio 0) = 0)
    (hEq : ∀ s : ℝ, 0 < s →
      (∫ x, Real.exp (-s*x) ∂mu) = ∫ x, Real.exp (-s*x) ∂nu) :
    mu = nu := by
  let R : ℝ → ℝ := fun x => -x
  have hR : Measurable R := measurable_neg
  let a := mu.map R
  let b := nu.map R
  let : IsProbabilityMeasure a := Measure.isProbabilityMeasure_map hR.aemeasurable
  let : IsProbabilityMeasure b := Measure.isProbabilityMeasure_map hR.aemeasurable
  have hInt (v : Measure ℝ) [IsProbabilityMeasure v] (hv : v (Iio 0) = 0)
      (s : ℝ) (hs : 0 < s) : Integrable (fun x => Real.exp (s*x)) (v.map R) := by
    let : IsProbabilityMeasure (v.map R) := Measure.isProbabilityMeasure_map hR.aemeasurable
    have hnull : (v.map R) (Ioi 0) = 0 := by
      rw [Measure.map_apply hR measurableSet_Ioi]
      convert hv using 2
      ext x; simp [R]
    have hae : ∀ᵐ x ∂(v.map R), x ≤ 0 := by
      rw [ae_iff]
      have he : {x : ℝ | ¬ x ≤ 0} = Ioi 0 := by ext x; simp
      rw [he]
      exact hnull
    apply (integrable_const (1 : ℝ)).mono (by fun_prop)
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.exp_pos _).le,Real.norm_eq_abs,abs_one]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hs.le hx)
  have hE : a = b := by
    apply AvramDividend.Classical.measure_eq_of_pos_mgf_on_ray (hInt mu hm) (hInt nu hn)
    intro s hs
    have hmeas : AEStronglyMeasurable (fun x : ℝ => Real.exp (s*x)) a := by fun_prop
    have hmeas' : AEStronglyMeasurable (fun x : ℝ => Real.exp (s*x)) b := by fun_prop
    rw [integral_map hR.aemeasurable hmeas,integral_map hR.aemeasurable hmeas']
    simpa only [R,mul_neg,neg_mul] using hEq s hs
  have hback (v : Measure ℝ) : (v.map R).map R = v := by
    rw [Measure.map_map hR hR]
    simp [R,Function.comp_def]
  exact (hback mu).symm.trans ((congrArg (Measure.map R) hE).trans (hback nu))
