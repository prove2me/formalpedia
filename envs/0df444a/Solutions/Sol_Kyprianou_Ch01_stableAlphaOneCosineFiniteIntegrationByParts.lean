-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneCosineFiniteIntegrationByParts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T09:09:53.447395+00:00
-- url     : https://prove2.me/submissions/799c6d87-0c99-44a5-bbf3-11adf1c7192e

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineQuotientDerivative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
open scoped Interval
set_option autoImplicit false
/-! Exact cosine-to-sine reduction on any compact positive interval. -/
theorem solution
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, (1 - Real.cos x) / x ^ 2) =
      (∫ x in a..b, Real.sin x / x) -
        ((1 - Real.cos b) / b - (1 - Real.cos a) / a) := by
  have hnonzero : ∀ x ∈ uIcc a b, x ≠ 0 := by
    intro x hx
    have hx' : x ∈ Icc a b := by
      simpa only [uIcc_of_le hab] using hx
    exact ne_of_gt (lt_of_lt_of_le ha hx'.1)
  have hcontinuousSin : ContinuousOn (fun x : ℝ => Real.sin x / x) (uIcc a b) := by
    apply (Real.continuous_sin.continuousOn.div continuous_id.continuousOn
      hnonzero).congr
    intro x hx
    rfl
  have hcontinuousCos :
      ContinuousOn (fun x : ℝ => (1 - Real.cos x) / x ^ 2) (uIcc a b) := by
    have hdenom : ∀ x ∈ uIcc a b, x ^ 2 ≠ 0 := by
      intro x hx
      exact pow_ne_zero _ (hnonzero x hx)
    apply ((continuousOn_const.sub Real.continuous_cos.continuousOn).div
      (continuous_id.continuousOn.pow 2) hdenom).congr
    intro x hx
    rfl
  have hsin := hcontinuousSin.intervalIntegrable (μ := volume)
  have hcos := hcontinuousCos.intervalIntegrable (μ := volume)
  have hderiv : ∀ x ∈ uIcc a b,
      HasDerivAt (fun y : ℝ => (1 - Real.cos y) / y)
        (Real.sin x / x - (1 - Real.cos x) / x ^ 2) x := by
    intro x hx
    exact Kyprianou.Ch01.stableAlphaOneCosineQuotientDerivative x (hnonzero x hx)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((hcontinuousSin.sub hcontinuousCos).intervalIntegrable (μ := volume))
  rw [intervalIntegral.integral_sub hsin hcos] at hftc
  linarith
