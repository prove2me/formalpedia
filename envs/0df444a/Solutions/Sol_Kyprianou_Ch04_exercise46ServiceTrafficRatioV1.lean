-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46ServiceTrafficRatioV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T10:19:34.541604+00:00
-- url     : https://prove2.me/submissions/1c22613e-b96c-40f0-a49e-b4558a37f94b

import Mathlib
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false
theorem solution
    (service : Measure Real) [IsProbabilityMeasure service]
    (hPositive : service (Ioi (0 : Real)) = 1)
    (lambda : Real) (hlambda : 0 < lambda)
    (nu : Measure Real)
    (hInput : nu = ENNReal.ofReal lambda • service.map (fun x : Real => -x))
    (hOverload : 1 < lambda * ∫ y : Real, y ∂service) :
    1 < ∫⁻ y : Real, ENNReal.ofReal (-y) ∂nu := by
  have hi : Integrable (fun y : Real => y) service := by
    by_contra hn
    rw [integral_undef hn, mul_zero] at hOverload
    linarith
  have hp : ∀ᵐ y ∂service, 0 < y := by
    apply (ae_mem_iff_measure_eq measurableSet_Ioi.nullMeasurableSet).mpr
    simpa using hPositive
  have hnn : 0 ≤ᵐ[service] (fun y : Real => y) := hp.mono fun y hy => hy.le
  rw [hInput, lintegral_smul_measure,
    lintegral_map (f := fun y : Real => ENNReal.ofReal (-y))
      (g := fun y : Real => -y) measurable_id.neg.ennreal_ofReal measurable_id.neg]
  simp only [neg_neg, smul_eq_mul]
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnn, ← ENNReal.ofReal_mul hlambda.le]
  exact ENNReal.one_lt_ofReal.mpr hOverload
