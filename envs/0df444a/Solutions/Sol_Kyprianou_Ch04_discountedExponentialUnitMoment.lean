-- Prove2me | solution 1 for Kyprianou.Ch04.discountedExponentialUnitMoment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T07:46:06.236798+00:00
-- url     : https://prove2.me/submissions/b29e6f3e-52e1-4053-9d2e-b0cbeedb15e3

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Remove the deterministic discount at time one. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real) (hZero : ∀ w, X 0 w = 0)
    (beta lam : Real)
    (hM : Martingale (fun (t : NNReal) w =>
      Real.exp (-lam * (t : Real)) * Real.exp (beta * X t w)) F P) :
    Integrable (fun w => Real.exp (beta * X 1 w)) P ∧
      (∫ w, Real.exp (beta * X 1 w) ∂P) = Real.exp lam := by
  have hi := (hM.integrable (1 : NNReal)).const_mul (Real.exp lam)
  have hm := hM.setIntegral_eq (show (0 : NNReal) ≤ 1 by positivity)
    (s := Set.univ) MeasurableSet.univ
  have he : (1 : Real) = Real.exp (-lam) * ∫ w, Real.exp (beta * X 1 w) ∂P := by
    simpa [hZero, integral_const_mul] using hm
  constructor
  · simpa [← mul_assoc, ← Real.exp_add] using hi
  · calc
      _ = Real.exp lam * (Real.exp (-lam) * ∫ w, Real.exp (beta * X 1 w) ∂P) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
      _ = _ := by rw [← he, mul_one]
