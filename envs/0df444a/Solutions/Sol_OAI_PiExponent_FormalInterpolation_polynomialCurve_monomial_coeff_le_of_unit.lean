-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.polynomialCurve_monomial_coeff_le_of_unit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:32:01.304888+00:00
-- url     : https://prove2.me/submissions/0cae9dfe-8b70-40b5-8bb3-21b8b02b326a

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData

open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (a : Fin d →₀ Nat) (c : Complex) :
    max 0 (-(polynomialCurveOrder nu
      (MvPolynomial.aeval x (MvPolynomial.monomial a c)) : Real)) ≤
    max 0 (-(polynomialCurveOrder nu
      (MvPolynomial.aeval x (MvPolynomial.monomial a (1 : Complex))) : Real)) := by
  by_cases hc : c = 0
  · subst hc
    simp [polynomialCurveOrder, AddValuation.map_zero]
  · have : MvPolynomial.monomial a c =
        MvPolynomial.C c * MvPolynomial.monomial a (1 : Complex) := by
      rw [MvPolynomial.C_mul_monomial, mul_one]
    rw [this, map_mul, MvPolynomial.aeval_C]
    unfold polynomialCurveOrder
    rw [AddValuation.map_mul, nu.2.1 c hc, zero_add]
