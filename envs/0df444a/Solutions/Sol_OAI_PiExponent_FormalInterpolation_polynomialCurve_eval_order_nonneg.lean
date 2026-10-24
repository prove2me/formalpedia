-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.polynomialCurve_eval_order_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T18:08:45.067974+00:00
-- url     : https://prove2.me/submissions/558de73f-bbcf-4380-9c7d-95ee366072cb

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Algebra.MvPolynomial.Eval
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurve_eval_value_nat

open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (f : MvPolynomial (Fin d) Complex)
    (hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i))
    (hne : MvPolynomial.aeval x f ≠ 0) :
    ∃ k : Nat,
      nu.1 (MvPolynomial.aeval x f) = ((k : Int) : WithTop Int) ∧
      polynomialCurveOrder nu (MvPolynomial.aeval x f) = (k : Int) := by
  obtain ⟨k, hk⟩ :=
    OAI.PiExponent.FormalInterpolation.polynomialCurve_eval_value_nat
      nu x f hchart hne
  refine ⟨k, hk, ?_⟩
  simpa [polynomialCurveOrder, hk]