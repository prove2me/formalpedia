-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.polynomialCurve_eval_value_nat
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T18:13:53.782145+00:00
-- url     : https://prove2.me/submissions/576ef13b-b333-40b9-bff3-c262e7d16abc

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Algebra.MvPolynomial.Eval
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurve_eval_nonneg
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_withTopInt_nonneg_finite_nat

open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (f : MvPolynomial (Fin d) Complex)
    (hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i))
    (hne : MvPolynomial.aeval x f ≠ 0) :
    ∃ k : Nat, nu.1 (MvPolynomial.aeval x f) = ((k : Int) : WithTop Int) := by
  apply OAI.PiExponent.FormalInterpolation.withTopInt_nonneg_finite_nat
  · exact (AddValuation.ne_top_iff nu.1).2 hne
  · exact OAI.PiExponent.FormalInterpolation.polynomialCurve_eval_nonneg nu x f hchart