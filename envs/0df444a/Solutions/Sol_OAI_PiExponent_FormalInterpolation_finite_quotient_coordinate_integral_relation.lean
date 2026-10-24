-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_quotient_coordinate_integral_relation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:32:07.006296+00:00
-- url     : https://prove2.me/submissions/6414172e-afb9-405c-85d1-964418035817

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_quotient_coordinate_integral_relation_v3

open scoped BigOperators

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) ℂ))
    (hquot : Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ I))
    (i : Fin d) :
    ∃ p : Polynomial ℂ, p ≠ 0 ∧
      Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X i) p ∈ I := by
  apply OAI.PiExponent.FormalInterpolation.finite_quotient_coordinate_integral_relation_v3 <;> assumption
