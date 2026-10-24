-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_monomial_quotient_coordinate_class_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:59:39.720594+00:00
-- url     : https://prove2.me/submissions/f1715100-15a8-4e2c-831b-31bdf279cc17

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_class_integral

open scoped BigOperators

theorem solution (d : Nat) (N : Fin d → Nat) (hN : ∀ i, 0 < N i) (i : Fin d) : IsIntegral ℂ (Ideal.Quotient.mk (Ideal.span (Set.range (fun j : Fin d => (MvPolynomial.X j : MvPolynomial (Fin d) ℂ) ^ N j))) (MvPolynomial.X i)) := by
  apply OAI.PiExponent.FormalInterpolation.coordinate_class_integral <;> assumption
