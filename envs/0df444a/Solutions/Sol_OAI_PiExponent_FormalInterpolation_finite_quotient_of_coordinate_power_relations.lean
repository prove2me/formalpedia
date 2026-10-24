-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_quotient_of_coordinate_power_relations
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:53:03.303411+00:00
-- url     : https://prove2.me/submissions/55353d8f-20b0-474f-9a5a-88cd7c118e0e

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_quotient_by_coordinate_powers_a9fbb753_463b_437c_88bf_627d1569d537
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_quotient_of_ideal_le_a9fbb753_463b_437c_88bf_627d1569d537

open scoped BigOperators

theorem solution
    {d : Nat} (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (N : Nat)
    (hpow : ∀ i : Fin d,
      MvPolynomial.monomial (Finsupp.single i N) (1 : ℂ) ∈ Ideal.span (Set.range p)) :
    Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ Ideal.span (Set.range p)) := by
  apply OAI.PiExponent.FormalInterpolation.finite_quotient_of_ideal_le_a9fbb753_463b_437c_88bf_627d1569d537
    (Ideal.span (Set.range (fun i : Fin d =>
      MvPolynomial.monomial (Finsupp.single i N) (1 : ℂ))))
    (Ideal.span (Set.range p))
  · exact Ideal.span_le.mpr (Set.forall_mem_range.mpr hpow)
  · exact OAI.PiExponent.FormalInterpolation.finite_quotient_by_coordinate_powers_a9fbb753_463b_437c_88bf_627d1569d537 N