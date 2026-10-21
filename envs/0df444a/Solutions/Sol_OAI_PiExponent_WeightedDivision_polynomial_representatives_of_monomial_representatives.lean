-- Prove2me | solution 1 for OAI.PiExponent.WeightedDivision.polynomial_representatives_of_monomial_representatives
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T08:40:23.176991+00:00
-- url     : https://prove2.me/submissions/92da92e6-74d4-4251-88d5-08a8f9c6f996

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem solution
    {ι : Type*} {R : Type*} [DecidableEq ι] [CommRing R]
    (J : Ideal (MvPolynomial ι R))
    (A : (ι →₀ ℕ) → Prop)
    (hmono : ∀ (u : ι →₀ ℕ) (c : R),
      ∃ Q : MvPolynomial ι R,
        MvPolynomial.monomial u c - Q ∈ J ∧ ∀ v ∈ Q.support, A v)
    (P : MvPolynomial ι R) :
    ∃ Q : MvPolynomial ι R,
      P - Q ∈ J ∧ ∀ u ∈ Q.support, A u := by
  induction P using MvPolynomial.induction_on' with
  | monomial u c =>
      exact hmono u c
  | add p q hp hq =>
      obtain ⟨Qp, hJp, hAp⟩ := hp
      obtain ⟨Qq, hJq, hAq⟩ := hq
      refine ⟨Qp + Qq, ?_, ?_⟩
      · have hdiff : (p + q) - (Qp + Qq) = (p - Qp) + (q - Qq) := by ring
        rw [hdiff]
        exact J.add_mem hJp hJq
      · intro u hu
        have hu' : u ∈ Qp.support ∪ Qq.support :=
          MvPolynomial.support_add hu
        rcases Finset.mem_union.mp hu' with h | h
        · exact hAp u h
        · exact hAq u h