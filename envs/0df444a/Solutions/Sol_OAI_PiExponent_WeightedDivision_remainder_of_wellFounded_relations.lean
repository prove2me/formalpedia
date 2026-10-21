-- Prove2me | solution 1 for OAI.PiExponent.WeightedDivision.remainder_of_wellFounded_relations
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T07:55:29.008987+00:00
-- url     : https://prove2.me/submissions/5cd1a29a-e7f6-4769-b35c-14ab9420f74d

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset
import Theorems.Thm_OAI_PiExponent_WeightedDivision_monomial_representatives_of_wellFounded_relations
import Theorems.Thm_OAI_PiExponent_WeightedDivision_polynomial_representatives_of_monomial_representatives

open scoped BigOperators

theorem solution
    {ι : Type*} {R : Type*} [DecidableEq ι] [CommRing R]
    (r : (ι →₀ ℕ) → (ι →₀ ℕ) → Prop)
    (hr : WellFounded r)
    (J : Ideal (MvPolynomial ι R))
    (A : (ι →₀ ℕ) → Prop)
    (hrel : ∀ u, ¬ A u →
      ∃ G : MvPolynomial ι R, G ∈ J ∧
        ∀ v ∈ (MvPolynomial.monomial u (1 : R) - G).support, r v u)
    (P : MvPolynomial ι R) :
    ∃ Q : MvPolynomial ι R,
      P - Q ∈ J ∧ ∀ u ∈ Q.support, A u := by
  apply OAI.PiExponent.WeightedDivision.polynomial_representatives_of_monomial_representatives
    J A
  intro u c
  exact OAI.PiExponent.WeightedDivision.monomial_representatives_of_wellFounded_relations
    r hr J A hrel u c