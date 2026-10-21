-- Prove2me | solution 1 for OAI.PiExponent.WeightedDivision.monomial_representatives_of_wellFounded_relations
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:22:21.739989+00:00
-- url     : https://prove2.me/submissions/f6978c94-93e6-4592-9835-fbb442bb17f3

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset
import Theorems.Thm_OAI_PiExponent_WeightedDivision_monomial_representatives_of_wellFounded_relations_unit

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
    (u : ι →₀ ℕ) (c : R) :
    ∃ Q : MvPolynomial ι R,
      MvPolynomial.monomial u c - Q ∈ J ∧ ∀ v ∈ Q.support, A v := by
  obtain ⟨Q, hQJ, hQA⟩ :=
    OAI.PiExponent.WeightedDivision.monomial_representatives_of_wellFounded_relations_unit
      r hr J A hrel u
  refine ⟨c • Q, ?_, ?_⟩
  · have h := J.mul_mem_left (MvPolynomial.C c) hQJ
    rw [mul_sub, MvPolynomial.C_mul_monomial, mul_one, MvPolynomial.C_mul'] at h
    exact h
  · intro v hv
    exact hQA v (MvPolynomial.support_smul.subset hv)
