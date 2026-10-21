-- Prove2me | solution 1 for OAI.PiExponent.WeightedDivision.monomial_representatives_of_wellFounded_relations_unit
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:32:12.833922+00:00
-- url     : https://prove2.me/submissions/7605317d-4f58-41dc-963a-4cd5f9225267

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset
import Theorems.Thm_OAI_PiExponent_WeightedDivision_finite_support_representatives

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
    (u : ι →₀ ℕ) :
    ∃ Q : MvPolynomial ι R,
      MvPolynomial.monomial u (1 : R) - Q ∈ J ∧ ∀ v ∈ Q.support, A v := by
  let P : (ι →₀ ℕ) → Prop := fun u =>
    ∃ Q : MvPolynomial ι R,
      MvPolynomial.monomial u (1 : R) - Q ∈ J ∧
        ∀ v ∈ Q.support, A v
  have hP : ∀ u, P u := by
    intro x
    induction x using hr.induction with
    | h x ih =>
      by_cases hx : A x
      · refine ⟨MvPolynomial.monomial x (1 : R), by simp, ?_⟩
        intro v hv
        rcases (show x = v ∧ (1 : R) ≠ 0 by simpa using hv) with ⟨hxv, _⟩
        simpa [hxv] using hx
      · obtain ⟨G, hG, hGs⟩ := hrel x hx
        let F := MvPolynomial.monomial x (1 : R) - G
        have hF : ∀ v ∈ F.support,
            ∃ Q : MvPolynomial ι R,
              MvPolynomial.monomial v (1 : R) - Q ∈ J ∧
                ∀ w ∈ Q.support, A w := by
          intro v hv
          exact ih v (hGs v hv)
        obtain ⟨Q, hFQ, hQA⟩ :=
          OAI.PiExponent.WeightedDivision.finite_support_representatives J A F hF
        refine ⟨Q, ?_, hQA⟩
        have hsub : MvPolynomial.monomial x (1 : R) - F ∈ J := by
          simpa [F] using hG
        have hsum : (MvPolynomial.monomial x (1 : R) - F) + (F - Q) ∈ J :=
          J.add_mem hsub hFQ
        convert hsum using 1 <;> ring
  exact hP u