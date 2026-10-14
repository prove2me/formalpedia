-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_column_monomial_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T05:46:10.478668+00:00
-- url     : https://prove2.me/submissions/4b6cb07e-c93c-47cd-8a85-c0e158b5979a

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (w0 : Real) (w : Fin m → Real) (H : Real)
    (x : InterpolationMatrix.Column w0 w H → Complex) :
    ∃ P : MvPolynomial (Fin (m + 1)) Complex,
      (∀ c : InterpolationMatrix.Column w0 w H,
        P.coeff (InterpolationMatrix.exponentVector c.1) = x c) ∧
      P.support ⊆ Finset.univ.image
        (fun c : InterpolationMatrix.Column w0 w H =>
          InterpolationMatrix.exponentVector c.1) := by
  classical
  let C := InterpolationMatrix.Column w0 w H
  let e : C → (Fin (m + 1) →₀ Nat) := fun c =>
    InterpolationMatrix.exponentVector c.1
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    exact Finsupp.equivFunOnFinite.symm.injective hab
  let P : MvPolynomial (Fin (m + 1)) Complex :=
    ∑ c : C, MvPolynomial.monomial (e c) (x c)
  refine ⟨P, ?_, ?_⟩
  · intro c
    change P.coeff (e c) = x c
    simp only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single c]
    · simp
    · intro d hd hdc
      have hne : e d ≠ e c := fun h => hdc (he h)
      simp [hne]
    · intro hc
      exact (hc (Finset.mem_univ c)).elim
  · change P.support ⊆ Finset.univ.image e
    apply Finset.Subset.trans (MvPolynomial.support_sum)
    intro a ha
    rcases Finset.mem_biUnion.mp ha with ⟨c, -, hmem⟩
    have hsingle : (MvPolynomial.monomial (e c) (x c)).support ⊆ {e c} :=
      MvPolynomial.support_monomial_subset
    have heq : a = e c := by simpa using hsingle hmem
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ c, heq.symm⟩
