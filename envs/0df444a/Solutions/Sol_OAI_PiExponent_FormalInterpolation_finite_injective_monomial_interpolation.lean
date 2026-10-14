-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_injective_monomial_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T08:58:13.522329+00:00
-- url     : https://prove2.me/submissions/520c969d-f88c-4890-b025-18ce152871f2

import Mathlib.Algebra.MvPolynomial.Basic

theorem solution
    {alpha sigma R : Type*} [Fintype alpha] [DecidableEq sigma] [CommSemiring R]
    (e : alpha -> Finsupp sigma Nat) (he : Function.Injective e) (x : alpha -> R) :
    Exists fun P : MvPolynomial sigma R =>
      And (forall a : alpha, P.coeff (e a) = x a)
        (P.support ⊆ Finset.univ.image e) := by
  classical
  refine ⟨∑ a : alpha, MvPolynomial.monomial (e a) (x a), ?_, ?_⟩
  · intro a
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b hb hba
      simp [he.ne hba]
    · intro ha
      exact (ha (Finset.mem_univ a)).elim
  · intro d hd
    have hs := MvPolynomial.support_sum (s := Finset.univ)
      (f := fun a : alpha => MvPolynomial.monomial (e a) (x a))
    have hd' : d ∈ Finset.univ.biUnion fun a : alpha =>
        (MvPolynomial.monomial (e a) (x a)).support := hs hd
    rcases Finset.mem_biUnion.mp hd' with ⟨a, ha, hmem⟩
    have hde : d = e a := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hmem)
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, hde.symm⟩
