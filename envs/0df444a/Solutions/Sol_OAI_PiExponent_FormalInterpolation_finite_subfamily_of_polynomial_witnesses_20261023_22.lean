-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_subfamily_of_polynomial_witnesses_20261023_22
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:06:57.713627+00:00
-- url     : https://prove2.me/submissions/3ccb66dc-880a-4127-92e5-77f908215649

import Mathlib
open scoped BigOperators

theorem solution
    {d : Nat} {α : Type}
    (F : α → MvPolynomial (Fin d) Complex)
    (h : ∀ x : Fin d → Complex,
      (∀ a : α, MvPolynomial.eval x (F a) = 0) →
      ∀ i : Fin d, x i = 0) :
    ∃ m : Nat, ∃ idx : Fin m → α,
      ∀ x : Fin d → Complex,
        (∀ j : Fin m,
          MvPolynomial.eval x (F (idx j)) = 0) →
        ∀ i : Fin d, x i = 0 := by
  classical
  have hfg : (Ideal.span (Set.range F)).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (Set.range F)).mp hfg
  have hpre : ∀ p ∈ s, ∃ a, F a = p := fun p hp => hs hp
  choose g hg using hpre
  refine ⟨s.card, fun j => g (s.equivFin.symm j).1 (s.equivFin.symm j).2, ?_⟩
  intro x hx
  apply h x
  intro a
  have hmem : F a ∈ Ideal.span (↑s : Set (MvPolynomial (Fin d) ℂ)) := by
    have : F a ∈ Ideal.span (Set.range F) := Ideal.subset_span ⟨a, rfl⟩
    have e : Ideal.span (Set.range F) = Ideal.span (↑s : Set (MvPolynomial (Fin d) ℂ)) := hspan
    rwa [e] at this
  have hker : Ideal.span (↑s : Set (MvPolynomial (Fin d) ℂ)) ≤ RingHom.ker (MvPolynomial.eval x) := by
    rw [Ideal.span_le]
    intro p hp
    have := hx (s.equivFin ⟨p, hp⟩)
    simp only [Equiv.symm_apply_apply] at this
    rw [hg p hp] at this
    exact this
  exact hker hmem
