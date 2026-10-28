-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_sections_finite_witness_20261023_14
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T08:38:21.002961+00:00
-- url     : https://prove2.me/submissions/9bcf6b59-a088-4270-a279-ce80eb596939

import Mathlib

open scoped BigOperators

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (s D : Nat)
    (hpoint : ∀ (x : Fin d → Complex), (∃ i : Fin d, x i ≠ 0) →
      ∃ p : MvPolynomial (Fin d) Complex,
        p ∈ I ^ s ∧
        (∀ a ∈ p.support,
          ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
        MvPolynomial.eval x
          (MvPolynomial.weightedHomogeneousComponent
            (fun k => (w k : ℚ)) (D : ℚ) p) ≠ 0) :
    ∃ m : Nat, ∃ g : Fin m → MvPolynomial (Fin d) Complex,
      (∀ j, g j ∈ I ^ s) ∧
      (∀ j, ∀ a ∈ (g j).support,
        ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
      (∀ (x : Fin d → Complex),
        (∀ (j : Fin m), MvPolynomial.eval x
          (MvPolynomial.weightedHomogeneousComponent
            (fun k => (w k : ℚ)) (D : ℚ) (g j)) = 0) →
          ∀ (i : Fin d), x i = 0) := by
  classical
  let P : MvPolynomial (Fin d) Complex → Prop := fun p => p ∈ I ^ s ∧
    ∀ a ∈ p.support, ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)
  let T : Set (MvPolynomial (Fin d) Complex) := {t | ∃ p, P p ∧
    MvPolynomial.weightedHomogeneousComponent (fun k => (w k : ℚ)) (D : ℚ) p = t}
  have hfg : (Ideal.span T).FG := IsNoetherian.noetherian _
  obtain ⟨S, hST, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset T).1 hfg
  have hc : ∀ t : S, ∃ p, P p ∧
      MvPolynomial.weightedHomogeneousComponent (fun k => (w k : ℚ)) (D : ℚ) p = t :=
    fun t => hST t.2
  choose g hg using hc
  refine ⟨S.card, fun j => g (S.equivFin.symm j), fun j => (hg _).1.1, fun j => (hg _).1.2, ?_⟩
  intro x hx i
  by_contra hxi
  obtain ⟨p, hp1, hp2, hp3⟩ := hpoint x ⟨i, hxi⟩
  apply hp3
  have hmem : MvPolynomial.weightedHomogeneousComponent (fun k => (w k : ℚ)) (D : ℚ) p ∈
      Ideal.span T := Ideal.subset_span ⟨p, ⟨hp1, hp2⟩, rfl⟩
  have hspan' : Ideal.span T = Ideal.span (S : Set (MvPolynomial (Fin d) Complex)) := hspan
  rw [hspan'] at hmem
  have hle : Ideal.span (S : Set (MvPolynomial (Fin d) Complex)) ≤
      RingHom.ker (MvPolynomial.eval x) := by
    rw [Ideal.span_le]
    intro t ht
    have h1 := hx (S.equivFin ⟨t, ht⟩)
    simp only [Equiv.symm_apply_apply] at h1
    rw [(hg _).2] at h1
    exact h1
  exact hle hmem
