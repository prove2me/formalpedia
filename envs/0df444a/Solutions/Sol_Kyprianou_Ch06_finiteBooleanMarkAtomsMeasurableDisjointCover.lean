-- Prove2me | solution 1 for Kyprianou.Ch06.finiteBooleanMarkAtomsMeasurableDisjointCover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:58:39.869603+00:00
-- url     : https://prove2.me/submissions/0bfb8e6d-8012-459a-b3af-809eaaf7d8fe

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

theorem solution
    {E : Type} [MeasurableSpace E] (m : Nat)
    (B : Fin m → Set E) (hB : ∀ i, MeasurableSet (B i)) :
    (∀ S : Finset (Fin m),
      MeasurableSet {x : E | ∀ i : Fin m,
        (x ∈ B i ↔ i ∈ S)}) ∧
    (∀ S T : Finset (Fin m), S ≠ T →
      Disjoint
        {x : E | ∀ i : Fin m, (x ∈ B i ↔ i ∈ S)}
        {x : E | ∀ i : Fin m, (x ∈ B i ↔ i ∈ T)}) ∧
    (∀ (i : Fin m) (x : E), x ∈ B i ↔
      ∃ S : Finset (Fin m),
        (∀ j : Fin m, (x ∈ B j ↔ j ∈ S)) ∧ i ∈ S) := by
  classical
  constructor
  · intro S
    have hMeas : ∀ i : Fin m,
        MeasurableSet {x : E | (x ∈ B i ↔ i ∈ S)} := by
      intro i
      by_cases hi : i ∈ S
      · simpa [hi] using hB i
      · have hEq :
            {x : E | (x ∈ B i ↔ i ∈ S)} = (B i)ᶜ := by
          ext x
          simp [hi]
        rw [hEq]
        exact (hB i).compl
    simpa only [Set.setOf_forall] using MeasurableSet.iInter hMeas
  constructor
  · intro S T hNe
    apply Set.disjoint_left.mpr
    intro x hxS hxT
    apply hNe
    ext i
    exact (hxS i).symm.trans (hxT i)
  · intro i x
    constructor
    · intro hi
      let S : Finset (Fin m) := Finset.univ.filter (fun j => x ∈ B j)
      refine ⟨S, ?_, ?_⟩
      · intro j
        simp [S]
      · simpa [S] using hi
    · rintro ⟨S, hS, hi⟩
      exact (hS i).mpr hi
