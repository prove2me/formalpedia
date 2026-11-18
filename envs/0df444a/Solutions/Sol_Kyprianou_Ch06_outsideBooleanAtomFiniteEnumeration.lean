-- Prove2me | solution 1 for Kyprianou.Ch06.outsideBooleanAtomFiniteEnumeration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:26:05.431003+00:00
-- url     : https://prove2.me/submissions/975eef2a-2b42-401e-b390-d5d61ffda738

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_finiteBooleanMarkAtomsMeasurableDisjointCover
import Theorems.Thm_Kyprianou_Ch06_nonemptyMarkPatternAtomFiniteIntensity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {E : Type} [MeasurableSpace E] (n : Measure E) (A : Set E)
    (m : Nat) (B : Fin m → Set E)
    (hB : ∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) :
    ∃ (a : Nat) (mark : Fin a → Set E)
      (selected : Fin m → Finset (Fin a)),
      (∀ j, MeasurableSet (mark j) ∧ n (mark j) < ⊤ ∧
        Disjoint A (mark j)) ∧
      (∀ j l : Fin a, j ≠ l → Disjoint (mark j) (mark l)) ∧
      (∀ i, (⋃ j ∈ selected i, mark j) = B i) := by
  classical
  let beta : Type := {S : Finset (Fin m) // S.Nonempty}
  let a : Nat := Fintype.card beta
  let encode : Fin a ≃ beta := (Fintype.equivFin beta).symm
  let pattern : Fin a → Finset (Fin m) := fun j => (encode j).val
  let mark : Fin a → Set E := fun j =>
    {x : E | ∀ i : Fin m, (x ∈ B i ↔ i ∈ pattern j)}
  obtain ⟨hAtomMeas, hAtomPair, hAtomCover⟩ :=
    Kyprianou.Ch06.finiteBooleanMarkAtomsMeasurableDisjointCover
      m B (fun i => (hB i).1)
  have hMarkFacts : ∀ j : Fin a,
      MeasurableSet (mark j) ∧ n (mark j) < ⊤ := by
    intro j
    obtain ⟨i, hi⟩ := (encode j).property
    exact ⟨hAtomMeas (pattern j),
      Kyprianou.Ch06.nonemptyMarkPatternAtomFiniteIntensity
        n m B (fun i => (hB i).2.2) (pattern j) i hi⟩
  have hOutside : ∀ j : Fin a, Disjoint A (mark j) := by
    intro j
    obtain ⟨i, hi⟩ := (encode j).property
    apply Set.disjoint_left.mpr
    intro x hxA hxMark
    have hxBi : x ∈ B i := (hxMark i).2 hi
    exact (hB i).2.1 hxBi hxA
  have hMarks : ∀ j l : Fin a, j ≠ l →
      Disjoint (mark j) (mark l) := by
    intro j l hne
    apply hAtomPair
    intro hEq
    apply hne
    apply encode.injective
    exact Subtype.ext hEq
  let selected : Fin m → Finset (Fin a) := fun i =>
    Finset.univ.filter (fun j => i ∈ pattern j)
  have hUnion (i : Fin m) :
      (⋃ j ∈ selected i, mark j) = B i := by
    ext x
    constructor
    · intro hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨j, hj, hxMark⟩ := hx
      have hi : i ∈ pattern j :=
        (Finset.mem_filter.mp hj).2
      exact (hxMark i).2 hi
    · intro hxi
      obtain ⟨S, hS, hi⟩ := (hAtomCover i x).mp hxi
      let b : beta := ⟨S, ⟨i, hi⟩⟩
      let j : Fin a := encode.symm b
      have hp : pattern j = S := by
        change (encode j).val = S
        change (encode (encode.symm b)).val = S
        simp [b]
      apply Set.mem_iUnion.mpr
      refine ⟨j, ?_⟩
      apply Set.mem_iUnion.mpr
      refine ⟨?_, ?_⟩
      · simp [selected, hp, hi]
      · change ∀ t : Fin m, (x ∈ B t ↔ t ∈ pattern j)
        simpa [hp] using hS
  refine ⟨a, mark, selected, ?_, hMarks, hUnion⟩
  intro j
  exact ⟨(hMarkFacts j).1, (hMarkFacts j).2, hOutside j⟩
