-- Prove2me | solution 1 for Kyprianou.Ch06.outsideMarkBooleanCountFamily
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:30:03.477713+00:00
-- url     : https://prove2.me/submissions/3cd00897-8185-4164-8ac5-2fc5ee0abd4f

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_outsideBooleanAtomFiniteEnumeration
import Theorems.Thm_Kyprianou_Ch06_finiteDisjointMarkedCountAdditivityAe
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (m : Nat) (B : Fin m → Set E)
    (hB : ∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) :
    ∃ (a : Nat) (mark : Fin a → Set E)
      (selected : Fin m → Finset (Fin a)),
      (∀ j, MeasurableSet (mark j) ∧ n (mark j) < ⊤ ∧
        Disjoint A (mark j)) ∧
      (∀ j l : Fin a, j ≠ l → Disjoint (mark j) (mark l)) ∧
      (∀ᵐ omega ∂P, ∀ i : Fin m, ∀ t : NNReal,
        N omega t (B i) =
          ∑ j ∈ selected i, N omega t (mark j)) := by
  classical
  obtain ⟨a, mark, selected, hFacts, hMarks, hCover⟩ :=
    Kyprianou.Ch06.outsideBooleanAtomFiniteEnumeration
      n A m B hB
  have hSpatial : ∀ i : Fin m, ∀ᵐ omega ∂P,
      ∀ t : NNReal, N omega t (B i) =
        ∑ j ∈ selected i, N omega t (mark j) := by
    intro i
    have hPair : ∀ j ∈ selected i, ∀ l ∈ selected i,
        j ≠ l → Disjoint (mark j) (mark l) := by
      intro j _ l _ hne
      exact hMarks j l hne
    have hAdd :=
      Kyprianou.Ch06.finiteDisjointMarkedCountAdditivityAe
        P n N hPPP mark (selected i) hPair
    filter_upwards [hAdd] with omega h
    intro t
    exact (congrArg (N omega t) (hCover i).symm).trans (h t)
  have hAll : ∀ᵐ omega ∂P,
      ∀ i : Fin m, ∀ t : NNReal,
        N omega t (B i) =
          ∑ j ∈ selected i, N omega t (mark j) :=
    Filter.eventually_all.2 hSpatial
  exact ⟨a, mark, selected, hFacts, hMarks, hAll⟩
