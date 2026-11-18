-- Prove2me | solution 2 for Kyprianou.Ch06.markedPoissonArrivalOutsideIndependenceMany
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:50:34.184178+00:00
-- url     : https://prove2.me/submissions/48d83e69-86f8-4603-b8fc-35f7eaa0be99

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_outsideCountVectorCompatibleRectangleRepresentation
import Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfFiniteCompatibleRectangleObservable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch06

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A)
    (hFinite : n A < ⊤)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x})) :
    let sigma : Omega → WithTop NNReal := fun omega =>
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A})
    (∀ (m : Nat) (times : Fin m → NNReal)
      (B : Fin m → Set E) (counts : Fin m → Nat) (t : NNReal),
      2 ≤ m →
      (∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) →
        P {omega | (t : WithTop NNReal) < sigma omega ∧
          (∀ i : Fin m, N omega (times i) (B i) = counts i)} =
          P {omega | (t : WithTop NNReal) < sigma omega} *
            P {omega |
              ∀ i : Fin m, N omega (times i) (B i) = counts i}) := by
  dsimp only
  intro m times B counts t hm hB
  obtain ⟨k, starts, stops, D, hValid, hAB, hSep, f, hAe⟩ :=
    Kyprianou.Ch06.outsideCountVectorCompatibleRectangleRepresentation
      P n N A hPPP hA hFinite m times B hB
  have h :=
    Kyprianou.Ch06.firstArrivalIndependentOfFiniteCompatibleRectangleObservable
      P n N A firstMark hPPP hA hFinite hMark
      k m starts stops D hValid hAB hSep t
      (fun omega : Omega =>
        fun i : Fin m => N omega (times i) (B i))
      f hAe counts
  simpa only [funext_iff, Set.setOf_forall,
    Set.mem_setOf_eq] using h
