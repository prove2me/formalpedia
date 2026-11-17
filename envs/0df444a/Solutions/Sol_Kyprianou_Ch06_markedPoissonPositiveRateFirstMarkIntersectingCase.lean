-- Prove2me | solution 1 for Kyprianou.Ch06.markedPoissonPositiveRateFirstMarkIntersectingCase
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:51:43.712977+00:00
-- url     : https://prove2.me/submissions/e1c5c7df-d8ae-453b-a6e9-deb5588118f7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_positiveFirstMarkSupersetACase
import Theorems.Thm_Kyprianou_Ch06_positiveFirstMarkProperOverlapCase
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
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
    (0 < n A →
      ∀ (m : Nat) (times : Fin m → NNReal)
      (B : Fin m → Set E) (counts : Fin m → Nat)
      (t : NNReal) (C : Set E),
      ¬ Disjoint C A →
      (∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) →
      MeasurableSet C →
        P {omega | firstMark omega ∈ (some '' C) ∧
          (t : WithTop NNReal) < sigma omega ∧
          (∀ i : Fin m, N omega (times i) (B i) = counts i)} =
          ((n (C ∩ A)) / n A) *
            P {omega | (t : WithTop NNReal) < sigma omega ∧
              (∀ i : Fin m, N omega (times i) (B i) = counts i)}) := by
  dsimp only
  intro hRate m times B counts t C hOverlap hB hMeasC
  by_cases hSuperset : A ⊆ C
  · exact
      Kyprianou.Ch06.positiveFirstMarkSupersetACase
        P n N A firstMark hPPP hA hFinite hMark
        hRate m times B counts t C hSuperset hB hMeasC
  · exact
      Kyprianou.Ch06.positiveFirstMarkProperOverlapCase
        P n N A firstMark hPPP hA hFinite hMark
        hRate m times B counts t C hOverlap hSuperset hB hMeasC