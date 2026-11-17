-- Prove2me | solution 1 for Kyprianou.Ch06.markedPoissonArrivalOutsideThreeOrMoreOverlapping
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T11:57:48.536767+00:00
-- url     : https://prove2.me/submissions/72fd4e50-a870-4411-8acf-46f03ee14271
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfFiniteOutsideZeroCountsSameTime
import Theorems.Thm_Kyprianou_Ch06_markedPoissonArrivalOutsideThreeOrMoreNonUniformZero
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
    (∀ (m : Nat) (times : Fin m → NNReal)
      (B : Fin m → Set E) (counts : Fin m → Nat) (t : NNReal),
      3 ≤ m →
      (∃ i j : Fin m, i ≠ j ∧ ¬ Disjoint (B i) (B j)) →
      (∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) →
        P {omega | (t : WithTop NNReal) < sigma omega ∧
          (∀ i : Fin m, N omega (times i) (B i) = counts i)} =
          P {omega | (t : WithTop NNReal) < sigma omega} *
            P {omega |
              ∀ i : Fin m, N omega (times i) (B i) = counts i}) := by
  dsimp only
  intro m times B counts t hLarge hOverlap hB
  by_cases hUniform : (∃ u : NNReal, ∀ i : Fin m, times i = u) ∧
      (∀ i : Fin m, counts i = 0)
  · obtain ⟨⟨u, ht⟩, hc⟩ := hUniform
    have hTime : times = fun _ : Fin m => u := funext ht
    have hCount : counts = fun _ : Fin m => 0 := funext hc
    subst times
    subst counts
    exact
      Kyprianou.Ch06.firstArrivalIndependentOfFiniteOutsideZeroCountsSameTime
        P n N A firstMark hPPP hA hFinite hMark m B hB t u
  · exact
      Kyprianou.Ch06.markedPoissonArrivalOutsideThreeOrMoreNonUniformZero
        P n N A firstMark hPPP hA hFinite hMark
        m times B counts t hLarge hOverlap hUniform hB