-- Prove2me | solution 1 for Kyprianou.Ch06.markedPoissonArrivalOutsideTwoOverlapDifferentObservation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T11:57:56.587204+00:00
-- url     : https://prove2.me/submissions/e971a784-f196-4b38-8d8a-fb4a2be1a86c

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfNestedOutsideZeroCounts
import Theorems.Thm_Kyprianou_Ch06_markedPoissonArrivalOutsideTwoOverlapRemainingBeyondNestedZero
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
    (∀ (times : Fin 2 → NNReal)
      (B : Fin 2 → Set E) (counts : Fin 2 → Nat) (t : NNReal),
      ¬ Disjoint (B 0) (B 1) →
      ¬ (B 0 = B 1 ∧ times 0 = times 1) →
      (∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) →
        P {omega | (t : WithTop NNReal) < sigma omega ∧
          (∀ i : Fin 2, N omega (times i) (B i) = counts i)} =
          P {omega | (t : WithTop NNReal) < sigma omega} *
            P {omega |
              ∀ i : Fin 2, N omega (times i) (B i) = counts i}) := by
  dsimp only
  intro times B counts t hOverlap hDistinct hB
  by_cases hNested : counts 0 = 0 ∧ counts 1 = 0 ∧
      ((B 0 ⊆ B 1 ∧ times 0 ≤ times 1) ∨
       (B 1 ⊆ B 0 ∧ times 1 ≤ times 0))
  · obtain ⟨hk0, hk1, h01 | h10⟩ := hNested
    · have hA1 : Disjoint A (B 1) := by
        apply Set.disjoint_left.mpr
        intro x hxA hxB
        exact (hB 1).2.1 hxB hxA
      have hResult :=
        Kyprianou.Ch06.firstArrivalIndependentOfNestedOutsideZeroCounts
          P n N A firstMark hPPP hA hFinite hMark
          (B 0) (B 1) (hB 1).1 hA1 (hB 1).2.2
          h01.1 (times 0) (times 1) t h01.2
      simpa [Fin.forall_fin_two, hk0, hk1] using hResult
    · have hA0 : Disjoint A (B 0) := by
        apply Set.disjoint_left.mpr
        intro x hxA hxB
        exact (hB 0).2.1 hxB hxA
      have hResult :=
        Kyprianou.Ch06.firstArrivalIndependentOfNestedOutsideZeroCounts
          P n N A firstMark hPPP hA hFinite hMark
          (B 1) (B 0) (hB 0).1 hA0 (hB 0).2.2
          h10.1 (times 1) (times 0) t h10.2
      simpa [Fin.forall_fin_two, hk0, hk1, and_comm] using hResult
  · exact
      Kyprianou.Ch06.markedPoissonArrivalOutsideTwoOverlapRemainingBeyondNestedZero
        P n N A firstMark hPPP hA hFinite hMark
        times B counts t hOverlap hDistinct hNested hB