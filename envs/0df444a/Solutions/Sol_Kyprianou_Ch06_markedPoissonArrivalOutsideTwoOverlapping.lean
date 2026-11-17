-- Prove2me | solution 1 for Kyprianou.Ch06.markedPoissonArrivalOutsideTwoOverlapping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:02:55.583709+00:00
-- url     : https://prove2.me/submissions/1f37534c-2031-4d99-b82e-e2ddfde8f304

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfRepeatedOutsideCount
import Theorems.Thm_Kyprianou_Ch06_markedPoissonArrivalOutsideTwoOverlapDifferentObservation
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
      (∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) →
        P {omega | (t : WithTop NNReal) < sigma omega ∧
          (∀ i : Fin 2, N omega (times i) (B i) = counts i)} =
          P {omega | (t : WithTop NNReal) < sigma omega} *
            P {omega |
              ∀ i : Fin 2, N omega (times i) (B i) = counts i}) := by
  dsimp only
  intro times B counts t hOverlap hB
  by_cases hIdent : B 0 = B 1 ∧ times 0 = times 1
  · obtain ⟨hEqB, hEqTime⟩ := hIdent
    have hAB : Disjoint A (B 0) := by
      apply Set.disjoint_left.mpr
      intro x hxA hxB
      exact (hB 0).2.1 hxB hxA
    have hRepeated :=
      Kyprianou.Ch06.firstArrivalIndependentOfRepeatedOutsideCount
        P n N A firstMark hPPP hA hFinite hMark
        (B 0) (hB 0).1 hAB (hB 0).2.2
    dsimp only at hRepeated
    simpa [Fin.forall_fin_two, hEqB, hEqTime] using
      (hRepeated t (times 0) (counts 0) (counts 1))
  · exact
      Kyprianou.Ch06.markedPoissonArrivalOutsideTwoOverlapDifferentObservation
        P n N A firstMark hPPP hA hFinite hMark
        times B counts t hOverlap hIdent hB