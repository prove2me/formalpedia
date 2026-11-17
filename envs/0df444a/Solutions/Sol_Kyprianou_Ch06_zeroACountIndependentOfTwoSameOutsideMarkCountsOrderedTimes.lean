-- Prove2me | solution 1 for Kyprianou.Ch06.zeroACountIndependentOfTwoSameOutsideMarkCountsOrderedTimes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:15:13.281239+00:00
-- url     : https://prove2.me/submissions/746cd383-f26f-4287-9702-f8d20df551d1

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_zeroAMarkedIncrementIndependentOfConsecutiveOutsideIncrements
import Theorems.Thm_Kyprianou_Ch06_eventIndependenceOfAlmostSureEquivalentEvents
import Theorems.Thm_Kyprianou_Ch06_orderedSameMarkCountsEquivalentToIncrementCountsAe
import Theorems.Thm_Kyprianou_Ch06_orderedSameMarkCountCylinderNullIfDescending
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (hFA : n A < ⊤) (hFB : n B < ⊤)
    (r s t : NNReal) (hst : s ≤ t) (k l : Nat) :
    P {omega | N omega r A = 0 ∧
      N omega s B = k ∧ N omega t B = l} =
    P {omega | N omega r A = 0} *
    P {omega | N omega s B = k ∧ N omega t B = l} := by
  have hFirstAe : ∀ᵐ omega ∂P,
      (N omega r A = 0) ↔
      (N omega r A - N omega 0 A = 0) := by
    filter_upwards [hPPP.2.1] with omega hw
    have hZero := hw.1 A
    omega
  by_cases hkl : k ≤ l
  · have hOutsideAe :=
      Kyprianou.Ch06.orderedSameMarkCountsEquivalentToIncrementCountsAe
        P n N hPPP B s t hst k l hkl
    have hRect :=
      Kyprianou.Ch06.zeroAMarkedIncrementIndependentOfConsecutiveOutsideIncrements
        P n N hPPP A B hA hB hAB hFA hFB r s t hst k (l-k)
    have hTransfer :=
      Kyprianou.Ch06.eventIndependenceOfAlmostSureEquivalentEvents
        P {omega | N omega r A = 0}
          {omega | N omega r A - N omega 0 A = 0}
          {omega | N omega s B = k ∧ N omega t B = l}
          {omega | N omega s B - N omega 0 B = k ∧
            N omega t B - N omega s B = l-k}
          hFirstAe hOutsideAe
    exact hTransfer hRect
  · have hDescending : l < k := Nat.lt_of_not_ge hkl
    have hNull :=
      Kyprianou.Ch06.orderedSameMarkCountCylinderNullIfDescending
        P n N hPPP B s t hst k l hDescending
    have hSub :
        {omega | N omega r A = 0 ∧
          N omega s B = k ∧ N omega t B = l} ⊆
        {omega | N omega s B = k ∧ N omega t B = l} := by
      intro omega h
      exact h.2
    have hJointNull :
        P {omega | N omega r A = 0 ∧
          N omega s B = k ∧ N omega t B = l} = 0 := by
      have hle := measure_mono (μ := P) hSub
      rw [hNull] at hle
      exact le_antisymm hle bot_le
    rw [hJointNull, hNull]
    simp
