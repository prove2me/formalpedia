-- Prove2me | solution 1 for Kyprianou.Ch06.zeroACountIndependentOfThreeOrderedRepeatedCountsAllLevels
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:25:26.034905+00:00
-- url     : https://prove2.me/submissions/83d72c45-df69-44a1-ae45-55a2cbf224e8

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfThreeOrderedRepeatedCumulativeCounts
import Theorems.Thm_Kyprianou_Ch06_threeOrderedDecreasingMarkedCountCylinderNull
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
    (r s t u : NNReal) (hst : s ≤ t) (htu : t ≤ u)
    (k l q : Nat) :
    P {omega | N omega r A = 0 ∧
      N omega s B = k ∧ N omega t B = l ∧ N omega u B = q} =
    P {omega | N omega r A = 0} *
      P {omega | N omega s B = k ∧
        N omega t B = l ∧ N omega u B = q} := by
  by_cases hGood : k ≤ l ∧ l ≤ q
  · exact
      Kyprianou.Ch06.zeroACountIndependentOfThreeOrderedRepeatedCumulativeCounts
        P n N hPPP A B hA hB hAB hFA hFB
        r s t u hst htu k l q hGood.1 hGood.2
  · have hBad : l < k ∨ q < l := by omega
    have hNull :=
      Kyprianou.Ch06.threeOrderedDecreasingMarkedCountCylinderNull
        P n N hPPP B s t u hst htu k l q hBad
    have hSub :
        {omega | N omega r A = 0 ∧
          N omega s B = k ∧ N omega t B = l ∧
          N omega u B = q} ⊆
        {omega | N omega s B = k ∧
          N omega t B = l ∧ N omega u B = q} := by
      intro omega h
      exact h.2
    have hJointNull :
        P {omega | N omega r A = 0 ∧
          N omega s B = k ∧ N omega t B = l ∧
          N omega u B = q} = 0 := by
      have hle := measure_mono (μ := P) hSub
      rw [hNull] at hle
      exact le_antisymm hle bot_le
    rw [hJointNull,hNull]
    simp
