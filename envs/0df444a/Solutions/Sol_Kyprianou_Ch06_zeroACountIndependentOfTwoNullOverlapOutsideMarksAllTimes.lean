-- Prove2me | solution 1 for Kyprianou.Ch06.zeroACountIndependentOfTwoNullOverlapOutsideMarksAllTimes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:28:19.621332+00:00
-- url     : https://prove2.me/submissions/3b01cb3c-f15e-459b-b4d4-6b461f5243e1

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_nullIntensityOverlapCountsEqualDisjointPartsAe
import Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfTwoDisjointOutsideMarksAllTimes
import Theorems.Thm_Kyprianou_Ch06_eventIndependenceOfAlmostSureEquivalentEvents
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
    (A B C : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hFA : n A < ⊤) (hFB : n B < ⊤) (hFC : n C < ⊤)
    (hNull : n (B ∩ C) = 0)
    (r s t : NNReal) (k l : Nat) :
    P {omega | N omega r A = 0 ∧
      N omega s B = k ∧ N omega t C = l} =
    P {omega | N omega r A = 0} *
    P {omega | N omega s B = k ∧ N omega t C = l} := by
  have hABdiff : Disjoint A (B \ C) := by
    apply Set.disjoint_left.mpr
    intro x hxA hxBC
    exact (Set.disjoint_left.mp hAB) hxA hxBC.1
  have hACdiff : Disjoint A (C \ B) := by
    apply Set.disjoint_left.mpr
    intro x hxA hxCB
    exact (Set.disjoint_left.mp hAC) hxA hxCB.1
  have hBCdisjoint : Disjoint (B \ C) (C \ B) := by
    apply Set.disjoint_left.mpr
    intro x hxBC hxCB
    exact hxBC.2 hxCB.1
  have hFBdiff : n (B \ C) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.diff_subset) hFB
  have hFCdiff : n (C \ B) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.diff_subset) hFC
  have hOutsideEq :
      ∀ᵐ omega ∂P,
        (N omega s B = k ∧ N omega t C = l) ↔
        (N omega s (B \ C) = k ∧ N omega t (C \ B) = l) := by
    filter_upwards
      [Kyprianou.Ch06.nullIntensityOverlapCountsEqualDisjointPartsAe
        P n N hPPP B C hB hC hNull] with omega he
    rw [(he s).1,(he t).2]
  have hFact :=
    Kyprianou.Ch06.zeroACountIndependentOfTwoDisjointOutsideMarksAllTimes
      P n N hPPP A (B \ C) (C \ B)
      hA (hB.diff hC) (hC.diff hB)
      hABdiff hACdiff hBCdisjoint hFA hFBdiff hFCdiff
      r s t k l
  have hTransfer :=
    Kyprianou.Ch06.eventIndependenceOfAlmostSureEquivalentEvents
      P {omega | N omega r A = 0}
        {omega | N omega r A = 0}
        {omega | N omega s B = k ∧ N omega t C = l}
        {omega | N omega s (B \ C) = k ∧
          N omega t (C \ B) = l}
        (Filter.Eventually.of_forall (fun _ => Iff.rfl))
        hOutsideEq
  have hFactor :
      P ({omega | N omega r A = 0} ∩
         {omega | N omega s (B \ C) = k ∧
           N omega t (C \ B) = l}) =
      P {omega | N omega r A = 0} *
      P {omega | N omega s (B \ C) = k ∧
        N omega t (C \ B) = l} := by
    simpa only [Set.inter_def, Set.mem_inter_iff, Set.mem_setOf_eq,
      and_assoc] using hFact
  have hResult := hTransfer hFactor
  simpa only [Set.inter_def, Set.mem_inter_iff,
    Set.mem_setOf_eq, and_assoc] using hResult
