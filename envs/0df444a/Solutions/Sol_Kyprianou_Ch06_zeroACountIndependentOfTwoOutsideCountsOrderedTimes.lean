-- Prove2me | solution 1 for Kyprianou.Ch06.zeroACountIndependentOfTwoOutsideCountsOrderedTimes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:42:00.071536+00:00
-- url     : https://prove2.me/submissions/380c419e-0f28-4fc3-944c-4726e46135e2

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_fourOverlapIndexedAtomFamilyMeasurable
import Theorems.Thm_Kyprianou_Ch06_fourOverlapIndexedAtomFamilyPairwiseDisjoint
import Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfIndexedFourOverlapAtomEvent
import Theorems.Thm_Kyprianou_Ch06_differentTimesOverlapCountCylinderAsFiniteAtomUnionAe
import Theorems.Thm_Kyprianou_Ch06_independentEventOfAeDisjointCountableUnion
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
    (r s t : NNReal) (hst : s ≤ t) (k l : Nat) :
    P {omega | N omega r A = 0 ∧
      N omega s B = k ∧ N omega t C = l} =
    P {omega | N omega r A = 0} *
      P {omega | N omega s B = k ∧ N omega t C = l} := by
  let D : Set Omega := {omega | N omega r A = 0}
  let G : Set Omega :=
    {omega | N omega s B = k ∧ N omega t C = l}
  let F : Fin (k+1) × Fin (l+1) → Set Omega := fun i =>
    {omega | (i.1 : Nat)+(i.2 : Nat) ≤ l ∧
      N omega s (B \ C) = k-(i.1 : Nat) ∧
      N omega s (B ∩ C) = (i.1 : Nat) ∧
      N omega s (C \ B) = (i.2 : Nat) ∧
      N omega t C - N omega s C = l-(i.1 : Nat)-(i.2 : Nat)}
  have hDMeas : MeasurableSet D :=
    measurableSet_eq_fun (hPPP.1 r A hA) measurable_const
  have hFMeas :=
    Kyprianou.Ch06.fourOverlapIndexedAtomFamilyMeasurable
      P n N hPPP B C hB hC s t k l
  have hFDisj :=
    Kyprianou.Ch06.fourOverlapIndexedAtomFamilyPairwiseDisjoint
      N B C s t k l
  have hFIndep : ∀ i, P (D ∩ F i) = P D * P (F i) := by
    intro i
    have h :=
      Kyprianou.Ch06.zeroACountIndependentOfIndexedFourOverlapAtomEvent
        P n N hPPP A B C hA hB hC hAB hAC hFA hFB hFC
        r s t hst k l i
    change P (D ∩ F i) = P D * P (F i) at h
    exact h
  have hAtomAe :=
    Kyprianou.Ch06.differentTimesOverlapCountCylinderAsFiniteAtomUnionAe
      P n N hPPP B C s t hst k l
  have hAe : ∀ᵐ omega ∂P,
      (omega ∈ G) ↔ omega ∈ ⋃ i, F i := hAtomAe
  have h :=
    Kyprianou.Ch06.independentEventOfAeDisjointCountableUnion
      P D G hDMeas F hFMeas hFDisj hFIndep hAe
  change P (D ∩ G) = P D * P G
  exact h
