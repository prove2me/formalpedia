-- Prove2me | solution 1 for Kyprianou.Ch06.zeroACountIndependentOfTwoOutsideOverlappingCountsSameTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:02:40.929264+00:00
-- url     : https://prove2.me/submissions/191b15fe-cb24-497c-802a-a92ed7b242ff

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_overlapCountCylinderAsFiniteAtomUnionAe
import Theorems.Thm_Kyprianou_Ch06_independentEventOfAeDisjointCountableUnion
import Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfOverlapThreeAtomCounts
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
    (s t : NNReal) (k l : Nat) :
    P {omega | N omega s A = 0 ∧ N omega t B = k ∧
      N omega t C = l} =
    P {omega | N omega s A = 0} *
    P {omega | N omega t B = k ∧ N omega t C = l} := by
  let D : Set Omega := {omega | N omega s A = 0}
  let F : Fin (min k l + 1) → Set Omega := fun q =>
    {omega | N omega t (B \ C) = k - (q : Nat) ∧
      N omega t (C \ B) = l - (q : Nat) ∧
      N omega t (B ∩ C) = (q : Nat)}
  have hDMeas : MeasurableSet D :=
    measurableSet_eq_fun (hPPP.1 s A hA) measurable_const
  have hFMeas : ∀ q, MeasurableSet (F q) := by
    intro q
    exact
      (measurableSet_eq_fun
        (hPPP.1 t (B \ C) (hB.diff hC)) measurable_const).inter
        ((measurableSet_eq_fun
          (hPPP.1 t (C \ B) (hC.diff hB)) measurable_const).inter
          (measurableSet_eq_fun
            (hPPP.1 t (B ∩ C) (hB.inter hC)) measurable_const))
  have hFDisj : Pairwise (fun q r => Disjoint (F q) (F r)) := by
    intro q r hqr
    apply Set.disjoint_left.mpr
    intro omega hq hr
    apply hqr
    apply Fin.ext
    exact hq.2.2.symm.trans hr.2.2
  have hFIndep : ∀ q, P (D ∩ F q) = P D * P (F q) := by
    intro q
    have h3 :=
      Kyprianou.Ch06.zeroACountIndependentOfOverlapThreeAtomCounts
        P n N hPPP A B C hA hB hC hAB hAC
        hFA hFB hFC s t (k-(q:Nat)) (l-(q:Nat)) q
    change P (D ∩ F q) = P D * P (F q) at h3
    exact h3
  have hAtomAe :=
    Kyprianou.Ch06.overlapCountCylinderAsFiniteAtomUnionAe
      P n N hPPP B C t k l
  have hEq : ∀ᵐ omega ∂P,
      (N omega t B = k ∧ N omega t C = l) ↔
      omega ∈ (⋃ q, F q) := by
    filter_upwards [hAtomAe] with omega ha
    simpa [F, Set.mem_iUnion] using ha
  have hIndependent :=
    Kyprianou.Ch06.independentEventOfAeDisjointCountableUnion
      P D {omega | N omega t B = k ∧ N omega t C = l}
      hDMeas F hFMeas hFDisj hFIndep hEq
  change P (D ∩ {omega | N omega t B = k ∧ N omega t C = l}) =
    P D * P {omega | N omega t B = k ∧ N omega t C = l}
  exact hIndependent
