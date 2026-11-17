-- Prove2me | solution 1 for Kyprianou.Ch06.firstArrivalIndependentOfRepeatedOutsideMarkTimeVector
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:17:04.743201+00:00
-- url     : https://prove2.me/submissions/ba59eb42-00c6-4b72-a809-11e216e5710f

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfRepeatedOutsideMarkTimeVector
import Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfEventFromZeroCountIndependence
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A) (hFA : n A < ⊤)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (B : Set E) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (hFB : n B < ⊤)
    (m : Nat) (u t : NNReal) (levels : Fin m → Nat) :
    P {omega | (t : WithTop NNReal) <
      sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
        {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
      ∀ i : Fin m, N omega u B = levels i} =
    P {omega | (t : WithTop NNReal) <
      sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
        {v : NNReal | 0 < v ∧ 0 < N omega v A})} *
      P {omega | ∀ i : Fin m, N omega u B = levels i} := by
  let D : Set Omega := {omega |
    ∀ i : Fin m, N omega u B = levels i}
  have hJoint : ∀ s : NNReal,
      P ({omega | N omega s A = 0} ∩ D) =
      P {omega | N omega s A = 0} * P D := by
    intro s
    have h :=
      Kyprianou.Ch06.zeroACountIndependentOfRepeatedOutsideMarkTimeVector
        P n N hPPP A B hA hB hAB hFA hFB m s u levels
    simpa only [D, Set.inter_def, Set.mem_inter_iff,
      Set.mem_setOf_eq] using h
  have h :=
    Kyprianou.Ch06.firstArrivalIndependentOfEventFromZeroCountIndependence
      P n N A firstMark hPPP hA hFA hMark D hJoint t
  simpa only [D, Set.inter_def, Set.mem_inter_iff,
    Set.mem_setOf_eq] using h
