-- Prove2me | solution 1 for Kyprianou.Ch06.firstArrivalIndependentOfThreeRepeatedOutsideMarkCountsAllTimes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:29:29.135471+00:00
-- url     : https://prove2.me/submissions/ff732574-5391-4329-b835-ea213a7ffe16

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfThreeRepeatedMarkCountsAllTimes
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
    (s t u v : NNReal) (k l q : Nat) :
    P {omega | (v : WithTop NNReal) <
      sInf ((fun w : NNReal => (w : WithTop NNReal)) ''
        {w : NNReal | 0 < w ∧ 0 < N omega w A}) ∧
      N omega s B = k ∧ N omega t B = l ∧ N omega u B = q} =
    P {omega | (v : WithTop NNReal) <
      sInf ((fun w : NNReal => (w : WithTop NNReal)) ''
        {w : NNReal | 0 < w ∧ 0 < N omega w A})} *
      P {omega | N omega s B = k ∧
        N omega t B = l ∧ N omega u B = q} := by
  let D : Set Omega := {omega |
    N omega s B = k ∧ N omega t B = l ∧ N omega u B = q}
  have hJoint : ∀ r : NNReal,
      P ({omega | N omega r A = 0} ∩ D) =
      P {omega | N omega r A = 0} * P D := by
    intro r
    have h :=
      Kyprianou.Ch06.zeroACountIndependentOfThreeRepeatedMarkCountsAllTimes
        P n N hPPP A B hA hB hAB hFA hFB r s t u k l q
    simpa only [D,Set.inter_def,Set.mem_inter_iff,
      Set.mem_setOf_eq,and_assoc] using h
  have h :=
    Kyprianou.Ch06.firstArrivalIndependentOfEventFromZeroCountIndependence
      P n N A firstMark hPPP hA hFA hMark D hJoint v
  simpa only [D,Set.inter_def,Set.mem_inter_iff,
    Set.mem_setOf_eq,and_assoc] using h
