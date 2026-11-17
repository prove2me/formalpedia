-- Prove2me | solution 1 for Kyprianou.Ch06.firstArrivalIndependentOfThreeArbitraryOutsideMarksSameTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:49:03.980687+00:00
-- url     : https://prove2.me/submissions/8444bbdd-35f8-4bf7-8a54-fb9ef3977e96

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfThreeArbitraryOutsideMarksSameTime
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
    (B C D : Set E) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hAD : Disjoint A D)
    (hFB : n B < ⊤) (hFC : n C < ⊤)
    (hFD : n D < ⊤)
    (t u : NNReal) (k l q : Nat) :
    P {omega | (t : WithTop NNReal) <
      sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
        {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
      N omega u B = k ∧ N omega u C = l ∧
      N omega u D = q} =
    P {omega | (t : WithTop NNReal) <
      sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
        {v : NNReal | 0 < v ∧ 0 < N omega v A})} *
      P {omega | N omega u B = k ∧
        N omega u C = l ∧ N omega u D = q} := by
  let Dobs : Set Omega := {omega |
    N omega u B = k ∧ N omega u C = l ∧
    N omega u D = q}
  have hJoint : ∀ r : NNReal,
      P ({omega | N omega r A = 0} ∩ Dobs) =
      P {omega | N omega r A = 0} * P Dobs := by
    intro r
    have h :=
      Kyprianou.Ch06.zeroACountIndependentOfThreeArbitraryOutsideMarksSameTime
        P n N hPPP A B C D hA hB hC hD hAB hAC hAD
        hFA hFB hFC hFD r u k l q
    simpa only [Dobs,Set.inter_def,Set.mem_inter_iff,
      Set.mem_setOf_eq,and_assoc] using h
  have h :=
    Kyprianou.Ch06.firstArrivalIndependentOfEventFromZeroCountIndependence
      P n N A firstMark hPPP hA hFA hMark Dobs hJoint t
  simpa only [Dobs,Set.inter_def,Set.mem_inter_iff,
    Set.mem_setOf_eq,and_assoc] using h
