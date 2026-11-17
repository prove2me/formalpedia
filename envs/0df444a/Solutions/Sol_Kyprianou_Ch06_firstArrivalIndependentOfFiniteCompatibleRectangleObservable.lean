-- Prove2me | solution 1 for Kyprianou.Ch06.firstArrivalIndependentOfFiniteCompatibleRectangleObservable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:35:23.020813+00:00
-- url     : https://prove2.me/submissions/98e6379d-84d8-4149-82e2-c684f483eda2

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfFiniteCompatibleRectangleObservable
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
    (m p : Nat) (starts stops : Fin m → NNReal)
    (B : Fin m → Set E)
    (hValid : ∀ i, starts i ≤ stops i ∧
      MeasurableSet (B i) ∧ n (B i) < ⊤)
    (hAB : ∀ i, Disjoint A (B i))
    (hSep : ∀ i j : Fin m, i ≠ j →
      stops i ≤ starts j ∨ stops j ≤ starts i ∨
      Disjoint (B i) (B j))
    (t : NNReal) (Y : Omega → Fin p → Nat)
    (f : (Fin m → Nat) → Fin p → Nat)
    (hAe : ∀ᵐ omega ∂P,
      Y omega = f (fun i =>
        N omega (stops i) (B i) - N omega (starts i) (B i)))
    (levels : Fin p → Nat) :
    P {omega | (t : WithTop NNReal) <
      sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
        {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
      Y omega = levels} =
    P {omega | (t : WithTop NNReal) <
      sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
        {v : NNReal | 0 < v ∧ 0 < N omega v A})} *
      P {omega | Y omega = levels} := by
  let D : Set Omega := {omega | Y omega = levels}
  have hJoint : ∀ r : NNReal,
      P ({omega | N omega r A = 0} ∩ D) =
      P {omega | N omega r A = 0} * P D := by
    intro r
    have h :=
      Kyprianou.Ch06.zeroACountIndependentOfFiniteCompatibleRectangleObservable
        P n N hPPP A hA hFA m p starts stops B
        hValid hAB hSep r Y f hAe levels
    simpa only [D, Set.inter_def, Set.mem_inter_iff,
      Set.mem_setOf_eq] using h
  have h :=
    Kyprianou.Ch06.firstArrivalIndependentOfEventFromZeroCountIndependence
      P n N A firstMark hPPP hA hFA hMark D hJoint t
  simpa only [D, Set.inter_def, Set.mem_inter_iff,
    Set.mem_setOf_eq] using h
