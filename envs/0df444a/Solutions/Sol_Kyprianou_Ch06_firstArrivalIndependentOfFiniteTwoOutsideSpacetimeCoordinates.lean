-- Prove2me | solution 1 for Kyprianou.Ch06.firstArrivalIndependentOfFiniteTwoOutsideSpacetimeCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:32:30.774896+00:00
-- url     : https://prove2.me/submissions/21dc4ca9-11d7-4cb9-bea0-5df8a81891a1

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfFiniteTwoOutsideSpacetimeCoordinates
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
    (B C : Set E) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hFB : n B < ⊤) (hFC : n C < ⊤)
    (m : Nat) (s t v : NNReal)
    (times : Fin m → NNReal) (marks : Fin m → Set E)
    (hSelect : ∀ i : Fin m,
      (times i = s ∧ marks i = B) ∨
      (times i = t ∧ marks i = C))
    (levels : Fin m → Nat) :
    P {omega | (v : WithTop NNReal) <
      sInf ((fun w : NNReal => (w : WithTop NNReal)) ''
        {w : NNReal | 0 < w ∧ 0 < N omega w A}) ∧
      ∀ i : Fin m, N omega (times i) (marks i) = levels i} =
    P {omega | (v : WithTop NNReal) <
      sInf ((fun w : NNReal => (w : WithTop NNReal)) ''
        {w : NNReal | 0 < w ∧ 0 < N omega w A})} *
      P {omega | ∀ i : Fin m,
        N omega (times i) (marks i) = levels i} := by
  let D : Set Omega := {omega |
    ∀ i : Fin m, N omega (times i) (marks i) = levels i}
  have hJoint : ∀ r : NNReal,
      P ({omega | N omega r A = 0} ∩ D) =
      P {omega | N omega r A = 0} * P D := by
    intro r
    have h :=
      Kyprianou.Ch06.zeroACountIndependentOfFiniteTwoOutsideSpacetimeCoordinates
        P n N hPPP A B C hA hB hC hAB hAC
        hFA hFB hFC m r s t times marks hSelect levels
    simpa only [D,Set.inter_def,Set.mem_inter_iff,
      Set.mem_setOf_eq] using h
  have h :=
    Kyprianou.Ch06.firstArrivalIndependentOfEventFromZeroCountIndependence
      P n N A firstMark hPPP hA hFA hMark D hJoint v
  simpa only [D,Set.inter_def,Set.mem_inter_iff,
    Set.mem_setOf_eq] using h
