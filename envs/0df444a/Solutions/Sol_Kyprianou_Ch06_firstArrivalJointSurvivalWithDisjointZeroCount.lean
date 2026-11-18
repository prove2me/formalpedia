-- Prove2me | solution 1 for Kyprianou.Ch06.firstArrivalJointSurvivalWithDisjointZeroCount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:56:33.26323+00:00
-- url     : https://prove2.me/submissions/00847496-a7f3-43d5-b27f-900d1de6f4b1

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstArrivalJointEventFromContinuousZeroCount
import Theorems.Thm_Kyprianou_Ch06_disjointMarkedPoissonZeroCountJointContinuous
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B D : Set E) (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hBD : Disjoint B D) (hFB : n B < ⊤) (hFD : n D < ⊤)
    (s t : NNReal) :
    P {omega |
      (s : WithTop NNReal) <
        sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ 0 < N omega u B}) ∧
      N omega t D = 0} =
    P {omega | N omega s B = 0 ∧ N omega t D = 0} := by
  have hInit : ∀ᵐ omega ∂P, N omega 0 B = 0 :=
    hPPP.2.1.mono (fun omega h => h.1 B)
  have hMono : ∀ᵐ omega ∂P,
      Monotone (fun u : NNReal => N omega u B) :=
    hPPP.2.1.mono (fun omega h => h.2.2 B)
  have hCont : ContinuousAt
      (fun u : NNReal =>
        P {omega | N omega u B = 0 ∧ N omega t D = 0}) s :=
    Kyprianou.Ch06.disjointMarkedPoissonZeroCountJointContinuous
      P n N hPPP B D hB hD hBD hFB hFD s t 0
  exact Kyprianou.Ch06.firstArrivalJointEventFromContinuousZeroCount
    P N B {omega | N omega t D = 0} s hInit hMono hCont
