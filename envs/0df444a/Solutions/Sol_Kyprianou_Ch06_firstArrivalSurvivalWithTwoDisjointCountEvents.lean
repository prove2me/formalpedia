-- Prove2me | solution 1 for Kyprianou.Ch06.firstArrivalSurvivalWithTwoDisjointCountEvents
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:14:09.554805+00:00
-- url     : https://prove2.me/submissions/4aa42bc3-2df4-4343-92f8-a6b00cfe0881

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstArrivalJointEventFromContinuousZeroCount
import Theorems.Thm_Kyprianou_Ch06_twoOutsideJointZeroCountContinuous
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
    (B D C : Set E)
    (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hC : MeasurableSet C)
    (hBD : Disjoint B D) (hBC : Disjoint B C)
    (hDC : Disjoint D C)
    (hFB : n B < ⊤) (hFD : n D < ⊤) (hFC : n C < ⊤)
    (s t u : NNReal) (k : Nat) :
    P {omega |
      (s : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v B}) ∧
      N omega t D = 0 ∧ N omega u C = k} =
    P {omega | N omega s B = 0 ∧
      N omega t D = 0 ∧ N omega u C = k} := by
  have hInit : ∀ᵐ omega ∂P, N omega 0 B = 0 :=
    hPPP.2.1.mono (fun omega h => h.1 B)
  have hMono : ∀ᵐ omega ∂P,
      Monotone (fun v : NNReal => N omega v B) :=
    hPPP.2.1.mono (fun omega h => h.2.2 B)
  have hCont : ContinuousAt
      (fun v : NNReal =>
        P {omega | N omega v B = 0 ∧
          omega ∈ {omega | N omega t D = 0 ∧ N omega u C = k}}) s :=
    Kyprianou.Ch06.twoOutsideJointZeroCountContinuous
      P n N hPPP B D C hB hD hC hBD hBC hDC
      hFB hFD hFC s t u 0 k
  simpa only [Set.mem_setOf_eq] using
    (Kyprianou.Ch06.firstArrivalJointEventFromContinuousZeroCount
      P N B {omega | N omega t D = 0 ∧ N omega u C = k}
      s hInit hMono hCont)
