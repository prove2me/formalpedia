-- Prove2me | solution 1 for Kyprianou.Ch06.firstArrivalTwoDisjointJointSurvivalIsZeroCount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:06:17.115324+00:00
-- url     : https://prove2.me/submissions/8928c550-01af-4704-b4d7-f12a07f7b849

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstArrivalJointSurvivalWithDisjointZeroCount
import Theorems.Thm_Kyprianou_Ch06_firstArrivalJointEventFromContinuousZeroCount
import Theorems.Thm_Kyprianou_Ch06_firstArrivalSurvivalDisjointZeroCountContinuous
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
      (t : WithTop NNReal) <
        sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ 0 < N omega u D})} =
    P {omega | N omega s B = 0 ∧ N omega t D = 0} := by
  let SB : Set Omega := {omega |
    (s : WithTop NNReal) <
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u B})}
  have hCont : ContinuousAt
      (fun u : NNReal => P {omega | N omega u D = 0 ∧ omega ∈ SB}) t :=
    Kyprianou.Ch06.firstArrivalSurvivalDisjointZeroCountContinuous
      P n N hPPP B D hB hD hBD hFB hFD s t
  have hInit : ∀ᵐ omega ∂P, N omega 0 D = 0 :=
    hPPP.2.1.mono (fun omega h => h.1 D)
  have hMono : ∀ᵐ omega ∂P,
      Monotone (fun u : NNReal => N omega u D) :=
    hPPP.2.1.mono (fun omega h => h.2.2 D)
  have hSecond :=
    Kyprianou.Ch06.firstArrivalJointEventFromContinuousZeroCount
      P N D SB t hInit hMono hCont
  have hFirst :=
    Kyprianou.Ch06.firstArrivalJointSurvivalWithDisjointZeroCount
      P n N hPPP B D hB hD hBD hFB hFD s t
  calc
    _ = P {omega |
      (t : WithTop NNReal) <
        sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ 0 < N omega u D}) ∧
      omega ∈ SB} := by
        congr 1
        ext omega
        simp only [SB, Set.mem_setOf_eq, and_comm]
    _ = P {omega | N omega t D = 0 ∧ omega ∈ SB} := by
      simpa only [SB, Set.mem_setOf_eq] using hSecond
    _ = P {omega | N omega s B = 0 ∧ N omega t D = 0} := by
      simpa only [SB, Set.mem_setOf_eq, and_comm] using hFirst

