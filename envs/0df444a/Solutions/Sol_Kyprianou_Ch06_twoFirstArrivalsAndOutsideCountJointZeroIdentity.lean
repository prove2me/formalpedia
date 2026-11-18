-- Prove2me | solution 1 for Kyprianou.Ch06.twoFirstArrivalsAndOutsideCountJointZeroIdentity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:21:23.007062+00:00
-- url     : https://prove2.me/submissions/32051a89-9a11-45d1-a942-cfc384371575

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstArrivalSurvivalWithTwoDisjointCountEvents
import Theorems.Thm_Kyprianou_Ch06_firstArrivalWithOutsideCountJointContinuous
import Theorems.Thm_Kyprianou_Ch06_firstArrivalJointEventFromContinuousZeroCount
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
      (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v D}) ∧
      N omega u C = k} =
    P {omega | N omega s B = 0 ∧
      N omega t D = 0 ∧ N omega u C = k} := by
  let SB : Set Omega := {omega |
    (s : WithTop NNReal) <
      sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
        {v : NNReal | 0 < v ∧ 0 < N omega v B})}
  let Cevent : Set Omega := {omega | omega ∈ SB ∧ N omega u C = k}
  have hInit : ∀ᵐ omega ∂P, N omega 0 D = 0 :=
    hPPP.2.1.mono (fun omega h => h.1 D)
  have hMono : ∀ᵐ omega ∂P,
      Monotone (fun v : NNReal => N omega v D) :=
    hPPP.2.1.mono (fun omega h => h.2.2 D)
  have hCont : ContinuousAt
      (fun v : NNReal =>
        P {omega | N omega v D = 0 ∧ omega ∈ Cevent}) t :=
    Kyprianou.Ch06.firstArrivalWithOutsideCountJointContinuous
      P n N hPPP B D C hB hD hC hBD hBC hDC
      hFB hFD hFC s t u k
  have hSecond :=
    Kyprianou.Ch06.firstArrivalJointEventFromContinuousZeroCount
      P N D Cevent t hInit hMono hCont
  have hFirst :=
    Kyprianou.Ch06.firstArrivalSurvivalWithTwoDisjointCountEvents
      P n N hPPP B D C hB hD hC hBD hBC hDC
      hFB hFD hFC s t u k
  calc
    _ = P {omega |
      (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v D}) ∧
      omega ∈ Cevent} := by
        congr 1
        ext omega
        simp only [Cevent, SB, Set.mem_setOf_eq,
          and_assoc, and_comm, and_left_comm]
    _ = P {omega | N omega t D = 0 ∧ omega ∈ Cevent} := hSecond
    _ = P {omega | N omega s B = 0 ∧
      N omega t D = 0 ∧ N omega u C = k} := by
        simpa only [Cevent, SB, Set.mem_setOf_eq,
          and_assoc, and_comm, and_left_comm] using hFirst
