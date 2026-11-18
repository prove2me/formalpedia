-- Prove2me | solution 1 for Kyprianou.Ch06.firstArrivalWithOutsideCountJointContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:17:08.203737+00:00
-- url     : https://prove2.me/submissions/b3f4d7c1-a66d-4bf4-9f0a-1bf1138f74a9

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstArrivalSurvivalWithTwoDisjointCountEvents
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
    ContinuousAt (fun v : NNReal =>
      P {omega | N omega v D = 0 ∧
        (s : WithTop NNReal) <
          sInf ((fun w : NNReal => (w : WithTop NNReal)) ''
            {w : NNReal | 0 < w ∧ 0 < N omega w B}) ∧
        N omega u C = k}) t := by
  have hEq (v : NNReal) :
      P {omega | N omega v D = 0 ∧
        (s : WithTop NNReal) <
          sInf ((fun w : NNReal => (w : WithTop NNReal)) ''
            {w : NNReal | 0 < w ∧ 0 < N omega w B}) ∧
        N omega u C = k} =
      P {omega | N omega v D = 0 ∧ N omega s B = 0 ∧
        N omega u C = k} := by
    have hFirst :=
      Kyprianou.Ch06.firstArrivalSurvivalWithTwoDisjointCountEvents
        P n N hPPP B D C hB hD hC hBD hBC hDC
        hFB hFD hFC s v u k
    calc
      _ = P {omega |
        (s : WithTop NNReal) <
          sInf ((fun w : NNReal => (w : WithTop NNReal)) ''
            {w : NNReal | 0 < w ∧ 0 < N omega w B}) ∧
        N omega v D = 0 ∧ N omega u C = k} := by
          congr 1
          ext omega
          simp only [and_assoc, and_left_comm, and_comm]
      _ = P {omega | N omega s B = 0 ∧ N omega v D = 0 ∧
        N omega u C = k} := hFirst
      _ = P {omega | N omega v D = 0 ∧ N omega s B = 0 ∧
        N omega u C = k} := by
          congr 1
          ext omega
          simp only [and_assoc, and_left_comm, and_comm]
  have hFun :
      (fun v : NNReal =>
        P {omega | N omega v D = 0 ∧
          (s : WithTop NNReal) <
            sInf ((fun w : NNReal => (w : WithTop NNReal)) ''
              {w : NNReal | 0 < w ∧ 0 < N omega w B}) ∧
          N omega u C = k}) =
      (fun v : NNReal =>
        P {omega | N omega v D = 0 ∧ N omega s B = 0 ∧
          N omega u C = k}) :=
    funext hEq
  rw [hFun]
  exact Kyprianou.Ch06.twoOutsideJointZeroCountContinuous
    P n N hPPP D B C hD hB hC hBD.symm hDC hBC
    hFD hFB hFC t s u 0 k
