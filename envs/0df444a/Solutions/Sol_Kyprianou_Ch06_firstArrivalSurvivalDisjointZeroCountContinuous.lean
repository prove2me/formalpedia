-- Prove2me | solution 1 for Kyprianou.Ch06.firstArrivalSurvivalDisjointZeroCountContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:04:22.138206+00:00
-- url     : https://prove2.me/submissions/2fbd4d17-09f9-4c78-8481-f1b2e63d1e4d

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstArrivalJointSurvivalWithDisjointZeroCount
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
    ContinuousAt (fun u : NNReal =>
      P {omega |
        N omega u D = 0 ∧
        (s : WithTop NNReal) <
          sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
            {v : NNReal | 0 < v ∧ 0 < N omega v B})}) t := by
  have hEq (u : NNReal) :
      P {omega |
        N omega u D = 0 ∧
        (s : WithTop NNReal) <
          sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
            {v : NNReal | 0 < v ∧ 0 < N omega v B})} =
      P {omega | N omega u D = 0 ∧ N omega s B = 0} := by
    have hFirst :=
      Kyprianou.Ch06.firstArrivalJointSurvivalWithDisjointZeroCount
        P n N hPPP B D hB hD hBD hFB hFD s u
    calc
      _ = P {omega |
        (s : WithTop NNReal) <
          sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
            {v : NNReal | 0 < v ∧ 0 < N omega v B}) ∧
        N omega u D = 0} := by
          congr 1
          ext omega
          simp only [and_comm]
      _ = P {omega | N omega s B = 0 ∧ N omega u D = 0} := hFirst
      _ = P {omega | N omega u D = 0 ∧ N omega s B = 0} := by
          congr 1
          ext omega
          simp only [and_comm]
  have hFun :
      (fun u : NNReal =>
        P {omega |
          N omega u D = 0 ∧
          (s : WithTop NNReal) <
            sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
              {v : NNReal | 0 < v ∧ 0 < N omega v B})}) =
      (fun u : NNReal =>
        P {omega | N omega u D = 0 ∧ N omega s B = 0}) :=
    funext hEq
  rw [hFun]
  exact Kyprianou.Ch06.disjointMarkedPoissonZeroCountJointContinuous
    P n N hPPP D B hD hB hBD.symm hFD hFB t s 0
