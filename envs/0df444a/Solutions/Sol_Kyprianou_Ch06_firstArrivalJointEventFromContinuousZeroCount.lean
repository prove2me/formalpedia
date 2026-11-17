-- Prove2me | solution 1 for Kyprianou.Ch06.firstArrivalJointEventFromContinuousZeroCount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:20:42.452395+00:00
-- url     : https://prove2.me/submissions/83973ea9-7a41-43a9-85da-ae93e9a371c7

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_beforeFirstPositiveMarkCountZero
import Theorems.Thm_Kyprianou_Ch06_zeroCountAfterTimeGivesBeforeFirstMark
import Theorems.Thm_Kyprianou_Ch06_rightContinuousSandwich
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (C : Set Omega) (t : NNReal)
    (hInit : ∀ᵐ omega ∂P, N omega 0 A = 0)
    (hMono : ∀ᵐ omega ∂P,
      Monotone (fun s : NNReal => N omega s A))
    (hCont : ContinuousAt
      (fun s : NNReal => P {omega | N omega s A = 0 ∧ omega ∈ C}) t) :
    P {omega |
      (t : WithTop NNReal) <
        sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ 0 < N omega u A}) ∧
      omega ∈ C} =
    P {omega | N omega t A = 0 ∧ omega ∈ C} := by
  let F : NNReal → ENNReal :=
    fun s => P {omega | N omega s A = 0 ∧ omega ∈ C}
  have hF : ContinuousAt F t := hCont
  have hUpper :
      P {omega |
        (t : WithTop NNReal) <
          sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
            {u : NNReal | 0 < u ∧ 0 < N omega u A}) ∧
        omega ∈ C} ≤ F t := by
    dsimp [F]
    apply measure_mono_ae
    filter_upwards [hInit] with omega hz
    intro ⟨hBefore, hC⟩
    exact ⟨Kyprianou.Ch06.beforeFirstPositiveMarkCountZero
      N A omega hz t hBefore, hC⟩
  have hLower : ∀ s : NNReal, t < s →
      F s ≤ P {omega |
        (t : WithTop NNReal) <
          sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
            {u : NNReal | 0 < u ∧ 0 < N omega u A}) ∧
        omega ∈ C} := by
    intro s hts
    dsimp [F]
    apply measure_mono_ae
    filter_upwards [hMono] with omega hm
    intro ⟨hZero, hC⟩
    exact ⟨Kyprianou.Ch06.zeroCountAfterTimeGivesBeforeFirstMark
      N A omega hm s t hts hZero, hC⟩
  exact Kyprianou.Ch06.rightContinuousSandwich F t
    (P {omega |
      (t : WithTop NNReal) <
        sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ 0 < N omega u A}) ∧
      omega ∈ C}) hF hUpper hLower
