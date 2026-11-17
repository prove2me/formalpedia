-- Prove2me | solution 1 for Kyprianou.Ch06.twoTimeMarkedPoissonCumulativeCountJointLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:11:26.409417+00:00
-- url     : https://prove2.me/submissions/afc16c99-ed64-445e-8218-6405ba3f24bc

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_consecutiveMarkedPoissonCountIncrements
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A : Set E) (hA : MeasurableSet A) (hFinite : n A < ⊤)
    (s t : NNReal) (hst : s ≤ t) (k l : Nat) :
    P {omega | N omega s A = k ∧ N omega t A = k+l} =
    ProbabilityTheory.poissonMeasure
      (s * (n A).toNNReal) {k} *
    ProbabilityTheory.poissonMeasure
      ((t-s) * (n A).toNNReal) {l} := by
  have hEq : ∀ᵐ omega ∂P,
      (N omega s A = k ∧ N omega t A = k+l) =
      (N omega s A - N omega 0 A = k ∧
       N omega t A - N omega s A = l) := by
    filter_upwards [hPPP.2.1] with omega hw
    have hZero : N omega 0 A = 0 := hw.1 A
    have hMono : N omega s A ≤ N omega t A := hw.2.2 A hst
    simp only [hZero, Nat.sub_zero]
    apply propext
    constructor
    · intro h
      constructor
      · exact h.1
      · omega
    · intro h
      constructor
      · exact h.1
      · omega
  have hMeasure :
      P {omega | N omega s A = k ∧ N omega t A = k+l} =
      P {omega | N omega s A - N omega 0 A = k ∧
          N omega t A - N omega s A = l} := by
    apply measure_congr
    exact hEq
  calc
    P {omega | N omega s A = k ∧ N omega t A = k+l} =
      P {omega | N omega s A - N omega 0 A = k ∧
        N omega t A - N omega s A = l} := hMeasure
    _ = ProbabilityTheory.poissonMeasure
          (s * (n A).toNNReal) {k} *
        ProbabilityTheory.poissonMeasure
          ((t-s) * (n A).toNNReal) {l} :=
          Kyprianou.Ch06.consecutiveMarkedPoissonCountIncrements
            P n N hPPP A hA hFinite s t hst k l
