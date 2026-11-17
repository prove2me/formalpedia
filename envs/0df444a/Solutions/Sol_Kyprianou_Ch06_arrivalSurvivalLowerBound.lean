-- Prove2me | solution 1 for Kyprianou.Ch06.arrivalSurvivalLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:00:50.913277+00:00
-- url     : https://prove2.me/submissions/e95e5c8c-bf81-4d58-878f-cb75681dbd20

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_zeroCountAfterTimeGivesBeforeFirstMark
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (N : Omega → NNReal → Set E → Nat) (A : Set E)
    (hMono : ∀ᵐ omega ∂P, Monotone (fun t : NNReal => N omega t A))
    (s t : NNReal) (hts : t < s) :
    P {omega | N omega s A = 0} ≤
    P {omega | (t : WithTop NNReal) <
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u A})} := by
  apply measure_mono_ae
  filter_upwards [hMono] with omega hm
  intro hZero
  exact Kyprianou.Ch06.zeroCountAfterTimeGivesBeforeFirstMark
    N A omega hm s t hts hZero
