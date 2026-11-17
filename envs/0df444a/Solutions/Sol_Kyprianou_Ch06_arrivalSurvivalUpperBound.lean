-- Prove2me | solution 1 for Kyprianou.Ch06.arrivalSurvivalUpperBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:00:41.61776+00:00
-- url     : https://prove2.me/submissions/391debd7-ddb1-4706-a5e2-edc6bc494361

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_beforeFirstPositiveMarkCountZero
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
    (hInit : ∀ᵐ omega ∂P, N omega 0 A = 0) (t : NNReal) :
    P {omega | (t : WithTop NNReal) <
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u A})} ≤
    P {omega | N omega t A = 0} := by
  apply measure_mono_ae
  filter_upwards [hInit] with omega hz
  intro hBefore
  exact Kyprianou.Ch06.beforeFirstPositiveMarkCountZero N A omega hz t hBefore
