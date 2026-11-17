-- Prove2me | solution 1 for Kyprianou.Ch06.markedPoissonMarginalCountLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T07:45:34.793163+00:00
-- url     : https://prove2.me/submissions/07011ff6-f237-4232-81f3-d9ee3d585d6e

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_markedPoissonOneRectangleIncrementLaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (t : NNReal) (A : Set E) (hA : MeasurableSet A)
    (hFinite : n A < ⊤) (k : Nat) :
  P {omega | N omega t A = k} =
    ProbabilityTheory.poissonMeasure (t * (n A).toNNReal) {k} := by
  have hzero : ∀ᵐ omega ∂P, N omega 0 A = 0 := by
    filter_upwards [hPPP.2.1] with omega hw
    exact hw.1 A
  have heq : ∀ᵐ omega ∂P,
      (N omega t A = k) = (N omega t A - N omega 0 A = k) := by
    filter_upwards [hzero] with omega hz
    simp [hz]
  calc
    P {omega | N omega t A = k} =
        P {omega | N omega t A - N omega 0 A = k} := by
          apply measure_congr
          exact heq
    _ = ProbabilityTheory.poissonMeasure (t * (n A).toNNReal) {k} := by
      simpa using
        (Kyprianou.Ch06.markedPoissonOneRectangleIncrementLaw
          P n N hPPP 0 t (zero_le) A hA hFinite k)
