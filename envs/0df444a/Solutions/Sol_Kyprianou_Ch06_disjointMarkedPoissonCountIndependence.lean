-- Prove2me | solution 1 for Kyprianou.Ch06.disjointMarkedPoissonCountIndependence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:10:54.273837+00:00
-- url     : https://prove2.me/submissions/3e4fb94d-fd3d-4f67-9c56-40b16eb370a4

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_twoDisjointMarkedPoissonRectangles
import Theorems.Thm_Kyprianou_Ch06_markedPoissonMarginalCountLaw
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
    (A B : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : Disjoint A B)
    (hFiniteA : n A < ⊤) (hFiniteB : n B < ⊤)
    (s t : NNReal) (k l : Nat) :
    P {omega | N omega s A = k ∧ N omega t B = l} =
      P {omega | N omega s A = k} *
      P {omega | N omega t B = l} := by
  have hInitial :
      ∀ᵐ omega ∂P, N omega 0 A = 0 ∧ N omega 0 B = 0 := by
    filter_upwards [hPPP.2.1] with omega h
    exact ⟨h.1 A, h.1 B⟩
  have hAe : ∀ᵐ omega ∂P,
      ((N omega s A = k) ∧ (N omega t B = l)) =
      ((N omega s A - N omega 0 A = k) ∧
       (N omega t B - N omega 0 B = l)) := by
    filter_upwards [hInitial] with omega hz
    simp [hz.1, hz.2]
  have heq :
      P {omega | N omega s A = k ∧ N omega t B = l} =
      P {omega | N omega s A - N omega 0 A = k ∧
        N omega t B - N omega 0 B = l} := by
    apply measure_congr
    exact hAe
  calc
    P {omega | N omega s A = k ∧ N omega t B = l} =
        P {omega | N omega s A - N omega 0 A = k ∧
          N omega t B - N omega 0 B = l} := heq
    _ = ProbabilityTheory.poissonMeasure
          (s * (n A).toNNReal) {k} *
        ProbabilityTheory.poissonMeasure
          (t * (n B).toNNReal) {l} :=
          Kyprianou.Ch06.twoDisjointMarkedPoissonRectangles
            P n N hPPP A B hA hB hAB hFiniteA hFiniteB s t k l
    _ = P {omega | N omega s A = k} *
        P {omega | N omega t B = l} := by
      rw [← Kyprianou.Ch06.markedPoissonMarginalCountLaw
           P n N hPPP s A hA hFiniteA k,
          ← Kyprianou.Ch06.markedPoissonMarginalCountLaw
           P n N hPPP t B hB hFiniteB l]
