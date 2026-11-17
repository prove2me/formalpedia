-- Prove2me | solution 1 for Kyprianou.Ch06.threeDisjointMarkedPoissonCountIndependence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:20:35.383234+00:00
-- url     : https://prove2.me/submissions/5a1202a8-c6d6-4c99-b5c2-f95df46878a9

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_threeDisjointMarkedPoissonRectangles
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
    (A B C : Set E)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C)
    (hFiniteA : n A < ⊤) (hFiniteB : n B < ⊤)
    (hFiniteC : n C < ⊤)
    (s t u : NNReal) (k l r : Nat) :
    P {omega | N omega s A = k ∧
      N omega t B = l ∧ N omega u C = r} =
    P {omega | N omega s A = k} *
    P {omega | N omega t B = l} *
    P {omega | N omega u C = r} := by
  have hInitial : ∀ᵐ omega ∂P, N omega 0 A = 0 ∧
      N omega 0 B = 0 ∧ N omega 0 C = 0 := by
    filter_upwards [hPPP.2.1] with omega h
    exact ⟨h.1 A, h.1 B, h.1 C⟩
  have hAe : ∀ᵐ omega ∂P,
      ((N omega s A = k) ∧
       (N omega t B = l) ∧ (N omega u C = r)) =
      ((N omega s A - N omega 0 A = k) ∧
       (N omega t B - N omega 0 B = l) ∧
       (N omega u C - N omega 0 C = r)) := by
    filter_upwards [hInitial] with omega hz
    simp [hz.1, hz.2.1, hz.2.2]
  have heq :
      P {omega | N omega s A = k ∧
        N omega t B = l ∧ N omega u C = r} =
      P {omega | N omega s A - N omega 0 A = k ∧
        N omega t B - N omega 0 B = l ∧
        N omega u C - N omega 0 C = r} := by
    apply measure_congr
    exact hAe
  calc
    P {omega | N omega s A = k ∧ N omega t B = l ∧
      N omega u C = r} =
        P {omega | N omega s A - N omega 0 A = k ∧
          N omega t B - N omega 0 B = l ∧
          N omega u C - N omega 0 C = r} := heq
    _ = ProbabilityTheory.poissonMeasure
          (s * (n A).toNNReal) {k} *
        ProbabilityTheory.poissonMeasure
          (t * (n B).toNNReal) {l} *
        ProbabilityTheory.poissonMeasure
          (u * (n C).toNNReal) {r} :=
          Kyprianou.Ch06.threeDisjointMarkedPoissonRectangles
            P n N hPPP A B C hA hB hC hAB hAC hBC
            hFiniteA hFiniteB hFiniteC s t u k l r
    _ = P {omega | N omega s A = k} *
        P {omega | N omega t B = l} *
        P {omega | N omega u C = r} := by
      rw [← Kyprianou.Ch06.markedPoissonMarginalCountLaw
           P n N hPPP s A hA hFiniteA k,
          ← Kyprianou.Ch06.markedPoissonMarginalCountLaw
           P n N hPPP t B hB hFiniteB l,
          ← Kyprianou.Ch06.markedPoissonMarginalCountLaw
           P n N hPPP u C hC hFiniteC r]
