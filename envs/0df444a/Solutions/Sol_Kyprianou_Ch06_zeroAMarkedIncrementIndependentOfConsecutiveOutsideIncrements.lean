-- Prove2me | solution 1 for Kyprianou.Ch06.zeroAMarkedIncrementIndependentOfConsecutiveOutsideIncrements
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:14:41.488985+00:00
-- url     : https://prove2.me/submissions/a129cc38-0cc4-4cb1-a60d-924bac650bac

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_consecutiveMarkedPoissonCountIncrements
import Theorems.Thm_Kyprianou_Ch06_zeroAAndConsecutiveOutsideIncrementTriplePoissonProduct
import Theorems.Thm_Kyprianou_Ch06_markedPoissonOneRectangleIncrementLaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (hFA : n A < ⊤) (hFB : n B < ⊤)
    (r s t : NNReal) (hst : s ≤ t) (k l : Nat) :
    P {omega | N omega r A - N omega 0 A = 0 ∧
      N omega s B - N omega 0 B = k ∧
      N omega t B - N omega s B = l} =
    P {omega | N omega r A - N omega 0 A = 0} *
    P {omega | N omega s B - N omega 0 B = k ∧
      N omega t B - N omega s B = l} := by
  have hJoint :=
    Kyprianou.Ch06.zeroAAndConsecutiveOutsideIncrementTriplePoissonProduct
      P n N hPPP A B hA hB hAB hFA hFB r s t hst k l
  have hFirst :
      P {omega | N omega r A - N omega 0 A = 0} =
        ProbabilityTheory.poissonMeasure (r * (n A).toNNReal) {0} := by
    simpa using
      (Kyprianou.Ch06.markedPoissonOneRectangleIncrementLaw
        P n N hPPP 0 r bot_le A hA hFA 0)
  have hOutside :=
    Kyprianou.Ch06.consecutiveMarkedPoissonCountIncrements
      P n N hPPP B hB hFB s t hst k l
  calc
    P {omega | N omega r A - N omega 0 A = 0 ∧
      N omega s B - N omega 0 B = k ∧
      N omega t B - N omega s B = l} =
      ProbabilityTheory.poissonMeasure (r * (n A).toNNReal) {0} *
        (ProbabilityTheory.poissonMeasure (s * (n B).toNNReal) {k} *
          ProbabilityTheory.poissonMeasure ((t-s) * (n B).toNNReal) {l}) := hJoint
    _ = P {omega | N omega r A - N omega 0 A = 0} *
      P {omega | N omega s B - N omega 0 B = k ∧
        N omega t B - N omega s B = l} := by
      rw [hFirst, hOutside]
