-- Prove2me | solution 1 for Kyprianou.Ch06.zeroAIncrementIndependentOfSeparatedOutsideRectangles
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:27:36.042442+00:00
-- url     : https://prove2.me/submissions/b57a3004-bcc9-4459-8e51-39472f59c60c

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_zeroAPlusSeparatedOutsideRectanglesPoissonProduct
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
    (A : Set E) (hA : MeasurableSet A) (hFA : n A < ⊤)
    (m : Nat) (starts stops : Fin m → NNReal)
    (B : Fin m → Set E) (counts : Fin m → Nat)
    (hValid : ∀ i, starts i ≤ stops i ∧
      MeasurableSet (B i) ∧ n (B i) < ⊤)
    (hAB : ∀ i, Disjoint A (B i))
    (hSep : ∀ i j : Fin m, i ≠ j →
      stops i ≤ starts j ∨ stops j ≤ starts i ∨
      Disjoint (B i) (B j))
    (r : NNReal) :
    P {omega | N omega r A - N omega 0 A = 0 ∧
      ∀ i : Fin m, N omega (stops i) (B i) -
        N omega (starts i) (B i) = counts i} =
    P {omega | N omega r A - N omega 0 A = 0} *
      P {omega | ∀ i : Fin m, N omega (stops i) (B i) -
        N omega (starts i) (B i) = counts i} := by
  have hJoint :=
    Kyprianou.Ch06.zeroAPlusSeparatedOutsideRectanglesPoissonProduct
      P n N hPPP A hA hFA m starts stops B counts hValid hAB hSep r
  have hOnlyOutside := hPPP.2.2 m starts stops B counts hValid hSep
  have hOnlyA :=
    Kyprianou.Ch06.markedPoissonOneRectangleIncrementLaw
      P n N hPPP 0 r bot_le A hA hFA 0
  calc
    P {omega | N omega r A - N omega 0 A = 0 ∧
      ∀ i : Fin m, N omega (stops i) (B i) -
        N omega (starts i) (B i) = counts i} =
      ProbabilityTheory.poissonMeasure (r * (n A).toNNReal) {0} *
        ∏ i : Fin m, ProbabilityTheory.poissonMeasure
          ((stops i - starts i) * (n (B i)).toNNReal) {counts i} := hJoint
    _ = P {omega | N omega r A - N omega 0 A = 0} *
        P {omega | ∀ i : Fin m, N omega (stops i) (B i) -
          N omega (starts i) (B i) = counts i} := by
          simpa using congrArg₂ (· * ·) hOnlyA.symm hOnlyOutside.symm
