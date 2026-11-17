-- Prove2me | solution 1 for Kyprianou.Ch06.zeroACountIndependentOfSeparatedOutsideRectangles
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:31:44.025214+00:00
-- url     : https://prove2.me/submissions/32c52357-3c3f-4180-834d-d71860dd44d3

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_zeroAIncrementIndependentOfSeparatedOutsideRectangles
import Theorems.Thm_Kyprianou_Ch06_eventIndependenceOfAlmostSureEquivalentEvents
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
    P {omega | N omega r A = 0 ∧
      ∀ i : Fin m, N omega (stops i) (B i) -
        N omega (starts i) (B i) = counts i} =
    P {omega | N omega r A = 0} *
      P {omega | ∀ i : Fin m, N omega (stops i) (B i) -
        N omega (starts i) (B i) = counts i} := by
  let D : Set Omega := {omega | N omega r A = 0}
  let D' : Set Omega := {omega | N omega r A - N omega 0 A = 0}
  let G : Set Omega := {omega | ∀ i : Fin m,
    N omega (stops i) (B i) - N omega (starts i) (B i) = counts i}
  have hD : ∀ᵐ omega ∂P, (omega ∈ D) ↔ (omega ∈ D') := by
    filter_upwards [hPPP.2.1] with omega hw
    change (N omega r A = 0) ↔ (N omega r A - N omega 0 A = 0)
    simp [hw.1 A]
  have hRect :=
    Kyprianou.Ch06.zeroAIncrementIndependentOfSeparatedOutsideRectangles
      P n N hPPP A hA hFA m starts stops B counts hValid hAB hSep r
  change P (D' ∩ G) = P D' * P G at hRect
  have hTransfer :=
    Kyprianou.Ch06.eventIndependenceOfAlmostSureEquivalentEvents
      P D D' G G hD
      (Filter.Eventually.of_forall (fun _ => Iff.rfl)) hRect
  change P (D ∩ G) = P D * P G
  exact hTransfer
