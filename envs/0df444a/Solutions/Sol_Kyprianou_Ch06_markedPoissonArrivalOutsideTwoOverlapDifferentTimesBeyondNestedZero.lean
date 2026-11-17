-- Prove2me | solution 1 for Kyprianou.Ch06.markedPoissonArrivalOutsideTwoOverlapDifferentTimesBeyondNestedZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:08:53.507357+00:00
-- url     : https://prove2.me/submissions/e762609b-0016-48ca-b1a7-73a0cec4f02d

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfTwoOutsideCountsAllTimes
import Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfEventFromZeroCountIndependence
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch06

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A)
    (hFinite : n A < ⊤)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x})) :
    let sigma : Omega → WithTop NNReal := fun omega =>
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A})
    (∀ (times : Fin 2 → NNReal)
      (B : Fin 2 → Set E) (counts : Fin 2 → Nat) (t : NNReal),
      ¬ Disjoint (B 0) (B 1) →
      ¬ (B 0 = B 1 ∧ times 0 = times 1) →
      ¬ (counts 0 = 0 ∧ counts 1 = 0 ∧
         ((B 0 ⊆ B 1 ∧ times 0 ≤ times 1) ∨
          (B 1 ⊆ B 0 ∧ times 1 ≤ times 0))) →
      times 0 ≠ times 1 →
      (∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) →
        P {omega | (t : WithTop NNReal) < sigma omega ∧
          (∀ i : Fin 2, N omega (times i) (B i) = counts i)} =
          P {omega | (t : WithTop NNReal) < sigma omega} *
            P {omega |
              ∀ i : Fin 2, N omega (times i) (B i) = counts i}) := by
  dsimp only
  intro times B counts t hOverlap hDistinct hNonNested hDifferent hB
  let D : Set Omega :=
    {omega | N omega (times 0) (B 0) = counts 0 ∧
      N omega (times 1) (B 1) = counts 1}
  have hAB0 : Disjoint A (B 0) := by
    apply Set.disjoint_left.mpr
    intro x hxA hxB
    exact (hB 0).2.1 hxB hxA
  have hAB1 : Disjoint A (B 1) := by
    apply Set.disjoint_left.mpr
    intro x hxA hxB
    exact (hB 1).2.1 hxB hxA
  have hJoint : ∀ s : NNReal,
      P ({omega | N omega s A = 0} ∩ D) =
        P {omega | N omega s A = 0} * P D := by
    intro s
    have hFromPPP :=
      Kyprianou.Ch06.zeroACountIndependentOfTwoOutsideCountsAllTimes
        P n N hPPP A (B 0) (B 1) hA (hB 0).1 (hB 1).1
        hAB0 hAB1 hFinite (hB 0).2.2 (hB 1).2.2
        s (times 0) (times 1) (counts 0) (counts 1)
    change P {omega | N omega s A = 0 ∧
      N omega (times 0) (B 0) = counts 0 ∧
      N omega (times 1) (B 1) = counts 1} =
      P {omega | N omega s A = 0} *
      P {omega | N omega (times 0) (B 0) = counts 0 ∧
        N omega (times 1) (B 1) = counts 1}
    exact hFromPPP
  have hArrival :=
    Kyprianou.Ch06.firstArrivalIndependentOfEventFromZeroCountIndependence
      P n N A firstMark hPPP hA hFinite hMark D hJoint t
  simpa only [D, Fin.forall_fin_two, Set.inter_def,
    Set.mem_setOf_eq, and_assoc] using hArrival
