-- Prove2me | solution 1 for Kyprianou.Ch06.markedPoissonArrivalOutsideIndependenceMany
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:51:35.721127+00:00
-- url     : https://prove2.me/submissions/f2724555-1e6b-4075-a955-6b33cace225e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfTwoDisjointOutsideCounts
import Theorems.Thm_Kyprianou_Ch06_markedPoissonArrivalOutsideTwoOverlapping
import Theorems.Thm_Kyprianou_Ch06_markedPoissonArrivalOutsideThreeOrMore
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
    (∀ (m : Nat) (times : Fin m → NNReal)
      (B : Fin m → Set E) (counts : Fin m → Nat) (t : NNReal),
      2 ≤ m →
      (∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) →
        P {omega | (t : WithTop NNReal) < sigma omega ∧
          (∀ i : Fin m, N omega (times i) (B i) = counts i)} =
          P {omega | (t : WithTop NNReal) < sigma omega} *
            P {omega |
              ∀ i : Fin m, N omega (times i) (B i) = counts i}) := by
  dsimp only
  intro m times B counts t h2 hB
  cases m with
  | zero => omega
  | succ m =>
      cases m with
      | zero => omega
      | succ m =>
          cases m with
          | zero =>
              by_cases hDisj : Disjoint (B 0) (B 1)
              · have hAB : Disjoint A (B 0) := by
                  apply Set.disjoint_left.mpr
                  intro x hxA hxB
                  exact (hB 0).2.1 hxB hxA
                have hAC : Disjoint A (B 1) := by
                  apply Set.disjoint_left.mpr
                  intro x hxA hxB
                  exact (hB 1).2.1 hxB hxA
                simpa [Fin.forall_fin_two] using
                  (Kyprianou.Ch06.firstArrivalIndependentOfTwoDisjointOutsideCounts
                    P n N A firstMark hPPP hA hFinite hMark
                    (B 0) (B 1) (hB 0).1 (hB 1).1
                    hAB hAC hDisj (hB 0).2.2 (hB 1).2.2
                    t (times 0) (times 1) (counts 0) (counts 1))
              · exact
                  Kyprianou.Ch06.markedPoissonArrivalOutsideTwoOverlapping
                    P n N A firstMark hPPP hA hFinite hMark
                    times B counts t hDisj hB
          | succ k =>
              exact
                Kyprianou.Ch06.markedPoissonArrivalOutsideThreeOrMore
                  P n N A firstMark hPPP hA hFinite hMark
                  (Nat.succ (Nat.succ (Nat.succ k)))
                  times B counts t (by omega) hB
