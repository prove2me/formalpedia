-- Prove2me | solution 1 for Kyprianou.Ch06.markedPoissonArrivalOutsideIndependence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:30:45.972474+00:00
-- url     : https://prove2.me/submissions/8a83cb58-97bd-44c3-b38d-dbef5a43ba74
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfOneDisjointCount
import Theorems.Thm_Kyprianou_Ch06_markedPoissonArrivalOutsideIndependenceMany
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
      (∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) →
        P {omega | (t : WithTop NNReal) < sigma omega ∧
          (∀ i : Fin m, N omega (times i) (B i) = counts i)} =
          P {omega | (t : WithTop NNReal) < sigma omega} *
            P {omega |
              ∀ i : Fin m, N omega (times i) (B i) = counts i}) := by
  dsimp only
  intro m times B counts t hB
  cases m with
  | zero =>
      simp
  | succ m =>
      cases m with
      | zero =>
          have hDisj : Disjoint A (B 0) := by
            apply Set.disjoint_left.mpr
            intro x hxA hxB
            exact (hB 0).2.1 hxB hxA
          simpa [Fin.forall_fin_one] using
            (Kyprianou.Ch06.firstArrivalIndependentOfOneDisjointCount
              P n N A firstMark hPPP hA hFinite hMark
              (B 0) (hB 0).1 hDisj (hB 0).2.2
              t (times 0) (counts 0))
      | succ k =>
          exact
            Kyprianou.Ch06.markedPoissonArrivalOutsideIndependenceMany
              P n N A firstMark hPPP hA hFinite hMark
              (k+2) times B counts t (by omega) hB
