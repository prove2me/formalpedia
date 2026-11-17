-- Prove2me | solution 1 for Kyprianou.Ch06.markedPoissonArrivalOutsideThreeOrMoreNonUniformZero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T12:06:15.589769+00:00
-- url     : https://prove2.me/submissions/a343c641-2fdb-4455-8b97-0670c5580e4d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfDominatedOutsideZeroCylinder
import Theorems.Thm_Kyprianou_Ch06_markedPoissonArrivalOutsideThreeOrMoreBeyondDominatedZeros
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
      3 ≤ m →
      (∃ i j : Fin m, i ≠ j ∧ ¬ Disjoint (B i) (B j)) →
      ¬ ((∃ u : NNReal, ∀ i : Fin m, times i = u) ∧
         (∀ i : Fin m, counts i = 0)) →
      (∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) →
        P {omega | (t : WithTop NNReal) < sigma omega ∧
          (∀ i : Fin m, N omega (times i) (B i) = counts i)} =
          P {omega | (t : WithTop NNReal) < sigma omega} *
            P {omega |
              ∀ i : Fin m, N omega (times i) (B i) = counts i}) := by
  dsimp only
  intro m times B counts t hLarge hOverlap hNonUniform hB
  by_cases hDomZero : (∀ i : Fin m, counts i = 0) ∧
      (∃ u : Fin m, ∀ i : Fin m, B i ⊆ B u ∧ times i ≤ times u)
  · obtain ⟨hCount, u, hDom⟩ := hDomZero
    have hEq : counts = fun _ : Fin m => 0 := funext hCount
    subst counts
    exact
      Kyprianou.Ch06.firstArrivalIndependentOfDominatedOutsideZeroCylinder
        P n N A firstMark hPPP hA hFinite hMark m times B hB u hDom t
  · exact
      Kyprianou.Ch06.markedPoissonArrivalOutsideThreeOrMoreBeyondDominatedZeros
        P n N A firstMark hPPP hA hFinite hMark
        m times B counts t hLarge hOverlap hNonUniform hDomZero hB
