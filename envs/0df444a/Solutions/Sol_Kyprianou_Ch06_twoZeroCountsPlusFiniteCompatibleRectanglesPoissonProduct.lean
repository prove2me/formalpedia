-- Prove2me | solution 1 for Kyprianou.Ch06.twoZeroCountsPlusFiniteCompatibleRectanglesPoissonProduct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:21:16.531865+00:00
-- url     : https://prove2.me/submissions/76686c07-d459-41f3-b141-134da02101c0

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
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
    (B D : Set E) (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hBD : Disjoint B D) (hFB : n B < ⊤) (hFD : n D < ⊤)
    (m : Nat) (starts stops : Fin m → NNReal)
    (C : Fin m → Set E) (counts : Fin m → Nat)
    (hValid : ∀ i, starts i ≤ stops i ∧
      MeasurableSet (C i) ∧ n (C i) < ⊤)
    (hBC : ∀ i, Disjoint B (C i))
    (hDC : ∀ i, Disjoint D (C i))
    (hSep : ∀ i j : Fin m, i ≠ j →
      stops i ≤ starts j ∨ stops j ≤ starts i ∨
      Disjoint (C i) (C j))
    (s t : NNReal) :
    P {omega |
      N omega s B - N omega 0 B = 0 ∧
      N omega t D - N omega 0 D = 0 ∧
      ∀ i : Fin m,
        N omega (stops i) (C i) -
          N omega (starts i) (C i) = counts i} =
    (ProbabilityTheory.poissonMeasure (s * (n B).toNNReal) {0} *
      ProbabilityTheory.poissonMeasure (t * (n D).toNNReal) {0}) *
    ∏ i : Fin m,
      ProbabilityTheory.poissonMeasure
        ((stops i - starts i) * (n (C i)).toNNReal) {counts i} := by
  let allStarts : Fin (m + 2) → NNReal :=
    Fin.cons 0 (Fin.cons 0 starts)
  let allStops : Fin (m + 2) → NNReal :=
    Fin.cons s (Fin.cons t stops)
  let allMarks : Fin (m + 2) → Set E :=
    Fin.cons B (Fin.cons D C)
  let allCounts : Fin (m + 2) → Nat :=
    Fin.cons 0 (Fin.cons 0 counts)
  have hValidAll : ∀ i : Fin (m + 2),
      allStarts i ≤ allStops i ∧
      MeasurableSet (allMarks i) ∧ n (allMarks i) < ⊤ := by
    intro i
    cases i using Fin.cases with
    | zero => exact ⟨bot_le, hB, hFB⟩
    | succ i =>
      cases i using Fin.cases with
      | zero => exact ⟨bot_le, hD, hFD⟩
      | succ i => exact hValid i
  have hSepAll : ∀ i j : Fin (m + 2), i ≠ j →
      allStops i ≤ allStarts j ∨
      allStops j ≤ allStarts i ∨
      Disjoint (allMarks i) (allMarks j) := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact False.elim (hij rfl)
      | succ j =>
        cases j using Fin.cases with
        | zero => exact Or.inr (Or.inr hBD)
        | succ j => exact Or.inr (Or.inr (hBC j))
    | succ i =>
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact Or.inr (Or.inr hBD.symm)
        | succ j =>
          cases j using Fin.cases with
          | zero => exact False.elim (hij rfl)
          | succ j => exact Or.inr (Or.inr (hDC j))
      | succ i =>
        cases j using Fin.cases with
        | zero => exact Or.inr (Or.inr (hBC i).symm)
        | succ j =>
          cases j using Fin.cases with
          | zero => exact Or.inr (Or.inr (hDC i).symm)
          | succ j =>
            have hij' : i ≠ j := by
              intro heq
              apply hij
              simpa [heq]
            exact hSep i j hij'
  have h :=
    hPPP.2.2 (m + 2) allStarts allStops allMarks allCounts
      hValidAll hSepAll
  simpa [allStarts, allStops, allMarks, allCounts,
    Fin.forall_fin_succ, Fin.prod_univ_succ, mul_assoc] using h
