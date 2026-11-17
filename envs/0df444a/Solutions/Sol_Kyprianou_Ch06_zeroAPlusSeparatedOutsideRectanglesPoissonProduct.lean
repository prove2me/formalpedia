-- Prove2me | solution 1 for Kyprianou.Ch06.zeroAPlusSeparatedOutsideRectanglesPoissonProduct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:19:12.982769+00:00
-- url     : https://prove2.me/submissions/210c3df6-2e8c-40a0-a30a-66474b181174

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
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
    ProbabilityTheory.poissonMeasure (r * (n A).toNNReal) {0} *
      ∏ i : Fin m, ProbabilityTheory.poissonMeasure
        ((stops i - starts i) * (n (B i)).toNNReal) {counts i} := by
  let extStarts : Fin (m+1) → NNReal := Fin.cons 0 starts
  let extStops : Fin (m+1) → NNReal := Fin.cons r stops
  let extMarks : Fin (m+1) → Set E := Fin.cons A B
  let extCounts : Fin (m+1) → Nat := Fin.cons 0 counts
  have hValidExt : ∀ i : Fin (m+1),
      extStarts i ≤ extStops i ∧
      MeasurableSet (extMarks i) ∧ n (extMarks i) < ⊤ := by
    intro i
    cases i using Fin.cases with
    | zero => exact ⟨bot_le, hA, hFA⟩
    | succ i => exact hValid i
  have hSepExt : ∀ i j : Fin (m+1), i ≠ j →
      extStops i ≤ extStarts j ∨
      extStops j ≤ extStarts i ∨
      Disjoint (extMarks i) (extMarks j) := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero => exact False.elim (hij rfl)
        | succ j => exact Or.inr (Or.inr (hAB j))
    | succ i =>
        cases j using Fin.cases with
        | zero => exact Or.inr (Or.inr (hAB i).symm)
        | succ j =>
            have hij' : i ≠ j := by
              intro heq
              apply hij
              simpa [heq]
            exact hSep i j hij'
  have h :=
    hPPP.2.2 (m+1) extStarts extStops extMarks extCounts
      hValidExt hSepExt
  simpa [extStarts, extStops, extMarks, extCounts,
    Fin.forall_fin_succ, Fin.prod_univ_succ] using h
