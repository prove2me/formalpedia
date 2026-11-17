-- Prove2me | solution 1 for Kyprianou.Ch06.threeDisjointMarkedPoissonRectangles
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:15:47.59024+00:00
-- url     : https://prove2.me/submissions/935510d2-628b-4e5c-9110-5d8e03785ae4

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
    (A B C : Set E)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C)
    (hFiniteA : n A < ⊤) (hFiniteB : n B < ⊤)
    (hFiniteC : n C < ⊤)
    (s t u : NNReal) (k l r : Nat) :
    P {omega | N omega s A - N omega 0 A = k ∧
      N omega t B - N omega 0 B = l ∧
      N omega u C - N omega 0 C = r} =
    ProbabilityTheory.poissonMeasure
      (s * (n A).toNNReal) {k} *
    ProbabilityTheory.poissonMeasure
      (t * (n B).toNNReal) {l} *
    ProbabilityTheory.poissonMeasure
      (u * (n C).toNNReal) {r} := by
  let times : Fin 3 → NNReal :=
    fun i => if i = 0 then s else if i = 1 then t else u
  let marks : Fin 3 → Set E :=
    fun i => if i = 0 then A else if i = 1 then B else C
  let counts : Fin 3 → Nat :=
    fun i => if i = 0 then k else if i = 1 then l else r
  have hparams : ∀ i : Fin 3,
      (0 : NNReal) ≤ times i ∧
      MeasurableSet (marks i) ∧ n (marks i) < ⊤ := by
    intro i
    fin_cases i <;> simp [times, marks, hA, hB, hC,
      hFiniteA, hFiniteB, hFiniteC]
  have hdisjoint : ∀ i j : Fin 3, i ≠ j →
      times i ≤ 0 ∨ times j ≤ 0 ∨
      Disjoint (marks i) (marks j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [times, marks, hAB, hAC, hBC,
        hAB.symm, hAC.symm, hBC.symm]
  have h := hPPP.2.2 3
    (fun _ => 0) times marks counts hparams hdisjoint
  simpa [times, marks, counts, Fin.forall_fin_succ, Fin.prod_univ_succ, mul_assoc] using h
