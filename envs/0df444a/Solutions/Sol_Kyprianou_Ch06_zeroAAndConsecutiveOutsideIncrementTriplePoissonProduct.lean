-- Prove2me | solution 1 for Kyprianou.Ch06.zeroAAndConsecutiveOutsideIncrementTriplePoissonProduct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:11:25.272545+00:00
-- url     : https://prove2.me/submissions/7eb13e80-d0f8-4d24-88e0-9b8b959529ee

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
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (hFA : n A < ⊤) (hFB : n B < ⊤)
    (r s t : NNReal) (hst : s ≤ t) (k l : Nat) :
    P {omega | N omega r A - N omega 0 A = 0 ∧
      N omega s B - N omega 0 B = k ∧
      N omega t B - N omega s B = l} =
    ProbabilityTheory.poissonMeasure (r * (n A).toNNReal) {0} *
      (ProbabilityTheory.poissonMeasure (s * (n B).toNNReal) {k} *
        ProbabilityTheory.poissonMeasure ((t-s) * (n B).toNNReal) {l}) := by
  let start : Fin 3 → NNReal := fun i => if i = 2 then s else 0
  let stop : Fin 3 → NNReal :=
    fun i => if i = 0 then r else if i = 1 then s else t
  let marks : Fin 3 → Set E := fun i => if i = 0 then A else B
  let levels : Fin 3 → Nat :=
    fun i => if i = 0 then 0 else if i = 1 then k else l
  have hparams : ∀ i : Fin 3,
      start i ≤ stop i ∧
      MeasurableSet (marks i) ∧ n (marks i) < ⊤ := by
    intro i
    fin_cases i <;> simp [start, stop, marks, hA, hB, hFA, hFB, hst]
  have hpair : ∀ i j : Fin 3, i ≠ j →
      stop i ≤ start j ∨ stop j ≤ start i ∨
      Disjoint (marks i) (marks j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [start, stop, marks, hAB, hAB.symm]
  have h3 := hPPP.2.2 3 start stop marks levels hparams hpair
  simpa [start, stop, marks, levels, Fin.forall_fin_succ,
    Fin.prod_univ_succ, mul_assoc] using h3
