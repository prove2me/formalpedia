-- Prove2me | solution 1 for Kyprianou.Ch06.twoDisjointMarkedPoissonRectangles
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:10:46.323917+00:00
-- url     : https://prove2.me/submissions/589b8290-1a31-428e-b297-acb42f0a5776

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
    (A B : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : Disjoint A B)
    (hFiniteA : n A < ⊤) (hFiniteB : n B < ⊤)
    (s t : NNReal) (k l : Nat) :
    P {omega | N omega s A - N omega 0 A = k ∧
      N omega t B - N omega 0 B = l} =
    ProbabilityTheory.poissonMeasure
      (s * (n A).toNNReal) {k} *
    ProbabilityTheory.poissonMeasure
      (t * (n B).toNNReal) {l} := by
  have hparams : ∀ i : Fin 2,
      (0 : NNReal) ≤ (if i = 0 then s else t) ∧
      MeasurableSet (if i = 0 then A else B) ∧
      n (if i = 0 then A else B) < ⊤ := by
    intro i
    fin_cases i <;> simp [hA, hB, hFiniteA, hFiniteB]
  have hdisjoint : ∀ i j : Fin 2, i ≠ j →
      (if i = 0 then s else t) ≤ 0 ∨
      (if j = 0 then s else t) ≤ 0 ∨
      Disjoint (if i = 0 then A else B)
        (if j = 0 then A else B) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [hAB, hAB.symm]
  have h := hPPP.2.2 2
    (fun _ => 0)
    (fun i => if i = 0 then s else t)
    (fun i => if i = 0 then A else B)
    (fun i => if i = 0 then k else l)
    hparams hdisjoint
  simpa [Fin.forall_fin_two, Fin.prod_univ_two] using h
