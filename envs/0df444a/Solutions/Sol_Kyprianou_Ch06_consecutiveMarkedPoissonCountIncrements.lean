-- Prove2me | solution 1 for Kyprianou.Ch06.consecutiveMarkedPoissonCountIncrements
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:06:00.71619+00:00
-- url     : https://prove2.me/submissions/c7d2f481-59bb-489c-8c87-3826f9c83686

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A : Set E) (hA : MeasurableSet A) (hFinite : n A < ⊤)
    (s t : NNReal) (hst : s ≤ t) (k l : Nat) :
    P {omega | N omega s A - N omega 0 A = k ∧
      N omega t A - N omega s A = l} =
    ProbabilityTheory.poissonMeasure
      (s * (n A).toNNReal) {k} *
    ProbabilityTheory.poissonMeasure
      ((t-s) * (n A).toNNReal) {l} := by
  have hparams : ∀ i : Fin 2,
      (if i = 0 then (0 : NNReal) else s) ≤
        (if i = 0 then s else t) ∧
      MeasurableSet A ∧ n A < ⊤ := by
    intro i
    fin_cases i <;> simp [hA, hFinite, hst]
  have hdisjoint : ∀ i j : Fin 2, i ≠ j →
      (if i = 0 then s else t) ≤
        (if j = 0 then (0 : NNReal) else s) ∨
      (if j = 0 then s else t) ≤
        (if i = 0 then (0 : NNReal) else s) ∨
      Disjoint A A := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h :=
    hPPP.2.2 2
      (fun i => if i = 0 then 0 else s)
      (fun i => if i = 0 then s else t)
      (fun _ => A)
      (fun i => if i = 0 then k else l)
      hparams hdisjoint
  simpa [Fin.forall_fin_two, Fin.prod_univ_two] using h
