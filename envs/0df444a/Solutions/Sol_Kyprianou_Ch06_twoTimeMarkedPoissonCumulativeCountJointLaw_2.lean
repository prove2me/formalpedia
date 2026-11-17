-- Prove2me | solution 2 for Kyprianou.Ch06.twoTimeMarkedPoissonCumulativeCountJointLaw
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:12:50.649293+00:00
-- url     : https://prove2.me/submissions/a0cb97be-ab72-4e04-b83e-c82e6cf203c2

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.twoTimeMarkedPoissonCumulativeCountJointLaw
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A : Set E) (hA : MeasurableSet A) (hFinite : n A < ⊤)
    (s t : NNReal) (hst : s ≤ t) (k l : Nat) :
    P {omega | N omega s A = k ∧ N omega t A = k+l} =
    ProbabilityTheory.poissonMeasure
      (s * (n A).toNNReal) {k} *
    ProbabilityTheory.poissonMeasure
      ((t-s) * (n A).toNNReal) {l} := by
  have key := hPPP.2.2 2 ![0, s] ![s, t] ![A, A] ![k, l]
    (by intro i; fin_cases i <;> simp [hA, hFinite, hst])
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
  simp only [Fin.prod_univ_two] at key
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, tsub_zero] at key
  rw [← key]
  apply measure_congr
  filter_upwards [hPPP.2.1] with omega h
  have h0 := h.1 A
  have hm : N omega s A ≤ N omega t A := h.2.2 A hst
  change (N omega s A = k ∧ N omega t A = k + l) =
    (∀ i : Fin 2, N omega (![s, t] i) (![A, A] i) - N omega (![0, s] i) (![A, A] i) = ![k, l] i)
  rw [eq_iff_iff, Fin.forall_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, h0, tsub_zero]
  omega

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A : Set E) (hA : MeasurableSet A) (hFinite : n A < ⊤)
    (s t : NNReal) (hst : s ≤ t) (k l : Nat) :
    P {omega | N omega s A = k ∧ N omega t A = k+l} =
    ProbabilityTheory.poissonMeasure
      (s * (n A).toNNReal) {k} *
    ProbabilityTheory.poissonMeasure
      ((t-s) * (n A).toNNReal) {l} :=
  Kyprianou.Ch06.twoTimeMarkedPoissonCumulativeCountJointLaw P n N hPPP A hA hFinite s t hst k l
