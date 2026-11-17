-- Prove2me | solution 1 for Kyprianou.Ch06.zeroACountIndependentOfThreeDisjointOutsideCounts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T12:18:46.929331+00:00
-- url     : https://prove2.me/submissions/868817da-e9d2-493c-b680-a09fa9a3d31b

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfDisjointOutsideCylinder
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
    (A B C D : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hD : MeasurableSet D)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hAD : Disjoint A D) (hBC : Disjoint B C)
    (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hFA : n A < ⊤) (hFB : n B < ⊤)
    (hFC : n C < ⊤) (hFD : n D < ⊤)
    (s t : NNReal) (k l q : Nat) :
    P {omega | N omega s A = 0 ∧ N omega t B = k ∧
      N omega t C = l ∧ N omega t D = q} =
    P {omega | N omega s A = 0} *
    P {omega | N omega t B = k ∧ N omega t C = l ∧
      N omega t D = q} := by
  let marks : Fin 3 → Set E := fun i =>
    if i = 0 then B else if i = 1 then C else D
  let clocks : Fin 3 → NNReal := fun _ => t
  let levels : Fin 3 → Nat := fun i =>
    if i = 0 then k else if i = 1 then l else q
  have hMeas : ∀ i : Fin 3,
      MeasurableSet (marks i) ∧ n (marks i) < ⊤ := by
    intro i
    fin_cases i <;> norm_num [marks, hB, hC, hD, hFB, hFC, hFD]
  have hExternal : ∀ i : Fin 3, Disjoint A (marks i) := by
    intro i
    fin_cases i <;> norm_num [marks, hAB, hAC, hAD]
  have hDisj : ∀ i j : Fin 3, i ≠ j →
      Disjoint (marks i) (marks j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [marks, hBC, hBD, hCD,
        hBC.symm, hBD.symm, hCD.symm]
  have hMain :=
    Kyprianou.Ch06.zeroACountIndependentOfDisjointOutsideCylinder
      P n N hPPP A hA hFA 3 clocks marks levels
      hMeas hExternal hDisj s
  simpa [marks, clocks, levels, Fin.forall_fin_succ] using hMain
