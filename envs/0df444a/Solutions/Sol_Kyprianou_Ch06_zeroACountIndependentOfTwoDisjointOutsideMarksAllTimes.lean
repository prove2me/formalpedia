-- Prove2me | solution 1 for Kyprianou.Ch06.zeroACountIndependentOfTwoDisjointOutsideMarksAllTimes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:22:03.125207+00:00
-- url     : https://prove2.me/submissions/c123333a-897f-403c-822c-f6dcf46afe2e

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
    (A B C : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C)
    (hFA : n A < ⊤) (hFB : n B < ⊤) (hFC : n C < ⊤)
    (r s t : NNReal) (k l : Nat) :
    P {omega | N omega r A = 0 ∧
      N omega s B = k ∧ N omega t C = l} =
    P {omega | N omega r A = 0} *
    P {omega | N omega s B = k ∧ N omega t C = l} := by
  let marks : Fin 2 → Set E := fun i => if i = 0 then B else C
  let clocks : Fin 2 → NNReal := fun i => if i = 0 then s else t
  let levels : Fin 2 → Nat := fun i => if i = 0 then k else l
  have hMeas : ∀ i : Fin 2,
      MeasurableSet (marks i) ∧ n (marks i) < ⊤ := by
    intro i
    fin_cases i <;> simp [marks, hB, hC, hFB, hFC]
  have hExternal : ∀ i : Fin 2, Disjoint A (marks i) := by
    intro i
    fin_cases i <;> simp [marks, hAB, hAC]
  have hPair : ∀ i j : Fin 2, i ≠ j →
      Disjoint (marks i) (marks j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [marks, hBC, hBC.symm]
  have hDisjoint :=
    Kyprianou.Ch06.zeroACountIndependentOfDisjointOutsideCylinder
      P n N hPPP A hA hFA 2 clocks marks levels
      hMeas hExternal hPair r
  simpa [marks, clocks, levels, Fin.forall_fin_two,
    and_assoc] using hDisjoint
