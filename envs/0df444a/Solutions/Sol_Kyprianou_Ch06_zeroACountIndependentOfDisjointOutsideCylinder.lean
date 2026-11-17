-- Prove2me | solution 1 for Kyprianou.Ch06.zeroACountIndependentOfDisjointOutsideCylinder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:01:10.698252+00:00
-- url     : https://prove2.me/submissions/1f6823d5-dcc4-4bdc-83e6-60e65009a74e

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_arbitraryDisjointMarkedPoissonCountIndependence
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
    (m : Nat) (times : Fin m → NNReal)
    (B : Fin m → Set E) (counts : Fin m → Nat)
    (hB : ∀ i, MeasurableSet (B i) ∧ n (B i) < ⊤)
    (hAB : ∀ i, Disjoint A (B i))
    (hBij : ∀ i j : Fin m, i ≠ j → Disjoint (B i) (B j))
    (t : NNReal) :
    P {omega | N omega t A = 0 ∧
      ∀ i : Fin m, N omega (times i) (B i) = counts i} =
      P {omega | N omega t A = 0} *
      P {omega | ∀ i : Fin m,
        N omega (times i) (B i) = counts i} := by
  let marks : Fin (m+1) → Set E := Fin.cons A B
  let clocks : Fin (m+1) → NNReal := Fin.cons t times
  let levels : Fin (m+1) → Nat := Fin.cons 0 counts
  have hTotal : ∀ i : Fin (m+1),
      MeasurableSet (marks i) ∧ n (marks i) < ⊤ := by
    intro i
    cases i using Fin.cases with
    | zero => exact ⟨hA, hFA⟩
    | succ i => exact hB i
  have hDisj : ∀ i j : Fin (m+1), i ≠ j →
      Disjoint (marks i) (marks j) := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero => exact False.elim (hij rfl)
        | succ j => exact hAB j
    | succ i =>
        cases j using Fin.cases with
        | zero => exact (hAB i).symm
        | succ j =>
            have hij' : i ≠ j := by
              intro hEq
              apply hij
              simpa [hEq]
            exact hBij i j hij'
  have hOne :=
    Kyprianou.Ch06.arbitraryDisjointMarkedPoissonCountIndependence
      P n N hPPP (m+1) clocks marks levels hTotal hDisj
  have hOther :=
    Kyprianou.Ch06.arbitraryDisjointMarkedPoissonCountIndependence
      P n N hPPP m times B counts hB hBij
  have hFactor :
      P {omega | N omega t A = 0 ∧
        ∀ i : Fin m, N omega (times i) (B i) = counts i} =
      P {omega | N omega t A = 0} *
        ∏ i : Fin m,
          P {omega | N omega (times i) (B i) = counts i} := by
    simpa [marks, clocks, levels, Fin.forall_fin_succ,
      Fin.prod_univ_succ] using hOne
  calc
    P {omega | N omega t A = 0 ∧
      ∀ i : Fin m, N omega (times i) (B i) = counts i} =
        P {omega | N omega t A = 0} *
          ∏ i : Fin m,
            P {omega | N omega (times i) (B i) = counts i} := hFactor
    _ = P {omega | N omega t A = 0} *
        P {omega | ∀ i : Fin m,
          N omega (times i) (B i) = counts i} := by
      rw [hOther]
