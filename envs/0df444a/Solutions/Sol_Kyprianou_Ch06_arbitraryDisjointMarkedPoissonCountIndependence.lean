-- Prove2me | solution 1 for Kyprianou.Ch06.arbitraryDisjointMarkedPoissonCountIndependence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:01:03.108869+00:00
-- url     : https://prove2.me/submissions/def748f8-e2c5-46ad-bacd-01912b98f58f

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_markedPoissonMarginalCountLaw
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
    (m : Nat) (times : Fin m → NNReal)
    (B : Fin m → Set E) (counts : Fin m → Nat)
    (hB : ∀ i, MeasurableSet (B i) ∧ n (B i) < ⊤)
    (hDisj : ∀ i j : Fin m, i ≠ j → Disjoint (B i) (B j)) :
    P {omega | ∀ i : Fin m, N omega (times i) (B i) = counts i} =
      ∏ i : Fin m,
        P {omega | N omega (times i) (B i) = counts i} := by
  have hParams : ∀ i : Fin m,
      (0 : NNReal) ≤ times i ∧
      MeasurableSet (B i) ∧ n (B i) < ⊤ := by
    intro i
    exact ⟨zero_le, (hB i).1, (hB i).2⟩
  have hRectDisj : ∀ i j : Fin m, i ≠ j →
      times i ≤ 0 ∨ times j ≤ 0 ∨ Disjoint (B i) (B j) := by
    intro i j hij
    exact Or.inr (Or.inr (hDisj i j hij))
  have hRect :=
    hPPP.2.2 m (fun _ => 0) times B counts hParams hRectDisj
  have hZero : ∀ᵐ omega ∂P, ∀ i : Fin m, N omega 0 (B i) = 0 := by
    filter_upwards [hPPP.2.1] with omega hPath
    intro i
    exact hPath.1 (B i)
  have hAE : ∀ᵐ omega ∂P,
      (∀ i : Fin m, N omega (times i) (B i) = counts i) =
      (∀ i : Fin m,
        N omega (times i) (B i) - N omega 0 (B i) = counts i) := by
    filter_upwards [hZero] with omega hz
    apply propext
    constructor
    · intro h i
      simpa [hz i] using h i
    · intro h i
      simpa [hz i] using h i
  have hEq :
      P {omega | ∀ i : Fin m, N omega (times i) (B i) = counts i} =
      P {omega | ∀ i : Fin m,
        N omega (times i) (B i) - N omega 0 (B i) = counts i} := by
    apply measure_congr
    exact hAE
  calc
    P {omega | ∀ i : Fin m, N omega (times i) (B i) = counts i} =
      P {omega | ∀ i : Fin m,
        N omega (times i) (B i) - N omega 0 (B i) = counts i} := hEq
    _ = ∏ i : Fin m,
        ProbabilityTheory.poissonMeasure
          (times i * (n (B i)).toNNReal) {counts i} := by
          simpa using hRect
    _ = ∏ i : Fin m,
        P {omega | N omega (times i) (B i) = counts i} := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (Kyprianou.Ch06.markedPoissonMarginalCountLaw
        P n N hPPP (times i) (B i) (hB i).1 (hB i).2 (counts i)).symm
