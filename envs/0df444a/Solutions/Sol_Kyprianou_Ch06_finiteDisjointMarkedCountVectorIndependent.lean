-- Prove2me | solution 1 for Kyprianou.Ch06.finiteDisjointMarkedCountVectorIndependent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:30:58.261915+00:00
-- url     : https://prove2.me/submissions/9338f4dd-c8be-4b00-99f2-54f039e0fe07

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_markedPoissonMarginalCountLaw
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
    (k : Nat) (times : Fin k → NNReal)
    (marks : Fin k → Set E) (counts : Fin k → Nat)
    (hMarks : ∀ i, MeasurableSet (marks i) ∧ n (marks i) < ⊤)
    (hDisjoint : ∀ i j : Fin k, i ≠ j →
      Disjoint (marks i) (marks j)) :
    P {omega | ∀ i : Fin k, N omega (times i) (marks i) = counts i} =
    ∏ i : Fin k,
      P {omega | N omega (times i) (marks i) = counts i} := by
  have hStart : ∀ᵐ omega ∂P,
      ∀ i : Fin k, N omega 0 (marks i) = 0 := by
    filter_upwards [hPPP.2.1] with omega h
    exact fun i => h.1 (marks i)
  have hEvents : ∀ᵐ omega ∂P,
      (∀ i : Fin k, N omega (times i) (marks i) = counts i) =
      (∀ i : Fin k,
        N omega (times i) (marks i) - N omega 0 (marks i) =
          counts i) := by
    filter_upwards [hStart] with omega h
    simp [h]
  have hEqual :
      P {omega | ∀ i : Fin k, N omega (times i) (marks i) =
        counts i} =
      P {omega | ∀ i : Fin k,
        N omega (times i) (marks i) - N omega 0 (marks i) =
          counts i} := measure_congr hEvents
  have hRect :=
    hPPP.2.2 k (fun _ => 0) times marks counts
      (fun i => ⟨zero_le, (hMarks i).1, (hMarks i).2⟩)
      (by
        intro i j hij
        exact Or.inr (Or.inr (hDisjoint i j hij)))
  calc
    _ = P {omega | ∀ i : Fin k,
          N omega (times i) (marks i) - N omega 0 (marks i) =
            counts i} := hEqual
    _ = ∏ i : Fin k, ProbabilityTheory.poissonMeasure
          (times i * (n (marks i)).toNNReal) {counts i} := by
      simpa using hRect
    _ = ∏ i : Fin k,
          P {omega | N omega (times i) (marks i) = counts i} := by
      apply Finset.prod_congr rfl
      intro i _
      exact (Kyprianou.Ch06.markedPoissonMarginalCountLaw
        P n N hPPP (times i) (marks i)
        (hMarks i).1 (hMarks i).2 (counts i)).symm
