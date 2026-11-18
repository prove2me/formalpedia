-- Prove2me | solution 1 for Kyprianou.Ch06.disjointTwoZeroCountsIndependentOfFiniteOutsideVector
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T10:59:41.780843+00:00
-- url     : https://prove2.me/submissions/3443a38b-24b1-4e28-8ec5-e6476a023da6

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_disjointMarkedCountVectorTwoPlusRestIndependent
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
    (k : Nat) (marks : Fin (2 + k) → Set E)
    (hMarks : ∀ i, MeasurableSet (marks i) ∧ n (marks i) < ⊤)
    (hDisjoint : ∀ i j : Fin (2 + k), i ≠ j →
      Disjoint (marks i) (marks j))
    (s t : NNReal) (outsideTimes : Fin k → NNReal)
    (outsideCounts : Fin k → Nat) :
    P {omega |
      N omega s (marks (Fin.castAdd k (0 : Fin 2))) = 0 ∧
      N omega t (marks (Fin.castAdd k (1 : Fin 2))) = 0 ∧
      (∀ j : Fin k, N omega (outsideTimes j)
        (marks (Fin.natAdd 2 j)) = outsideCounts j)} =
    P {omega |
      N omega s (marks (Fin.castAdd k (0 : Fin 2))) = 0 ∧
      N omega t (marks (Fin.castAdd k (1 : Fin 2))) = 0} *
    P {omega | ∀ j : Fin k, N omega (outsideTimes j)
      (marks (Fin.natAdd 2 j)) = outsideCounts j} := by
  classical
  let times : Fin (2 + k) → NNReal :=
    Fin.append (![s, t]) outsideTimes
  let counts : Fin (2 + k) → Nat :=
    Fin.append (![0, 0]) outsideCounts
  have hProduct :=
    Kyprianou.Ch06.disjointMarkedCountVectorTwoPlusRestIndependent
      P n N hPPP k times marks counts hMarks hDisjoint
  have hTwo (omega : Omega) :
      (∀ i : Fin 2, N omega (times (Fin.castAdd k i))
        (marks (Fin.castAdd k i)) = counts (Fin.castAdd k i)) ↔
      N omega s (marks (Fin.castAdd k (0 : Fin 2))) = 0 ∧
      N omega t (marks (Fin.castAdd k (1 : Fin 2))) = 0 := by
    constructor
    · intro h
      exact ⟨by simpa [times, counts] using h 0,
        by simpa [times, counts] using h 1⟩
    · rintro ⟨h0, h1⟩ i
      fin_cases i
      · simpa [times, counts] using h0
      · simpa [times, counts] using h1
  have hRest (omega : Omega) :
      (∀ j : Fin k, N omega (times (Fin.natAdd 2 j))
        (marks (Fin.natAdd 2 j)) = counts (Fin.natAdd 2 j)) ↔
      (∀ j : Fin k, N omega (outsideTimes j)
        (marks (Fin.natAdd 2 j)) = outsideCounts j) := by
    simp [times, counts]
  calc
    _ = P {omega |
      (∀ i : Fin 2, N omega (times (Fin.castAdd k i))
        (marks (Fin.castAdd k i)) = counts (Fin.castAdd k i)) ∧
      (∀ j : Fin k, N omega (times (Fin.natAdd 2 j))
        (marks (Fin.natAdd 2 j)) = counts (Fin.natAdd 2 j))} := by
      congr 1
      ext omega
      simpa only [Set.mem_setOf_eq, and_assoc] using
        (and_congr (hTwo omega).symm (hRest omega).symm)
    _ = P {omega | ∀ i : Fin 2,
        N omega (times (Fin.castAdd k i))
          (marks (Fin.castAdd k i)) = counts (Fin.castAdd k i)} *
      P {omega | ∀ j : Fin k,
        N omega (times (Fin.natAdd 2 j))
          (marks (Fin.natAdd 2 j)) = counts (Fin.natAdd 2 j)} := hProduct
    _ = _ := by
      congr 1
      · congr 1
        ext omega
        exact hTwo omega
      · congr 1
        ext omega
        exact hRest omega
