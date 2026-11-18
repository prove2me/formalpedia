-- Prove2me | solution 1 for Kyprianou.Ch06.secondZeroCountWithFiniteOutsideVectorContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T11:21:16.757401+00:00
-- url     : https://prove2.me/submissions/7bf240e7-5ee3-4b0a-9753-54d7dcf9d78b

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_disjointTwoZeroCountsIndependentOfFiniteOutsideVector
import Theorems.Thm_Kyprianou_Ch06_disjointMarkedPoissonZeroCountJointContinuous
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (k : Nat) (marks : Fin (2 + k) → Set E)
    (hMarks : ∀ i, MeasurableSet (marks i) ∧ n (marks i) < ⊤)
    (hDisjoint : ∀ i j : Fin (2 + k), i ≠ j →
      Disjoint (marks i) (marks j))
    (s t : NNReal) (outsideTimes : Fin k → NNReal)
    (outsideCounts : Fin k → Nat) :
    ContinuousAt (fun v : NNReal =>
      P {omega |
        N omega s (marks (Fin.castAdd k (0 : Fin 2))) = 0 ∧
        N omega v (marks (Fin.castAdd k (1 : Fin 2))) = 0 ∧
        (∀ j : Fin k, N omega (outsideTimes j)
          (marks (Fin.natAdd 2 j)) = outsideCounts j)}) t := by
  have hIndex : (Fin.castAdd k (0 : Fin 2)) ≠
      Fin.castAdd k (1 : Fin 2) := by
    intro heq
    exact (by decide : (0 : Fin 2) ≠ 1)
      ((Fin.castAdd_injective 2 k) heq)
  have hPair : ContinuousAt
      (fun v : NNReal =>
        P {omega |
          N omega s (marks (Fin.castAdd k (0 : Fin 2))) = 0 ∧
          N omega v (marks (Fin.castAdd k (1 : Fin 2))) = 0}) t := by
    simpa only [and_comm] using
      (Kyprianou.Ch06.disjointMarkedPoissonZeroCountJointContinuous
        P n N hPPP
        (marks (Fin.castAdd k (1 : Fin 2)))
        (marks (Fin.castAdd k (0 : Fin 2)))
        (hMarks _).1 (hMarks _).1
        (hDisjoint _ _ hIndex.symm)
        (hMarks _).2 (hMarks _).2 t s 0)
  have hFactor :
      (fun v : NNReal =>
        P {omega |
          N omega s (marks (Fin.castAdd k (0 : Fin 2))) = 0 ∧
          N omega v (marks (Fin.castAdd k (1 : Fin 2))) = 0 ∧
          (∀ j : Fin k, N omega (outsideTimes j)
            (marks (Fin.natAdd 2 j)) = outsideCounts j)}) =
      (fun v : NNReal =>
        P {omega |
          N omega s (marks (Fin.castAdd k (0 : Fin 2))) = 0 ∧
          N omega v (marks (Fin.castAdd k (1 : Fin 2))) = 0} *
        P {omega | ∀ j : Fin k, N omega (outsideTimes j)
          (marks (Fin.natAdd 2 j)) = outsideCounts j}) := by
    funext v
    exact
      Kyprianou.Ch06.disjointTwoZeroCountsIndependentOfFiniteOutsideVector
        P n N hPPP k marks hMarks hDisjoint
        s v outsideTimes outsideCounts
  rw [hFactor]
  have hFinite :
      P {omega | ∀ j : Fin k,
        N omega (outsideTimes j)
          (marks (Fin.natAdd 2 j)) = outsideCounts j} ≠ ⊤ :=
    measure_ne_top P _
  exact (ENNReal.continuous_mul_const hFinite).continuousAt.comp hPair
