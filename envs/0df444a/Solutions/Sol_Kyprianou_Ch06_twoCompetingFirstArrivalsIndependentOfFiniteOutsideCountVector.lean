-- Prove2me | solution 1 for Kyprianou.Ch06.twoCompetingFirstArrivalsIndependentOfFiniteOutsideCountVector
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:19:44.787093+00:00
-- url     : https://prove2.me/submissions/1858ca7a-f73c-4d87-b7b2-c4615ae3a078

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_twoFirstArrivalsWithFiniteOutsideCountVectorIdentity
import Theorems.Thm_Kyprianou_Ch06_disjointTwoZeroCountsIndependentOfFiniteOutsideVector
import Theorems.Thm_Kyprianou_Ch06_firstArrivalTwoDisjointJointSurvivalIsZeroCount
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
    P {omega |
      (s : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 <
            N omega v (marks (Fin.castAdd k (0 : Fin 2)))}) ∧
      (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 <
            N omega v (marks (Fin.castAdd k (1 : Fin 2)))}) ∧
      (∀ j : Fin k, N omega (outsideTimes j)
        (marks (Fin.natAdd 2 j)) = outsideCounts j)} =
    P {omega |
      (s : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 <
            N omega v (marks (Fin.castAdd k (0 : Fin 2)))}) ∧
      (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 <
            N omega v (marks (Fin.castAdd k (1 : Fin 2)))})} *
    P {omega | (∀ j : Fin k, N omega (outsideTimes j)
        (marks (Fin.natAdd 2 j)) = outsideCounts j)} := by
  have hIndex : (Fin.castAdd k (0 : Fin 2)) ≠
      Fin.castAdd k (1 : Fin 2) := by
    intro heq
    exact (by decide : (0 : Fin 2) ≠ 1)
      ((Fin.castAdd_injective 2 k) heq)
  rw [Kyprianou.Ch06.twoFirstArrivalsWithFiniteOutsideCountVectorIdentity
        P n N hPPP k marks hMarks hDisjoint
        s t outsideTimes outsideCounts,
      Kyprianou.Ch06.disjointTwoZeroCountsIndependentOfFiniteOutsideVector
        P n N hPPP k marks hMarks hDisjoint
        s t outsideTimes outsideCounts,
      ← Kyprianou.Ch06.firstArrivalTwoDisjointJointSurvivalIsZeroCount
        P n N hPPP
        (marks (Fin.castAdd k (0 : Fin 2)))
        (marks (Fin.castAdd k (1 : Fin 2)))
        (hMarks _).1 (hMarks _).1
        (hDisjoint _ _ hIndex)
        (hMarks _).2 (hMarks _).2 s t]
