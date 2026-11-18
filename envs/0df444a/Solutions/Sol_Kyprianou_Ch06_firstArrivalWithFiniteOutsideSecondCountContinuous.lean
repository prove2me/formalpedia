-- Prove2me | solution 1 for Kyprianou.Ch06.firstArrivalWithFiniteOutsideSecondCountContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T11:28:40.214604+00:00
-- url     : https://prove2.me/submissions/1315e319-2551-4bec-af4e-a73ac222eb42

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstArrivalWithFiniteOutsideCountVector
import Theorems.Thm_Kyprianou_Ch06_secondZeroCountWithFiniteOutsideVectorContinuous
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
        N omega v (marks (Fin.castAdd k (1 : Fin 2))) = 0 ∧
        (s : WithTop NNReal) <
          sInf ((fun w : NNReal => (w : WithTop NNReal)) ''
            {w : NNReal | 0 < w ∧ 0 <
              N omega w (marks (Fin.castAdd k (0 : Fin 2)))}) ∧
        (∀ j : Fin k, N omega (outsideTimes j)
          (marks (Fin.natAdd 2 j)) = outsideCounts j)}) t := by
  let SB : Set Omega := {omega |
    (s : WithTop NNReal) <
      sInf ((fun w : NNReal => (w : WithTop NNReal)) ''
        {w : NNReal | 0 < w ∧ 0 <
          N omega w (marks (Fin.castAdd k (0 : Fin 2)))})}
  have hEq (v : NNReal) :
      P {omega | N omega v (marks (Fin.castAdd k (1 : Fin 2))) = 0 ∧
        omega ∈ SB ∧
        (∀ j : Fin k, N omega (outsideTimes j)
          (marks (Fin.natAdd 2 j)) = outsideCounts j)} =
      P {omega |
        N omega s (marks (Fin.castAdd k (0 : Fin 2))) = 0 ∧
        N omega v (marks (Fin.castAdd k (1 : Fin 2))) = 0 ∧
        (∀ j : Fin k, N omega (outsideTimes j)
          (marks (Fin.natAdd 2 j)) = outsideCounts j)} := by
    have hFirst :=
      Kyprianou.Ch06.firstArrivalWithFiniteOutsideCountVector
        P n N hPPP k marks hMarks hDisjoint
        s v outsideTimes outsideCounts
    simpa only [SB, Set.mem_setOf_eq,
      and_assoc, and_left_comm, and_comm] using hFirst
  have hFunc :
      (fun v : NNReal =>
        P {omega | N omega v (marks (Fin.castAdd k (1 : Fin 2))) = 0 ∧
          omega ∈ SB ∧
          (∀ j : Fin k, N omega (outsideTimes j)
            (marks (Fin.natAdd 2 j)) = outsideCounts j)}) =
      (fun v : NNReal =>
        P {omega | N omega s (marks (Fin.castAdd k (0 : Fin 2))) = 0 ∧
          N omega v (marks (Fin.castAdd k (1 : Fin 2))) = 0 ∧
          (∀ j : Fin k, N omega (outsideTimes j)
            (marks (Fin.natAdd 2 j)) = outsideCounts j)}) :=
    funext hEq
  change ContinuousAt (fun v : NNReal =>
    P {omega | N omega v (marks (Fin.castAdd k (1 : Fin 2))) = 0 ∧
      omega ∈ SB ∧
      (∀ j : Fin k, N omega (outsideTimes j)
        (marks (Fin.natAdd 2 j)) = outsideCounts j)}) t
  rw [hFunc]
  exact Kyprianou.Ch06.secondZeroCountWithFiniteOutsideVectorContinuous
    P n N hPPP k marks hMarks hDisjoint
    s t outsideTimes outsideCounts
