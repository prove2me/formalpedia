-- Prove2me | solution 1 for Kyprianou.Ch06.twoFirstArrivalsWithFiniteOutsideCountVectorIdentity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:15:57.737206+00:00
-- url     : https://prove2.me/submissions/9ab0dd0f-b857-47cb-a815-47b2430b5689

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstArrivalWithFiniteOutsideCountVector
import Theorems.Thm_Kyprianou_Ch06_firstArrivalWithFiniteOutsideSecondCountContinuous
import Theorems.Thm_Kyprianou_Ch06_firstArrivalJointEventFromContinuousZeroCount
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
      N omega s (marks (Fin.castAdd k (0 : Fin 2))) = 0 ∧
      N omega t (marks (Fin.castAdd k (1 : Fin 2))) = 0 ∧
      (∀ j : Fin k, N omega (outsideTimes j)
        (marks (Fin.natAdd 2 j)) = outsideCounts j)} := by
  let SB : Set Omega := {omega |
    (s : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 <
            N omega v (marks (Fin.castAdd k (0 : Fin 2)))})}
  let Cevent : Set Omega := {omega | omega ∈ SB ∧
    (∀ j : Fin k, N omega (outsideTimes j)
        (marks (Fin.natAdd 2 j)) = outsideCounts j)}
  have hInit : ∀ᵐ omega ∂P,
      N omega 0 (marks (Fin.castAdd k (1 : Fin 2))) = 0 :=
    hPPP.2.1.mono (fun omega h => h.1 _)
  have hMono : ∀ᵐ omega ∂P,
      Monotone (fun v : NNReal =>
        N omega v (marks (Fin.castAdd k (1 : Fin 2)))) :=
    hPPP.2.1.mono (fun omega h => h.2.2 _)
  have hCont : ContinuousAt (fun v : NNReal =>
      P {omega | N omega v (marks (Fin.castAdd k (1 : Fin 2))) = 0 ∧
        omega ∈ Cevent}) t :=
    Kyprianou.Ch06.firstArrivalWithFiniteOutsideSecondCountContinuous
      P n N hPPP k marks hMarks hDisjoint
      s t outsideTimes outsideCounts
  have hSecond :=
    Kyprianou.Ch06.firstArrivalJointEventFromContinuousZeroCount
      P N (marks (Fin.castAdd k (1 : Fin 2))) Cevent
      t hInit hMono hCont
  have hFirst :=
    Kyprianou.Ch06.firstArrivalWithFiniteOutsideCountVector
      P n N hPPP k marks hMarks hDisjoint
      s t outsideTimes outsideCounts
  calc
    _ = P {omega |
      (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 <
            N omega v (marks (Fin.castAdd k (1 : Fin 2)))}) ∧
      omega ∈ Cevent} := by
        congr 1
        ext omega
        simp only [Cevent, SB, Set.mem_setOf_eq]
        tauto
    _ = P {omega |
      N omega t (marks (Fin.castAdd k (1 : Fin 2))) = 0 ∧
      omega ∈ Cevent} := hSecond
    _ = P {omega |
      (s : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 <
            N omega v (marks (Fin.castAdd k (0 : Fin 2)))}) ∧
      N omega t (marks (Fin.castAdd k (1 : Fin 2))) = 0 ∧
      (∀ j : Fin k, N omega (outsideTimes j)
        (marks (Fin.natAdd 2 j)) = outsideCounts j)} := by
        congr 1
        ext omega
        change
          (N omega t (marks (Fin.castAdd k (1 : Fin 2))) = 0 ∧
           ((s : WithTop NNReal) <
             sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
               {v : NNReal | 0 < v ∧ 0 <
                 N omega v (marks (Fin.castAdd k (0 : Fin 2)))}) ∧
           (∀ j : Fin k, N omega (outsideTimes j)
             (marks (Fin.natAdd 2 j)) = outsideCounts j))) ↔
          ((s : WithTop NNReal) <
             sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
               {v : NNReal | 0 < v ∧ 0 <
                 N omega v (marks (Fin.castAdd k (0 : Fin 2)))}) ∧
           N omega t (marks (Fin.castAdd k (1 : Fin 2))) = 0 ∧
           (∀ j : Fin k, N omega (outsideTimes j)
             (marks (Fin.natAdd 2 j)) = outsideCounts j))
        tauto
    _ = _ := hFirst
