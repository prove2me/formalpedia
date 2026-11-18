-- Prove2me | solution 1 for Kyprianou.Ch06.twoZeroCountsWithFiniteOutsideVectorContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T11:21:08.266822+00:00
-- url     : https://prove2.me/submissions/417e4ea1-1b90-4110-8119-9ce54dea3df4

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
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (k : Nat) (marks : Fin (2 + k) → Set E)
    (hMarks : ∀ i, MeasurableSet (marks i) ∧ n (marks i) < ⊤)
    (hDisjoint : ∀ i j : Fin (2 + k), i ≠ j →
      Disjoint (marks i) (marks j))
    (s t : NNReal) (outsideTimes : Fin k → NNReal)
    (outsideCounts : Fin k → Nat) :
    ContinuousAt (fun v : NNReal =>
      P {omega |
      N omega v (marks (Fin.castAdd k (0 : Fin 2))) = 0 ∧
      N omega t (marks (Fin.castAdd k (1 : Fin 2))) = 0 ∧
      (∀ j : Fin k, N omega (outsideTimes j)
        (marks (Fin.natAdd 2 j)) = outsideCounts j)}) s := by
  have hMass : P Set.univ = 1 := by
    have hRect :=
      hPPP.2.2 0 (fun _ => 0) (fun _ => 0)
        (fun _ => (∅ : Set E)) (fun _ => 0)
        (by intro i; exact Fin.elim0 i)
        (by intro i; exact Fin.elim0 i)
    simpa using hRect
  letI : IsProbabilityMeasure P := ⟨hMass⟩
  have hIndex : (Fin.castAdd k (0 : Fin 2)) ≠
      Fin.castAdd k (1 : Fin 2) := by
    intro heq
    exact (by decide : (0 : Fin 2) ≠ 1)
      ((Fin.castAdd_injective 2 k) heq)
  have hContinuity : ContinuousAt
      (fun v : NNReal =>
        P {omega | N omega v (marks (Fin.castAdd k (0 : Fin 2))) = 0 ∧
          N omega t (marks (Fin.castAdd k (1 : Fin 2))) = 0}) s :=
    Kyprianou.Ch06.disjointMarkedPoissonZeroCountJointContinuous
      P n N hPPP
      (marks (Fin.castAdd k (0 : Fin 2))) (marks (Fin.castAdd k (1 : Fin 2)))
      (hMarks _).1 (hMarks _).1
      (hDisjoint _ _ hIndex)
      (hMarks _).2 (hMarks _).2 s t 0
  have hFunc :
      (fun v : NNReal => P {omega |
      N omega v (marks (Fin.castAdd k (0 : Fin 2))) = 0 ∧
      N omega t (marks (Fin.castAdd k (1 : Fin 2))) = 0 ∧
      (∀ j : Fin k, N omega (outsideTimes j)
        (marks (Fin.natAdd 2 j)) = outsideCounts j)}) =
      (fun v : NNReal => P {omega | N omega v (marks (Fin.castAdd k (0 : Fin 2))) = 0 ∧
        N omega t (marks (Fin.castAdd k (1 : Fin 2))) = 0} *
        P {omega | (∀ j : Fin k, N omega (outsideTimes j)
        (marks (Fin.natAdd 2 j)) = outsideCounts j)}) := by
    funext v
    exact
      Kyprianou.Ch06.disjointTwoZeroCountsIndependentOfFiniteOutsideVector
        P n N hPPP k marks hMarks hDisjoint
        v t outsideTimes outsideCounts
  rw [hFunc]
  have hFinite :
      P {omega | ∀ j : Fin k,
        N omega (outsideTimes j)
          (marks (Fin.natAdd 2 j)) = outsideCounts j} ≠ ⊤ :=
    measure_ne_top P _
  exact (ENNReal.continuous_mul_const hFinite).continuousAt.comp
    hContinuity
