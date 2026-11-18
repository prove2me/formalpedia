-- Prove2me | solution 1 for Kyprianou.Ch06.disjointMarkedCountVectorTwoPlusRestIndependent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:35:53.079192+00:00
-- url     : https://prove2.me/submissions/7499ae7e-9325-409a-8e6c-235bd09cbdbb

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_finiteDisjointMarkedCountVectorIndependent
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
    (k : Nat) (times : Fin (2 + k) → NNReal)
    (marks : Fin (2 + k) → Set E)
    (counts : Fin (2 + k) → Nat)
    (hMarks : ∀ i, MeasurableSet (marks i) ∧ n (marks i) < ⊤)
    (hDisjoint : ∀ i j : Fin (2 + k), i ≠ j →
      Disjoint (marks i) (marks j)) :
    P {omega |
      (∀ i : Fin 2, N omega (times (Fin.castAdd k i))
        (marks (Fin.castAdd k i)) = counts (Fin.castAdd k i)) ∧
      (∀ j : Fin k, N omega (times (Fin.natAdd 2 j))
        (marks (Fin.natAdd 2 j)) = counts (Fin.natAdd 2 j))} =
    P {omega | ∀ i : Fin 2,
      N omega (times (Fin.castAdd k i))
        (marks (Fin.castAdd k i)) = counts (Fin.castAdd k i)} *
    P {omega | ∀ j : Fin k,
      N omega (times (Fin.natAdd 2 j))
        (marks (Fin.natAdd 2 j)) = counts (Fin.natAdd 2 j)} := by
  have hFirst : ∀ i j : Fin 2, i ≠ j →
      Disjoint (marks (Fin.castAdd k i))
        (marks (Fin.castAdd k j)) := by
    intro i j hij
    apply hDisjoint
    intro heq
    exact hij ((Fin.castAdd_injective 2 k) heq)
  have hRest : ∀ i j : Fin k, i ≠ j →
      Disjoint (marks (Fin.natAdd 2 i))
        (marks (Fin.natAdd 2 j)) := by
    intro i j hij
    apply hDisjoint
    intro heq
    exact hij ((Fin.natAdd_injective k 2) heq)
  have hFull :=
    Kyprianou.Ch06.finiteDisjointMarkedCountVectorIndependent
      P n N hPPP (2 + k) times marks counts hMarks hDisjoint
  have hPart1 :=
    Kyprianou.Ch06.finiteDisjointMarkedCountVectorIndependent
      P n N hPPP 2
      (fun i => times (Fin.castAdd k i))
      (fun i => marks (Fin.castAdd k i))
      (fun i => counts (Fin.castAdd k i))
      (fun i => hMarks (Fin.castAdd k i)) hFirst
  have hPart2 :=
    Kyprianou.Ch06.finiteDisjointMarkedCountVectorIndependent
      P n N hPPP k
      (fun i => times (Fin.natAdd 2 i))
      (fun i => marks (Fin.natAdd 2 i))
      (fun i => counts (Fin.natAdd 2 i))
      (fun i => hMarks (Fin.natAdd 2 i)) hRest
  have hEvents :
      P {omega | (∀ i : Fin 2,
        N omega (times (Fin.castAdd k i))
          (marks (Fin.castAdd k i)) = counts (Fin.castAdd k i)) ∧
        (∀ j : Fin k,
          N omega (times (Fin.natAdd 2 j))
            (marks (Fin.natAdd 2 j)) = counts (Fin.natAdd 2 j))} =
      P {omega | ∀ i : Fin (2 + k),
        N omega (times i) (marks i) = counts i} := by
    congr 1
    ext omega
    exact (Fin.forall_fin_add
      (fun i : Fin (2 + k) =>
        N omega (times i) (marks i) = counts i)).symm
  calc
    _ = P {omega | ∀ i : Fin (2 + k),
          N omega (times i) (marks i) = counts i} := hEvents
    _ = ∏ i : Fin (2 + k),
          P {omega | N omega (times i) (marks i) = counts i} := hFull
    _ = (∏ i : Fin 2, P {omega |
          N omega (times (Fin.castAdd k i))
            (marks (Fin.castAdd k i)) = counts (Fin.castAdd k i)}) *
        (∏ j : Fin k, P {omega |
          N omega (times (Fin.natAdd 2 j))
            (marks (Fin.natAdd 2 j)) = counts (Fin.natAdd 2 j)}) := by
      exact Fin.prod_univ_add _
    _ = _ := by rw [← hPart1, ← hPart2]
