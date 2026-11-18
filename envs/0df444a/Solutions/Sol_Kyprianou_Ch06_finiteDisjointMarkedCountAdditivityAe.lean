-- Prove2me | solution 1 for Kyprianou.Ch06.finiteDisjointMarkedCountAdditivityAe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:11:59.701843+00:00
-- url     : https://prove2.me/submissions/4106ea21-5f2b-4359-a027-fa87292b1f21

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Omega E ι : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    [DecidableEq ι]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (D : ι → Set E) (s : Finset ι)
    (hDisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (D i) (D j)) :
    ∀ᵐ omega ∂P, ∀ t : NNReal,
      N omega t (⋃ i ∈ s, D i) = ∑ i ∈ s, N omega t (D i) := by
  filter_upwards [hPPP.2.1] with omega hPath
  intro t
  have hZero : N omega t (∅ : Set E) = 0 := by
    have h := hPath.2.1 t (∅ : Set E) ∅ (by simp)
    simp only [Set.empty_union] at h
    omega
  have hInd : ∀ u : Finset ι,
      (∀ i ∈ u, ∀ j ∈ u, i ≠ j → Disjoint (D i) (D j)) →
      N omega t (⋃ i ∈ u, D i) = ∑ i ∈ u, N omega t (D i) := by
    intro u
    induction u using Finset.induction_on with
    | empty =>
        intro _
        simpa using hZero
    | @insert a u ha ih =>
        intro hu
        have hPair : ∀ i ∈ u, ∀ j ∈ u,
            i ≠ j → Disjoint (D i) (D j) := by
          intro i hi j hj hne
          exact hu i (Finset.mem_insert_of_mem hi)
            j (Finset.mem_insert_of_mem hj) hne
        have hSep : Disjoint (D a) (⋃ i ∈ u, D i) := by
          apply Set.disjoint_left.mpr
          intro x hx hy
          simp only [Set.mem_iUnion] at hy
          obtain ⟨i, hi, hxi⟩ := hy
          have hne : a ≠ i := by
            intro heq
            subst i
            exact ha hi
          exact (Set.disjoint_left.mp
            (hu a (Finset.mem_insert_self a u)
              i (Finset.mem_insert_of_mem hi) hne)) hx hxi
        have hUnion :
            (⋃ i ∈ insert a u, D i) =
              D a ∪ (⋃ i ∈ u, D i) := by
          ext x
          simp [Finset.mem_insert, or_and_right]
        rw [hUnion, hPath.2.1 t (D a) (⋃ i ∈ u, D i) hSep,
            Finset.sum_insert ha, ih hPair]
  exact hInd s hDisj
