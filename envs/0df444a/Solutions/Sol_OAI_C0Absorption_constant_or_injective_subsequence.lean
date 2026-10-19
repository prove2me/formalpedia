-- Prove2me | solution 1 for OAI.C0Absorption.constant_or_injective_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:24:22.414141+00:00
-- url     : https://prove2.me/submissions/8e8b9682-35cf-451e-957a-90f28d2b1247

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality
import Definitions.Def_OAI_Analysis_C0Absorption_Selection

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology


theorem solution {A : Type*} (f : ℕ → A) :
    (∃ a, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, f (φ i)=a) ∨
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ Function.Injective (f ∘ φ)) := by
  classical
  by_cases h : ∃ a, {n | f n = a}.Infinite
  · obtain ⟨a, ha⟩ := h
    exact Or.inl ⟨a, Nat.nth (fun n => f n = a), Nat.nth_strictMono ha,
      fun i => Nat.nth_mem_of_infinite ha i⟩
  · push_neg at h
    right
    let S : Set ℕ := {n | ∀ m < n, f m ≠ f n}
    have hS : S.Infinite := by
      intro hS
      have hcov : (Set.univ : Set ℕ) ⊆ ⋃ a ∈ f '' S, {n | f n = a} := by
        intro n _
        have hex : ∃ m, f m = f n := ⟨n, rfl⟩
        let m := Nat.find hex
        have hm : f m = f n := Nat.find_spec hex
        have hmS : m ∈ S := by
          intro k hk hfk
          exact Nat.find_min hex hk (hfk.trans hm)
        simp only [Set.mem_iUnion, Set.mem_setOf_eq]
        exact ⟨f m, ⟨m, hmS, rfl⟩, hm.symm⟩
      have hfin : (⋃ a ∈ f '' S, {n | f n = a}).Finite :=
        (hS.image f).biUnion (fun a _ => h a)
      exact Set.infinite_univ (hfin.subset hcov)
    refine ⟨Nat.nth (· ∈ S), Nat.nth_strictMono hS, ?_⟩
    intro i j hij
    by_contra hne
    have hmem : ∀ k, Nat.nth (· ∈ S) k ∈ S := fun k => Nat.nth_mem_of_infinite hS k
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hmem j _ (Nat.nth_strictMono hS hlt) hij
    · exact hmem i _ (Nat.nth_strictMono hS hlt) hij.symm

