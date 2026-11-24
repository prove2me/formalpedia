-- Prove2me | solution 1 for KernelRamsey.card_split
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:29:05.151718+00:00
-- url     : https://prove2.me/submissions/0f40ae99-fe6d-4e36-a5ff-55024a16608e

import Mathlib
open Finset

theorem solution {V : Type} (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] (A : Finset V) {v : V} (hv : v ∈ A) :
    A.card = 1 + (A.filter (fun w => G.Adj v w)).card +
      (A.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)).card := by
  have hsplit : A = insert v ((A.filter (fun w => G.Adj v w)) ∪ (A.filter (fun w => w ≠ v ∧ ¬ G.Adj v w))) := by
    ext w
    simp only [mem_insert, mem_union, mem_filter]
    constructor
    · intro hw
      by_cases hwv : w = v
      · exact Or.inl hwv
      · by_cases ha : G.Adj v w
        · exact Or.inr (Or.inl ⟨hw, ha⟩)
        · exact Or.inr (Or.inr ⟨hw, hwv, ha⟩)
    · rintro (rfl | ⟨hw, _⟩ | ⟨hw, _⟩) <;> assumption
  have hdisj : Disjoint (A.filter (fun w => G.Adj v w)) (A.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)) := by
    rw [Finset.disjoint_left]
    intro w hwN hwM
    exact (Finset.mem_filter.mp hwM).2.2 (Finset.mem_filter.mp hwN).2
  have hvn : v ∉ (A.filter (fun w => G.Adj v w)) ∪ (A.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)) := by
    simp only [mem_union, mem_filter]
    rintro (⟨_, h1⟩ | ⟨_, h1, _⟩)
    · exact G.loopless.irrefl _ h1
    · exact h1 rfl
  have := congrArg Finset.card hsplit
  rw [Finset.card_insert_of_notMem hvn, Finset.card_union_of_disjoint hdisj] at this
  omega
