-- Prove2me | solution 1 for Nock.Verb.getIndex_none_of_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:27.799994+00:00
-- url     : https://prove2.me/submissions/627c8a36-beac-4207-a7b9-55c3c1b99608

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
public import Theorems.Thm_Nock_Verb_enum_nonpending_of_terminal
section
@[expose] public section
namespace Nock
namespace Verb
private theorem maximumPendingIndex_eq_none :
    ∀ {L : List (Nat × Verb)},
      maximumPendingIndex L = none ↔ ∀ p ∈ L, p.2.isPending = false
  | [] => by simp [maximumPendingIndex]
  | (i, w) :: t => by
      simp only [maximumPendingIndex]
      by_cases hw : w.isPending = true
      · rw [if_pos hw]
        constructor
        · intro h; cases maximumPendingIndex t <;> simp at h
        · intro h; exact absurd (h (i, w) (by simp)) (by simp [hw])
      · rw [if_neg hw]
        rw [maximumPendingIndex_eq_none]
        constructor
        · intro h p hp
          rcases List.mem_cons.1 hp with heq | hmem
          · subst heq; simpa using hw
          · exact h p hmem
        · intro h p hp; exact h p (List.mem_cons_of_mem _ hp)
end Verb
end Nock
end
end

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {v : Verb} (h : isTerminal v = true) : getIndex v = none := by
  unfold getIndex nodes
  rw [maximumPendingIndex_eq_none]
  exact enum_nonpending_of_terminal v h 0
end Nock.Verb
