-- Prove2me | solution 1 for Nock.Verb.getIndex_none_iff_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:53.336278+00:00
-- url     : https://prove2.me/submissions/f2b537ff-e648-40c0-b650-3d59dcc269e2

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
public import Theorems.Thm_Nock_Verb_getIndex_none_of_terminal
public import Theorems.Thm_Nock_Verb_terminal_of_enum_nonpending
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
theorem _root_.solution {v : Verb} : getIndex v = none ↔ isTerminal v = true := by
  constructor
  · intro h
    apply terminal_of_enum_nonpending v 0
    unfold getIndex nodes at h
    exact maximumPendingIndex_eq_none.1 h
  · exact getIndex_none_of_terminal
end Nock.Verb
