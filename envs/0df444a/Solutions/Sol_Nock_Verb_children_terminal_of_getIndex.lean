-- Prove2me | solution 1 for Nock.Verb.children_terminal_of_getIndex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:25.186611+00:00
-- url     : https://prove2.me/submissions/7522f614-0cac-4f13-b803-9ca2ae6be2c7

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
public import Theorems.Thm_Nock_Verb_enum_ge_start
public import Theorems.Thm_Nock_Verb_enum_index_range
public import Theorems.Thm_Nock_Verb_mem_nodes_of_map
public import Theorems.Thm_Nock_Verb_isPendingIdx_iff_mem
public import Theorems.Thm_Nock_Verb_getIndex_eq_some_iff
public import Theorems.Thm_Nock_Verb_terminal_of_enum_nonpending
public import Theorems.Thm_Nock_Verb_enum_subtree_mem

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {v : Verb} {i : Nat} {a : Action} {l r : Verb}
    (hidx : getIndex v = some i) (hmap : map i v = some (Verb.node a l r)) :
    isTerminal l = true ∧ isTerminal r = true := by
  have hmax : IsMaxPending dfsLt v i := getIndex_eq_some_iff.1 hidx
  have hmem : (i, Verb.node a l r) ∈ nodes v := mem_nodes_of_map hmap
  have hsub : ∀ p ∈ (enum (Verb.node a l r) i).2, p ∈ nodes v := by
    intro p hp; exact enum_subtree_mem v 0 i (Verb.node a l r) hmem p hp
  have hnopend : ∀ p ∈ (enum (Verb.node a l r) i).2, i < p.1 → p.2.isPending = false := by
    intro p hp hlt
    obtain ⟨j, w⟩ := p
    simp only at hlt ⊢
    cases hw : w.isPending with
    | false => rfl
    | true =>
        have hpid : IsPendingIdx v j := isPendingIdx_iff_mem.2 ⟨w, hsub (j, w) hp, hw⟩
        exact absurd hlt (hmax.2 j hpid)
  refine ⟨?_, ?_⟩
  · apply terminal_of_enum_nonpending l (i + 1)
    intro p hp
    apply hnopend p
    · simp only [enum, List.mem_cons, List.mem_append]; exact Or.inr (Or.inl hp)
    · have := enum_index_range l (i + 1) p hp; omega
  · apply terminal_of_enum_nonpending r (enum l (i + 1)).1
    intro p hp
    apply hnopend p
    · simp only [enum, List.mem_cons, List.mem_append]; exact Or.inr (Or.inr hp)
    · have hge : i + 1 ≤ (enum l (i + 1)).1 := enum_ge_start l (i + 1)
      have := enum_index_range r (enum l (i + 1)).1 p hp; omega
end Nock.Verb
