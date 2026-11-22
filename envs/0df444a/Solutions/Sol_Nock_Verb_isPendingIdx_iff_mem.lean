-- Prove2me | solution 1 for Nock.Verb.isPendingIdx_iff_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:33.448328+00:00
-- url     : https://prove2.me/submissions/5d504db1-6845-4b22-b774-bc64400de7cd

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
public import Theorems.Thm_Nock_Verb_map_of_mem_nodes
public import Theorems.Thm_Nock_Verb_mem_nodes_of_map

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {a : Verb} {i : Nat} :
    IsPendingIdx a i ↔ ∃ v, (i, v) ∈ nodes a ∧ v.isPending = true := by
  constructor
  · rintro ⟨v, hmap, hp⟩; exact ⟨v, mem_nodes_of_map hmap, hp⟩
  · rintro ⟨v, hmem, hp⟩; exact ⟨v, map_of_mem_nodes hmem, hp⟩
end Nock.Verb
