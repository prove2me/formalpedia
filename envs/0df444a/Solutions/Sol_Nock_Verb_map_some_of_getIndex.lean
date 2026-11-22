-- Prove2me | solution 1 for Nock.Verb.map_some_of_getIndex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:28.583467+00:00
-- url     : https://prove2.me/submissions/1e169fcc-421f-484a-9a5e-f56da5c9b40f

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
public import Theorems.Thm_Nock_Verb_getIndex_eq_some_iff

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {a : Verb} {i : Nat} (h : getIndex a = some i) :
    ∃ sub, map i a = some sub := by
  obtain ⟨⟨v, hmap, _⟩, _⟩ := getIndex_eq_some_iff.1 h
  exact ⟨v, hmap⟩
end Nock.Verb
