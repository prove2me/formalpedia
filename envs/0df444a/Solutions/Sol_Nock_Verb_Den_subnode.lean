-- Prove2me | solution 1 for Nock.Verb.Den_subnode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:26:37.463965+00:00
-- url     : https://prove2.me/submissions/8929c4fd-ae31-4365-a75f-d7ed02102594

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Theorems.Thm_Nock_Verb_enum_den_defined
public import Theorems.Thm_Nock_Verb_mem_nodes_of_map


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {v : Verb} {x : Noun} (hok : editOk v = true) (hv : Den v x)
    {i : Nat} {sub : Verb} (hmap : map i v = some sub) : ∃ y, Den sub y := by
  obtain ⟨f, hf⟩ := hv
  have hmem : (i, sub) ∈ nodes v := mem_nodes_of_map hmap
  obtain ⟨g, y, hg⟩ := enum_den_defined v hok 0 f x hf (i, sub) hmem
  exact ⟨y, g, hg⟩
end Nock.Verb
