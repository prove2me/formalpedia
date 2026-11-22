-- Prove2me | solution 1 for Nock.Verb.DenP_subnode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:24:14.077543+00:00
-- url     : https://prove2.me/submissions/6d4180b6-e00c-48b4-b59f-e1b4df8909c1

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_enum_denP_defined
public import Theorems.Thm_Nock_Verb_mem_nodes_of_map


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {v : Verb} {x : Noun} (hok : editOk v = true) (hv : DenP v x)
    {i : Nat} {sub : Verb} (hmap : map i v = some sub) : ∃ y, DenP sub y := by
  obtain ⟨f, hf⟩ := hv
  have hmem : (i, sub) ∈ nodes v := mem_nodes_of_map hmap
  obtain ⟨g, y, hg⟩ := enum_denP_defined v hok 0 f x hf (i, sub) hmem
  exact ⟨y, g, hg⟩
end Nock.Verb
