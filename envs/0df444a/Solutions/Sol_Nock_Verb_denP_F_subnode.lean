-- Prove2me | solution 1 for Nock.Verb.denP_F_subnode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:25:08.195105+00:00
-- url     : https://prove2.me/submissions/bbec9de6-09ba-4f3b-869b-0f4e0700011f

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Theorems.Thm_Nock_Verb_enum_denP_F
public import Theorems.Thm_Nock_Verb_mem_nodes_of_map


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {F : Nat} {v : Verb} {x : Noun} (hok : editOk v = true)
    (hv : denP F v = some x) {i : Nat} {sub : Verb} (hmap : map i v = some sub) :
    ∃ y, denP F sub = some y :=
  enum_denP_F v hok 0 x hv (i, sub) (mem_nodes_of_map hmap)
end Nock.Verb
