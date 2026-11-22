-- Prove2me | solution 1 for Nock.Verb.den_F_subnode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:27:09.562817+00:00
-- url     : https://prove2.me/submissions/e633da3f-b348-4d5d-9c89-7ab06c2897e0

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Theorems.Thm_Nock_Verb_enum_den_F
public import Theorems.Thm_Nock_Verb_mem_nodes_of_map


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {F : Nat} {v : Verb} {x : Noun} (hok : editOk v = true)
    (hv : den F v = some x) {i : Nat} {sub : Verb} (hmap : map i v = some sub) :
    ∃ y, den F sub = some y :=
  enum_den_F v hok 0 x hv (i, sub) (mem_nodes_of_map hmap)
end Nock.Verb
