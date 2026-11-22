-- Prove2me | solution 1 for Nock.Verb.editOk_ofNoun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:42.334034+00:00
-- url     : https://prove2.me/submissions/d2a8ac86-0278-4665-a31e-e761fbcca55a

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution (n : Noun) : editOk (ofNoun n) = true := by
  induction n with
  | atom k => rfl
  | cell l r ihl ihr => simp [ofNoun, editOk, ihl, ihr]
end Nock.Verb
