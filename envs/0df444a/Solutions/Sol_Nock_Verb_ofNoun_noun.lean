-- Prove2me | solution 1 for Nock.Verb.ofNoun_noun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:41.1118+00:00
-- url     : https://prove2.me/submissions/41042795-805c-4489-a207-487b487a62e8

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
theorem _root_.solution (n : Noun) : (ofNoun n).noun = n := by
  induction n with
  | atom k => rfl
  | cell l r ihl ihr => simp only [ofNoun, noun, ihl, ihr]
end Nock.Verb
