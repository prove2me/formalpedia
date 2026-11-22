-- Prove2me | solution 1 for Nock.Verb.ofNoun_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:11.9738+00:00
-- url     : https://prove2.me/submissions/8fbc8435-9d75-457c-a813-3033ec937a78

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
theorem _root_.solution (n : Noun) : isTerminal (ofNoun n) = true := by
  induction n with
  | atom k => rfl
  | cell l r ihl ihr => simp [ofNoun, isTerminal, Action.isNull, ihl, ihr]
end Nock.Verb
