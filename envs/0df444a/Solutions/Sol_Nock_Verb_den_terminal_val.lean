-- Prove2me | solution 1 for Nock.Verb.den_terminal_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:25.837626+00:00
-- url     : https://prove2.me/submissions/d7674d1f-c269-4fc6-b640-7f507871ab73

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Theorems.Thm_Nock_Verb_Den_terminal_iff


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {v : Verb} {F : Nat} {y : Noun}
    (ht : isTerminal v = true) (h : den F v = some y) : y = v.noun :=
  (Den_terminal_iff ht).1 ⟨F, h⟩
end Nock.Verb
