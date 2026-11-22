-- Prove2me | solution 1 for Nock.Verb.vcostN_equal_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:03.61604+00:00
-- url     : https://prove2.me/submissions/f9022cc6-1637-4733-bfdb-cd688ad83adc

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {F : Nat} {l r : Verb} :
    vcostN F (Verb.node .equal l r) = 1 + vcostN F l + vcostN F r := rfl
end Nock.Verb
