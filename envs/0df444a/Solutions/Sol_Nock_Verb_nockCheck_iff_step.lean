-- Prove2me | solution 1 for Nock.Verb.nockCheck_iff_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:31:32.320624+00:00
-- url     : https://prove2.me/submissions/4a2fb4d1-9356-4819-98e9-1ab2b02d1b74

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
public import Theorems.Thm_Nock_Verb_nockCheck_eq_true_iff


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {a : Verb} {b : Option Verb} :
    NockCheck a b = true ↔ (∃ v, b = some v ∧ Step a v) ∨ (b = none ∧ Crashes a) :=
  nockCheck_eq_true_iff
end Nock.Verb
