-- Prove2me | solution 1 for Nock.Verb.den_localP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:24:13.66599+00:00
-- url     : https://prove2.me/submissions/d37bc97f-6731-4563-9852-9b7010a5afe8

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_den_localP_opReady
public import Theorems.Thm_Nock_Verb_den_localP_opcode

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {sub r₀ x} (hd : inDomain sub = true) (hr : reduce sub = some r₀) :
    (DenP sub x ↔ DenP r₀ x) := by
  rw [inDomain, Bool.or_eq_true] at hd
  rcases hd with h | h
  · exact den_localP_opcode h hr
  · exact den_localP_opReady h hr
end Nock.Verb
