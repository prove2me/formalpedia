-- Prove2me | solution 1 for Nock.Verb.DenP_wut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:17.12907+00:00
-- url     : https://prove2.me/submissions/a1e2e831-df1c-493f-8345-0d901e80d3b6

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {l r x} : ¬ DenP (.node .wut l r) x := by
  rintro ⟨fuel, h⟩
  cases fuel with
  | zero => simp [denP] at h
  | succ f => simp [denP] at h
end Nock.Verb
