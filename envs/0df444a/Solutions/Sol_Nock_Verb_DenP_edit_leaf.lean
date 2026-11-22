-- Prove2me | solution 1 for Nock.Verb.DenP_edit_leaf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:12.04934+00:00
-- url     : https://prove2.me/submissions/42e810b2-d31b-4a47-b38d-14f747b940dc

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
theorem _root_.solution {l k x} : ¬ DenP (.node .edit l (.leaf k)) x := by
  rintro ⟨fuel, h⟩
  cases fuel with
  | zero => simp [denP] at h
  | succ f => simp [denP] at h
end Nock.Verb
