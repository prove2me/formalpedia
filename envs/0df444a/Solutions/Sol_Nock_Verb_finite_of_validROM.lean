-- Prove2me | solution 1 for Nock.Verb.finite_of_validROM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:31:28.224748+00:00
-- url     : https://prove2.me/submissions/dd2ddec9-aafd-4173-ac8e-08242416737f

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
public import Theorems.Thm_Nock_Verb_traceOf_of_traceOfROM
public import Theorems.Thm_Nock_Verb_next_none_of_terminal


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {F : Verb} (h : ValidROM F) : Finite F := by
  obtain ⟨T, v, hT, hl, _, hterm⟩ := h
  exact ⟨T, traceOf_of_traceOfROM hT, v, hl, next_none_of_terminal hterm⟩
end Nock.Verb
