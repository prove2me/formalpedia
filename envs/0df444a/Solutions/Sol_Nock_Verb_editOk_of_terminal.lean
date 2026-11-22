-- Prove2me | solution 1 for Nock.Verb.editOk_of_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:55.309803+00:00
-- url     : https://prove2.me/submissions/d529b5b8-32b0-4e60-aa62-d15b56d7908d

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_editOk_null_eq


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution : ∀ {v : Verb}, isTerminal v = true → editOk v = true := by
  intro v
  induction v with
  | leaf => intro _; rfl
  | node a l r ihl ihr =>
      intro h
      simp only [isTerminal, Bool.and_eq_true] at h
      obtain ⟨⟨ha, hl⟩, hr⟩ := h
      have haN : a = Action.null := by cases a <;> simp_all only [Action.isNull, reduceCtorEq]
      subst haN
      simp [editOk_null_eq, ihl hl, ihr hr]
end Nock.Verb
