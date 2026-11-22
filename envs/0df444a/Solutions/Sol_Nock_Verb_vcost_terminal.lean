-- Prove2me | solution 1 for Nock.Verb.vcost_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:05:03.636407+00:00
-- url     : https://prove2.me/submissions/773a9c34-8d3e-40d8-bb22-4a01a5602e6c

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
theorem _root_.solution : ∀ (v : Verb), isTerminal v = true → ∀ F, vcost F v = 0 := by
  intro v
  induction v with
  | leaf k => intro _ F; rfl
  | node a l r ihl ihr =>
      intro hterm F
      simp only [isTerminal, Bool.and_eq_true] at hterm
      obtain ⟨⟨hnull, hl⟩, hr⟩ := hterm
      have ha : a = Action.null := by cases a <;> simp_all only [Action.isNull, reduceCtorEq]
      subst ha
      simp only [vcost]; rw [ihl hl F, ihr hr F]
end Nock.Verb
