-- Prove2me | solution 1 for Nock.Verb.vcostN_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:05:56.647873+00:00
-- url     : https://prove2.me/submissions/f6961d1a-df1a-482b-b7e8-0d069df7f858

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
theorem _root_.solution : ∀ (v : Verb), isTerminal v = true → ∀ F, vcostN F v = 0 := by
  intro v
  induction v with
  | leaf k => intro _ F; rfl
  | node a l r ihl ihr =>
      intro hterm F
      simp only [isTerminal, Bool.and_eq_true] at hterm
      obtain ⟨⟨hnull, hl⟩, hr⟩ := hterm
      have ha : a = Action.null := by cases a <;> simp_all [Action.isNull]
      subst ha
      simp only [vcostN]; rw [ihl hl F, ihr hr F]
end Nock.Verb
