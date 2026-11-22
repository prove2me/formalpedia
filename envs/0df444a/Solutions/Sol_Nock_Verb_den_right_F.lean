-- Prove2me | solution 1 for Nock.Verb.den_right_F
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:25:28.602009+00:00
-- url     : https://prove2.me/submissions/253e5251-6bcc-4450-9bfb-b641fd15acb5

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Theorems.Thm_Nock_Verb_den_succ
public import Theorems.Thm_Nock_Verb_editOk_edit_cond


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {a : Action} {l r : Verb} {f : Nat} {x : Noun}
    (hok : editOk (Verb.node a l r) = true) (h : den (f + 1) (Verb.node a l r) = some x) :
    ∃ yr, den (f + 1) r = some yr := by
  cases a with
  | wut => simp [den] at h
  | edit =>
      have hrp : Verb.isPending r = false := editOk_edit_cond hok
      cases r with
      | leaf k => simp [den] at h
      | node rb nw od =>
          have hrb : rb = Action.null := by
            simp only [isPending] at hrp
            cases rb <;> simp_all [Action.isNull]
          subst hrb
          simp only [den] at h
          cases hnw : den f nw with
          | none => rw [hnw] at h; simp at h
          | some n =>
              cases hod : den f od with
              | none => rw [hnw, hod] at h; simp at h
              | some o => exact ⟨.cell n o, by simp [den, hnw, hod]⟩
  | null =>
      cases hr : den f r with
      | some y => exact ⟨y, den_succ hr⟩
      | none => simp [den, hr] at h
  | star =>
      cases hr : den f r with
      | some y => exact ⟨y, den_succ hr⟩
      | none => simp [den, hr] at h
  | slot =>
      cases hr : den f r with
      | some y => exact ⟨y, den_succ hr⟩
      | none => simp [den, hr] at h
  | equal =>
      cases hr : den f r with
      | some y => exact ⟨y, den_succ hr⟩
      | none => simp [den, hr] at h
  | minus =>
      cases hr : den f r with
      | some y => exact ⟨y, den_succ hr⟩
      | none => simp [den, hr] at h
end Nock.Verb
