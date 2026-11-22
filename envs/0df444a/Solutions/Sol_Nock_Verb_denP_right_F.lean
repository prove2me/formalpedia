-- Prove2me | solution 1 for Nock.Verb.denP_right_F
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:15.921856+00:00
-- url     : https://prove2.me/submissions/9ac3986a-dbb1-443d-b1f5-0e151bec75a4

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Theorems.Thm_Nock_Verb_denP_succ
public import Theorems.Thm_Nock_Verb_editOk_edit_cond


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {a : Action} {l r : Verb} {f : Nat} {x : Noun}
    (hok : editOk (Verb.node a l r) = true) (h : denP (f + 1) (Verb.node a l r) = some x) :
    ∃ yr, denP (f + 1) r = some yr := by
  cases a with
  | wut => simp [denP] at h
  | edit =>
      have hrp : Verb.isPending r = false := editOk_edit_cond hok
      cases r with
      | leaf k => simp [denP] at h
      | node rb nw od =>
          have hrb : rb = Action.null := by
            simp only [isPending] at hrp
            cases rb <;> simp_all [Action.isNull]
          subst hrb
          simp only [denP] at h
          cases hnw : denP f nw with
          | none => rw [hnw] at h; simp at h
          | some n =>
              cases hod : denP f od with
              | none => rw [hnw, hod] at h; simp at h
              | some o => exact ⟨.cell n o, by simp [denP, hnw, hod]⟩
  | null => cases hr : denP f r with | some y => exact ⟨y, denP_succ hr⟩ | none => simp [denP, hr]
    at h
  | star => cases hr : denP f r with | some y => exact ⟨y, denP_succ hr⟩ | none => simp [denP, hr]
    at h
  | slot => cases hr : denP f r with | some y => exact ⟨y, denP_succ hr⟩ | none => simp [denP, hr]
    at h
  | equal => cases hr : denP f r with | some y => exact ⟨y, denP_succ hr⟩ | none => simp [denP, hr]
    at h
  | minus => cases hr : denP f r with | some y => exact ⟨y, denP_succ hr⟩ | none => simp [denP, hr]
    at h
end Nock.Verb
