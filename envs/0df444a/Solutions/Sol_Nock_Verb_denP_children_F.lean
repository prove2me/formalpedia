-- Prove2me | solution 1 for Nock.Verb.denP_children_F
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:51.836158+00:00
-- url     : https://prove2.me/submissions/ac239376-7946-41f1-8263-b4b054aa55c4

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Theorems.Thm_Nock_Verb_denP_right_F
public import Theorems.Thm_Nock_Verb_denP_left_defined
public import Theorems.Thm_Nock_Verb_denP_succ


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {a : Action} {l r : Verb} {F : Nat} {x : Noun}
    (hok : editOk (Verb.node a l r) = true) (h : denP F (Verb.node a l r) = some x) :
    (∃ yl, denP F l = some yl) ∧ (∃ yr, denP F r = some yr) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := by
    cases F with
    | zero => simp [denP] at h
    | succ n => exact ⟨n, rfl⟩
  refine ⟨?_, denP_right_F hok h⟩
  obtain ⟨yl, hyl⟩ := denP_left_defined h
  exact ⟨yl, denP_succ hyl⟩
end Nock.Verb
