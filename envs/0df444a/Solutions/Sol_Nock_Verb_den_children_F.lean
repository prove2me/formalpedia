-- Prove2me | solution 1 for Nock.Verb.den_children_F
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:26:04.167813+00:00
-- url     : https://prove2.me/submissions/488f8403-0195-442a-9af2-535927fe3c4d

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Theorems.Thm_Nock_Verb_den_left_defined
public import Theorems.Thm_Nock_Verb_den_right_F
public import Theorems.Thm_Nock_Verb_den_succ


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {a : Action} {l r : Verb} {F : Nat} {x : Noun}
    (hok : editOk (Verb.node a l r) = true) (h : den F (Verb.node a l r) = some x) :
    (∃ yl, den F l = some yl) ∧ (∃ yr, den F r = some yr) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := by
    cases F with
    | zero => simp [den] at h
    | succ n => exact ⟨n, rfl⟩
  refine ⟨?_, den_right_F hok h⟩
  obtain ⟨yl, hyl⟩ := den_left_defined h
  exact ⟨yl, den_succ hyl⟩
end Nock.Verb
