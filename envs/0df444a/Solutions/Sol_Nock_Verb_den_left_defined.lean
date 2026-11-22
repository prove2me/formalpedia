-- Prove2me | solution 1 for Nock.Verb.den_left_defined
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:25.557851+00:00
-- url     : https://prove2.me/submissions/f3c2547e-ed9d-44c1-b3c9-cd8a0589ad29

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
theorem _root_.solution {a : Action} {l r : Verb} {f : Nat} {x : Noun}
    (h : den (f + 1) (Verb.node a l r) = some x) : ∃ y, den f l = some y := by
  cases hl : den f l with
  | some y => exact ⟨y, rfl⟩
  | none =>
      exfalso
      cases a with
      | edit =>
          cases r with
          | leaf k => simp [den] at h
          | node rb nw od => simp [den, hl] at h
      | wut => simp [den] at h
      | _ => simp [den, hl] at h
end Nock.Verb
