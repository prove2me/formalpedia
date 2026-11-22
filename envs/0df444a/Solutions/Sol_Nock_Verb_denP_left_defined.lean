-- Prove2me | solution 1 for Nock.Verb.denP_left_defined
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:59.691601+00:00
-- url     : https://prove2.me/submissions/e3cae818-a9a9-46ae-bb81-c64ad6d1aa8e

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
theorem _root_.solution {a : Action} {l r : Verb} {f : Nat} {x : Noun}
    (h : denP (f + 1) (Verb.node a l r) = some x) : ∃ y, denP f l = some y := by
  cases hl : denP f l with
  | some y => exact ⟨y, rfl⟩
  | none =>
      exfalso
      cases a with
      | edit =>
          cases r with
          | leaf k => simp [denP] at h
          | node rb nw od => simp [denP, hl] at h
      | wut => simp [denP] at h
      | _ => simp [denP, hl] at h
end Nock.Verb
