-- Prove2me | solution 1 for Nock.Verb.denP_null_leaf0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:24:20.117403+00:00
-- url     : https://prove2.me/submissions/4642cd6c-f25d-43f2-bc0e-16d90f335231

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {inner : Verb} {f : Nat} {dv : Noun}
    (h : denP (f + 1) (Verb.node .null (Verb.leaf 0) inner) = some dv) :
    ∃ w, dv = Noun.cell (Noun.atom 0) w := by
  simp only [denP] at h
  cases hi : denP f inner with
  | none => rw [hi] at h; simp at h
  | some iv => rw [hi] at h; exact ⟨iv, (Option.some.inj h).symm⟩
end Nock.Verb
