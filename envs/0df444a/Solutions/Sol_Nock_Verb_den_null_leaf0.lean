-- Prove2me | solution 1 for Nock.Verb.den_null_leaf0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:25:47.44928+00:00
-- url     : https://prove2.me/submissions/71409473-3263-4f53-b005-95c8a1242cac

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
theorem _root_.solution {inner : Verb} {f : Nat} {dv : Noun}
    (h : den (f + 1) (Verb.node .null (Verb.leaf 0) inner) = some dv) :
    ∃ w, dv = Noun.cell (Noun.atom 0) w := by
  simp only [den] at h
  cases hi : den f inner with
  | none => rw [hi] at h; simp at h
  | some iv => rw [hi] at h; exact ⟨iv, (Option.some.inj h).symm⟩
end Nock.Verb
