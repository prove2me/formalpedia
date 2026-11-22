-- Prove2me | solution 1 for Nock.checkValidNoun_accept_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:27:43.228431+00:00
-- url     : https://prove2.me/submissions/f629f07f-2295-47d7-9697-2b69b05fefc2

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Ring.Nat
public import Definitions.Def_LeanPool_PureNock_NounValidation

set_option autoImplicit true
@[expose] public section
public section
open Nock
namespace Nock
theorem _root_.solution (n₀ : Noun) (T : Transcript) :
    checkValidNoun n₀ T = Result.accept ↔ runMset {n₀} T = some 0 := by
  unfold checkValidNoun
  cases hr : runMset {n₀} T with
  | none => simp
  | some m =>
      by_cases hz : m = 0
      · subst hz; simp
      · simp [hz]
end Nock
