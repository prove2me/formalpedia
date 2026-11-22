-- Prove2me | solution 1 for Nock.msize_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:27:46.103339+00:00
-- url     : https://prove2.me/submissions/58281425-f4d2-4eb0-97ba-6c1cf1cc7b56

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Ring.Nat
public import Definitions.Def_LeanPool_PureNock_NounValidation
public import Theorems.Thm_Nock_msize_zero
public import Theorems.Thm_Nock_msize_cons
attribute [local simp] Nock.msize_zero
attribute [local simp] Nock.msize_cons

set_option autoImplicit true
@[expose] public section
public section
open Nock
namespace Nock
theorem _root_.solution (a : Noun) : msize ({a} : Multiset Noun) = a.size := by
  simp [msize]
end Nock
