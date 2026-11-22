-- Prove2me | solution 1 for Nock.msize_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:37.780281+00:00
-- url     : https://prove2.me/submissions/82842f4c-0ef0-4193-b91d-762eb01d2f82

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
theorem _root_.solution : msize (0 : Multiset Noun) = 0 := by simp [msize]
end Nock
