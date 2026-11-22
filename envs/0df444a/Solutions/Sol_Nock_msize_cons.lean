-- Prove2me | solution 1 for Nock.msize_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:03.312355+00:00
-- url     : https://prove2.me/submissions/88bbaa05-cfe5-4cee-aa31-a28a9f1ca437

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Ring.Nat
public import Definitions.Def_LeanPool_PureNock_NounValidation
public import Theorems.Thm_Nock_msize_zero
attribute [local simp] Nock.msize_zero

set_option autoImplicit true
@[expose] public section
public section
open Nock
namespace Nock
theorem _root_.solution (a : Noun) (m : Multiset Noun) :
    msize (a ::ₘ m) = a.size + msize m := by
  simp [msize]
end Nock
