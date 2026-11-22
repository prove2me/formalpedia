-- Prove2me | solution 1 for Nock.msize_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:27:46.629797+00:00
-- url     : https://prove2.me/submissions/f7c3b935-74da-477c-9d09-a5b0c0c0f6e4

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Ring.Nat
public import Definitions.Def_LeanPool_PureNock_NounValidation
public import Theorems.Thm_Nock_msize_cons
attribute [local simp] Nock.msize_cons

set_option autoImplicit true
@[expose] public section
public section
open Nock
namespace Nock
theorem _root_.solution {n : Noun} {m : Multiset Noun} (h : n ∈ m) :
    msize m = n.size + msize (m.erase n) := by
  conv_lhs => rw [← Multiset.cons_erase h]
  rw [msize_cons]
end Nock
