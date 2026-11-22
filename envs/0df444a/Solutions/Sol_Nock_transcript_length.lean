-- Prove2me | solution 1 for Nock.transcript_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:42.562508+00:00
-- url     : https://prove2.me/submissions/864e4dc9-90ff-4db1-ad67-d530cf970ea1

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
theorem _root_.solution (n : Noun) : (transcript n).length = n.size := by
  induction n with
  | atom k => rfl
  | cell l r ihl ihr =>
      simp only [transcript, List.length_cons, List.length_append, ihl, ihr, Noun.size]
      omega
end Nock
