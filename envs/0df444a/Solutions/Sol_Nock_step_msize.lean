-- Prove2me | solution 1 for Nock.step_msize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:28:11.455316+00:00
-- url     : https://prove2.me/submissions/8106e85d-0698-4ff6-a62a-3a6fa67cf700

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
public import Theorems.Thm_Nock_msize_erase
attribute [local simp] Nock.msize_zero
attribute [local simp] Nock.msize_cons

set_option autoImplicit true
@[expose] public section
public section
open Nock
namespace Nock
theorem _root_.solution {m m' : Multiset Noun} {n : Noun} {ch : Option (Noun × Noun)}
    (h : stepMset m n ch = some m') : msize m = msize m' + 1 := by
  cases n with
  | atom k =>
      cases ch with
      | none =>
          simp only [stepMset] at h
          split at h
          · rename_i hmem
            simp only [Option.some.injEq] at h
            subst h
            rw [msize_erase hmem]; simp only [Noun.size]; omega
          · simp at h
      | some c => simp only [stepMset] at h; simp at h
  | cell a b =>
      cases ch with
      | none => simp only [stepMset] at h; simp at h
      | some c =>
          obtain ⟨a', b'⟩ := c
          simp only [stepMset] at h
          split at h
          · rename_i hcond
            obtain ⟨hmem, -, -⟩ := hcond
            simp only [Option.some.injEq] at h
            subst h
            rw [msize_erase hmem]
            simp only [msize_cons, Noun.size]
            omega
          · simp at h
end Nock
