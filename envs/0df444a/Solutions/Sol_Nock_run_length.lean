-- Prove2me | solution 1 for Nock.run_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:28:36.520841+00:00
-- url     : https://prove2.me/submissions/6a198556-3729-4483-905d-191496237dcb

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
public import Theorems.Thm_Nock_step_msize
attribute [local simp] Nock.msize_zero
attribute [local simp] Nock.msize_cons

set_option autoImplicit true
@[expose] public section
public section
open Nock
namespace Nock
theorem _root_.solution : ∀ {m : Multiset Noun} {T : Transcript},
    runMset m T = some 0 → T.length = msize m := by
  intro m T
  induction T generalizing m with
  | nil =>
      intro h
      simp only [runMset, Option.some.injEq] at h
      subst h; simp
  | cons t ts ih =>
      intro h
      obtain ⟨n, ch⟩ := t
      simp only [runMset] at h
      cases hstep : stepMset m n ch with
      | none => rw [hstep] at h; simp at h
      | some m' =>
          rw [hstep] at h
          have hlen := ih h
          have hms := step_msize hstep
          simp only [List.length_cons]
          omega
end Nock
