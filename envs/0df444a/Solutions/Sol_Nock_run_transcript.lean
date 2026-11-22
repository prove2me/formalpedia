-- Prove2me | solution 1 for Nock.run_transcript
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:28:07.057796+00:00
-- url     : https://prove2.me/submissions/40f73902-bf9a-48a4-b4e6-17d87abf1c10

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Ring.Nat
public import Definitions.Def_LeanPool_PureNock_NounValidation
public import Theorems.Thm_Nock_runMset_cons
public import Theorems.Thm_Nock_msize_zero
public import Theorems.Thm_Nock_msize_cons
public import Theorems.Thm_Nock_transcript_length
attribute [local simp] Nock.msize_zero
attribute [local simp] Nock.msize_cons
attribute [local simp] Nock.transcript_length

set_option autoImplicit true
@[expose] public section
public section
open Nock
namespace Nock
theorem _root_.solution : ∀ (n : Noun) (m : Multiset Noun) (rest : Transcript),
    runMset (n ::ₘ m) (transcript n ++ rest) = runMset m rest := by
  intro n
  induction n with
  | atom k =>
      intro m rest
      rw [show transcript (Noun.atom k) ++ rest = (Noun.atom k, none) :: rest from rfl]
      have hstep : stepMset (Noun.atom k ::ₘ m) (Noun.atom k) none = some m := by
        simp [stepMset, Multiset.erase_cons_head]
      rw [runMset_cons hstep]
  | cell l r ihl ihr =>
      intro m rest
      rw [show transcript (Noun.cell l r) ++ rest
          = (Noun.cell l r, some (l, r)) :: (transcript l ++ transcript r ++ rest) from rfl]
      have hstep : stepMset (Noun.cell l r ::ₘ m) (Noun.cell l r) (some (l, r))
          = some (l ::ₘ r ::ₘ m) := by
        simp [stepMset, Multiset.erase_cons_head]
      rw [runMset_cons hstep, List.append_assoc,
        ihl (r ::ₘ m) (transcript r ++ rest), ihr m rest]
end Nock
