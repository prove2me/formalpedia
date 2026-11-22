-- Prove2me | solution 1 for Nock.Noun_Validation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:29:01.168917+00:00
-- url     : https://prove2.me/submissions/26998702-2486-4c71-a1de-df5886435747

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Ring.Nat
public import Definitions.Def_LeanPool_PureNock_NounValidation
public import Theorems.Thm_Nock_checkValidNoun_accept_iff
public import Theorems.Thm_Nock_msize_singleton
public import Theorems.Thm_Nock_run_length
public import Theorems.Thm_Nock_transcript_length
public import Theorems.Thm_Nock_run_transcript_accept
public import Theorems.Thm_Nock_Noun_one_le_leaves
public import Theorems.Thm_Nock_Noun_size_add_one

attribute [local simp] Nock.transcript_length

set_option autoImplicit true
@[expose] public section
public section
open Nock
namespace Nock
theorem _root_.solution (n : Noun) (lam : ℕ) :
    n.leaves = lam ↔
      ∃ T : Transcript, checkValidNoun n T = Result.accept ∧ T.length = 2 * lam - 1 := by
  constructor
  · intro hlen
    refine ⟨transcript n, ?_, ?_⟩
    · rw [checkValidNoun_accept_iff]; exact run_transcript_accept n
    · rw [transcript_length]
      have := n.size_add_one
      omega
  · rintro ⟨T, hacc, hlenT⟩
    rw [checkValidNoun_accept_iff] at hacc
    have hlenrun := run_length hacc
    rw [msize_singleton] at hlenrun
    have hsz := n.size_add_one
    have hpos := n.one_le_leaves
    omega
end Nock
