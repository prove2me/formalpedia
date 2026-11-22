-- Prove2me | solution 1 for Nock.run_transcript_accept
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:28:32.282056+00:00
-- url     : https://prove2.me/submissions/cd94ef40-f4d4-42c0-9682-e9c93470cdb8

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Ring.Nat
public import Definitions.Def_LeanPool_PureNock_NounValidation
public import Theorems.Thm_Nock_run_transcript

set_option autoImplicit true
@[expose] public section
public section
open Nock
namespace Nock
theorem _root_.solution (n : Noun) : runMset {n} (transcript n) = some 0 := by
  have h := run_transcript n 0 []
  rw [List.append_nil] at h
  rw [show ({n} : Multiset Noun) = n ::ₘ 0 from rfl, h]
  rfl
end Nock
