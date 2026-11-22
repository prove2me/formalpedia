-- Prove2me | solution 1 for Nock.FieldEmbedding.slot_boundedBy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:20.951811+00:00
-- url     : https://prove2.me/submissions/7dbd3ce8-42b2-47aa-8184-311e53acf0d7

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Mathlib.Data.ZMod.Basic
public import Definitions.Def_LeanPool_PureNock_ModularEval
public import Theorems.Thm_Nock_FieldEmbedding_BoundedBy_atom
public import Theorems.Thm_Nock_FieldEmbedding_BoundedBy_cell
attribute [local simp] Nock.FieldEmbedding.BoundedBy_atom
attribute [local simp] Nock.FieldEmbedding.BoundedBy_cell

set_option autoImplicit true
@[expose] public section
public section
open Nock Nock.FieldEmbedding
open Nock Nock.Noun
namespace Nock.FieldEmbedding
theorem _root_.solution (q : ℕ) (ax : Nat) (n : Noun) :
    BoundedBy q n → ∀ {m : Noun}, slot ax n = some m → BoundedBy q m := by
  induction ax, n using Nock.Noun.slot.induct with
  | case1 x => intro _ m h; simp [slot] at h
  | case2 n => intro hn m h; simp only [slot] at h; obtain rfl := Option.some.inj h; exact hn
  | case3 a n l r hrec ih =>
      intro hn m h
      have hlr : BoundedBy q (Noun.cell l r) := ih hn hrec
      simp only [slot, hrec] at h
      split at h
      · obtain rfl := Option.some.inj h; exact hlr.1
      · obtain rfl := Option.some.inj h; exact hlr.2
  | case4 a n hno ih =>
      intro hn m h
      simp only [slot] at h
      cases hs : slot ((a + 2) / 2) n with
      | none => simp at h
      | some w =>
        cases w with
        | atom k => simp at h
        | cell l r => exact (hno l r hs).elim
end Nock.FieldEmbedding
