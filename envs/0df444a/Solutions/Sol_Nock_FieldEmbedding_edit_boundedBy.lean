-- Prove2me | solution 1 for Nock.FieldEmbedding.edit_boundedBy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:48.284457+00:00
-- url     : https://prove2.me/submissions/cf527db4-8ba4-4dad-b045-bdfdb9ead9e2

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Mathlib.Data.ZMod.Basic
public import Definitions.Def_LeanPool_PureNock_ModularEval
public import Theorems.Thm_Nock_FieldEmbedding_BoundedBy_atom
public import Theorems.Thm_Nock_FieldEmbedding_BoundedBy_cell
public import Theorems.Thm_Nock_FieldEmbedding_slot_boundedBy
attribute [local simp] Nock.FieldEmbedding.BoundedBy_atom
attribute [local simp] Nock.FieldEmbedding.BoundedBy_cell

set_option autoImplicit true
@[expose] public section
public section
open Nock Nock.FieldEmbedding
open Nock Nock.Noun
namespace Nock.FieldEmbedding
theorem _root_.solution (q : ℕ) (ax : Nat) (new old : Noun) :
    BoundedBy q new → BoundedBy q old →
      ∀ {m : Noun}, edit ax new old = some m → BoundedBy q m := by
  induction ax, new, old using Nock.Noun.edit.induct with
  | case1 x y => intro _ _ m h; simp [edit] at h
  | case2 new x => intro hnew _ m h; simp only [edit] at h; obtain rfl := Option.some.inj h; exact
    hnew
  | case3 a new old sibAxis sib hsib paired ih =>
      intro hnew hold m h
      have hsibB : BoundedBy q sib := slot_boundedBy q _ _ hold hsib
      have hpair : ∀ b : Bool, BoundedBy q
          (if b = true then new.cell sib else sib.cell new) := by
        intro b; cases b <;> exact ⟨by assumption, by assumption⟩
      simp only [edit] at h
      rw [show slot (if ((a + 2) % 2 == 0) = true then a + 2 + 1 else a + 2 - 1) old = some sib
            from hsib] at h
      exact ih (hpair _) hold h
  | case4 a new old sibAxis hnone =>
      intro _ _ m h
      simp only [edit] at h
      rw [show slot (if ((a + 2) % 2 == 0) = true then a + 2 + 1 else a + 2 - 1) old = none
            from hnone] at h
      simp at h
end Nock.FieldEmbedding
