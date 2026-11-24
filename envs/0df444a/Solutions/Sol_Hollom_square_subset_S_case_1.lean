-- Prove2me | solution 1 for Hollom.square_subset_S_case_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:20:47.577299+00:00
-- url     : https://prove2.me/submissions/62a04ba1-24ef-4fbf-949d-c0830ccc012c

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.CompleteLattice
import Mathlib.Order.Interval.Set.Infinite
import Definitions.Def_AharoniKorman_ForMathlib_Misc
import Definitions.Def_AharoniKorman_Counterexample
import Theorems.Thm_Hollom_toHollom_le_toHollom
import Theorems.Thm_Hollom_SpinalMap_ext
import Theorems.Thm_Hollom_SpinalMap_toFun_eq_coe
import Theorems.Thm_Hollom_SpinalMap_mem
import Theorems.Thm_Hollom_SpinalMap_idempotent
import Theorems.Thm_Hollom_square_subset_R
attribute [local ext] Hollom.SpinalMap.ext
attribute [local simp] Hollom.SpinalMap.toFun_eq_coe
attribute [local simp] Hollom.SpinalMap.mem
attribute [local simp] Hollom.SpinalMap.idempotent

set_option autoImplicit true
attribute [local aesop 2 simp] Set.subset_def Finset.subset_iff
open Hollom
local notation3 "h(" x ", " y ", " z ")" => toHollom (x, y, z)
variable {C : Set Hollom}
open Filter
variable {f : SpinalMap C}
variable {n : ℕ}
namespace Hollom
theorem _root_.solution (h : (C ∩ level n).Finite) (h' : (C ∩ level (n + 1)).Finite) :
    ∀ᶠ a in atTop, embed n '' Set.Ici (a, a) ⊆ S n C \ (C ∩ level n) := by
  rw [S, if_pos h']

  -- Take a maximal pair `(b, c)` so that any `(d, e, n)` in `C` satisfies
  -- `(d, e, n) ≤ (b, c, n)`.
  obtain ⟨b, c, hab⟩ : ∃ b c, ∀ d e, h(d, e, n + 1) ∈ C → (d, e) ≤ (b, c) := by
    obtain ⟨⟨b, c⟩, hbc⟩ := (h'.image (fun t ↦ ((ofHollom t).1, (ofHollom t).2.1))).bddAbove
    use b, c
    intro d e hde
    simpa using hbc ⟨h(_, _, _), ⟨hde, by simp⟩, rfl⟩

  -- Using `a ≥ max b c`, we have that all elements of `{(x, y, n) | x ≥ a ∧ y ≥ a}` are comparable
  -- to all elements of `C ∩ level (n + 1)`.
  have : ∀ᶠ a in atTop, embed n '' .Ici (a, a) ⊆ {x | ∀ y ∈ C ∩ level (n + 1), x ≤ y ∨ y ≤ x} := by
    rw [eventually_atTop, level_eq]
    refine ⟨max b c, ?_⟩
    simp only [ge_iff_le, sup_le_iff, embed_apply,
      Set.mem_inter_iff, Set.mem_setOf_eq, and_imp, «forall», ofHollom_toHollom, Prod.forall,
      Set.subset_def, Set.mem_image, Set.mem_Ici, Prod.exists, Prod.mk_le_mk, forall_exists_index,
      EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
    rintro d hbd hcd _ _ _ e f hde hdf rfl rfl rfl g h _ hgh rfl
    right
    apply toHollom_le_toHollom _ (by simp)
    have := hab _ _ hgh
    simp only [Prod.mk_le_mk] at this ⊢
    omega

  -- Combined with the fact that sufficiently large `a` have
  -- `{(x, y, n) | x ≥ a ∧ y ≥ a} ⊆ R \ (C ∩ level n)`, we can easily finish.
  filter_upwards [square_subset_R h, this] with a h₁ h₂
  exact fun x hx ↦ ⟨⟨(h₁ hx).1, h₂ hx⟩, (h₁ hx).2⟩
end Hollom
