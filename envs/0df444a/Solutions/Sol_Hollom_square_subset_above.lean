-- Prove2me | solution 1 for Hollom.square_subset_above
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:13:31.450843+00:00
-- url     : https://prove2.me/submissions/de804ff2-4acb-4f25-9430-0f98ab33827d

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
import Theorems.Thm_Hollom_SpinalMap_ext
import Theorems.Thm_Hollom_SpinalMap_toFun_eq_coe
import Theorems.Thm_Hollom_SpinalMap_mem
import Theorems.Thm_Hollom_SpinalMap_idempotent
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
theorem _root_.solution (h : (C ∩ level n).Finite) :
    ∀ᶠ a in atTop, embed n '' Set.Ici (a, a) ⊆ {x | ∀ y ∈ C ∩ level n, y ≤ x} \ (C ∩ level n) := by
  -- If `(C ∩ level n)` is empty, trivially we are done.
  obtain h | hne := (C ∩ level n).eq_empty_or_nonempty
  · simp [h]

  -- Otherwise take a maximal pair `(a, b)` so that any `(c, d, n)` in `C` satisfies
  -- `(c, d, n) ≤ (a, b, n)`.
  obtain ⟨a, b, hab⟩ : ∃ a b, ∀ c d, h(c, d, n) ∈ C → c ≤ a ∧ d ≤ b := by
    obtain ⟨⟨a, b⟩, hab⟩ := (h.image (fun t ↦ ((ofHollom t).1, (ofHollom t).2.1))).bddAbove
    use a, b
    intro c d hcd
    simpa using hab ⟨h(_, _, _), ⟨hcd, by simp⟩, rfl⟩

  -- With this pair, we can use the "base" of the square as `max a b + 1`.
  rw [eventually_atTop]
  refine ⟨max a b + 1, ?_⟩
  simp +contextual only [ge_iff_le, sup_le_iff, embed_apply, Set.mem_inter_iff, and_imp, «forall», toHollom_mem_level_iff,
    Prod.forall, Set.subset_def, Set.mem_image, Set.mem_Ici, Prod.exists, Prod.mk_le_mk,
    Set.mem_setOf_eq, forall_exists_index, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq,
    toHollom_le_toHollom_iff_fixed_right, Set.mem_diff, and_true, ← max_add_add_right]

  -- After simplifying, direct calculations show the subset relation as required.
  rintro k hak hbk _ _ _ f g hkf hkg rfl rfl rfl
  constructor
  · rintro c d n hcd rfl
    specialize hab c d hcd
    omega
  · intro hfg
    specialize hab _ _ hfg
    omega
end Hollom
