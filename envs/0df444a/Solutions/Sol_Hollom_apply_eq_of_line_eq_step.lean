-- Prove2me | solution 1 for Hollom.apply_eq_of_line_eq_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:11:16.712733+00:00
-- url     : https://prove2.me/submissions/819809f1-71f4-4abd-ad48-7ccc47ba915b

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
import Theorems.Thm_Hollom_embed_strictMono
import Theorems.Thm_Hollom_embed_image_Icc
import Theorems.Thm_Hollom_SpinalMap_ext
import Theorems.Thm_Hollom_SpinalMap_toFun_eq_coe
import Theorems.Thm_Hollom_SpinalMap_mem
import Theorems.Thm_Hollom_SpinalMap_idempotent
import Theorems.Thm_Hollom_SpinalMap_not_lt_of_eq
import Theorems.Thm_Hollom_SpinalMap_mapsTo_Icc_self
import Theorems.Thm_Hollom_SpinalMap_injOn_of_isChain
import Theorems.Thm_Hollom_chainBetween_isChain
import Theorems.Thm_Hollom_card_chainBetween
import Theorems.Thm_Hollom_chainBetween_subset
import Theorems.Thm_Hollom_mapsTo_Icc_image
import Theorems.Thm_Hollom_card_C_inter_Icc_eq
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
open Finset
namespace Hollom
theorem _root_.solution (f : SpinalMap C) {n xl yl xh yh : ℕ}
    (hC : IsChain (· ≤ ·) C)
    (hlo : h(xl, yl, n) ∈ C) (hhi : h(xh, yh, n) ∈ C) (hx : xl ≤ xh) (hy : yl ≤ yh)
    {x y : ℕ}
    (h₁l : h(xl, yl, n) ≤ h(x + 1, y, n)) (h₂l : h(xl, yl, n) ≤ h(x, y + 1, n))
    (h₁h : h(x + 1, y, n) ≤ h(xh, yh, n)) (h₂h : h(x, y + 1, n) ≤ h(xh, yh, n)) :
    f h(x + 1, y, n) = f h(x, y + 1, n) := by
  classical
  -- Write `int` for the interval `[(xl, yl, n), (xh, yh, n)]`, as a finite set, and `I` for the
  -- intersection of `C` with this interval.
  set int : Finset Hollom := (Icc (xl, yl) (xh, yh)).image (embed n)
  set I : Finset Hollom := {x ∈ int | x ∈ C}
  -- Previous results give an exact expression for `#I`.
  have cI : #I = xh + yh + 1 - (xl + yl) := card_C_inter_Icc_eq f hC hx hy hlo hhi
  have int_eq : int = Set.Icc h(xl, yl, n) h(xh, yh, n) := by
    simp only [coe_image, coe_Icc, int, embed_image_Icc]
  -- Write `B` for the union of chains `(xl, yl, n)` to `(x, y, n)` and `(x + 1, y + 1, n)`
  -- to `(xh, yh, n)`, observing that adding either of `(x + 1, y, n)` or `(x, y + 1, n)` would
  -- make `B` into a maximal chain.
  let B : Finset Hollom :=
    (chainBetween xl yl x y ∪ chainBetween (x + 1) (y + 1) xh yh).image (embed n)
  -- The map `f` sends both these points into `int`, by the properties of spinal maps,
  have : f h(x + 1, y, n) ∈ int ∧ f h(x, y + 1, n) ∈ int := by
    rw [← mem_coe, ← mem_coe, int_eq]
    exact ⟨f.mapsTo_Icc_self hC hlo hhi ⟨h₁l, h₁h⟩, f.mapsTo_Icc_self hC hlo hhi ⟨h₂l, h₂h⟩⟩
  simp only [toHollom_le_toHollom_iff_fixed_right] at h₁l h₂l h₁h h₂h
  -- and we can give an exact expression for `#B`, which is exactly one less than `#I`.
  have cB : #B = xh + yh - (xl + yl) := by
    rw [card_image_of_injective _ (embed n).injective, card_union_of_disjoint,
      card_chainBetween h₂l.1 h₁l.2, card_chainBetween h₁h.1 h₂h.2]
    · omega
    · simp [disjoint_left, chainBetween, *]
      omega
  -- It is easy to see that our chain `B` lives entirely within `int`
  have hB : B ⊆ int := by
    refine Finset.image_subset_image ?_
    rw [Finset.union_subset_iff]
    refine ⟨chainBetween_subset.trans ?_, chainBetween_subset.trans ?_⟩
    · exact Finset.Icc_subset_Icc_right (by simp [*])
    · exact Finset.Icc_subset_Icc_left (by simp [*])
  -- and thus `f` must map it to `I`
  have f_maps : Set.MapsTo f B I := by
    simp only [I, Finset.coe_filter]
    exact ((mapsTo_Icc_image hC hlo hhi).mono_left hB).inter (by simp [Set.MapsTo])
  -- and as `B` is a chain, `f` acts injectively on it.
  have f_inj : Set.InjOn f B := by
    refine f.injOn_of_isChain ?_
    simp only [B]
    rw [coe_image]
    have hU : IsChain (· ≤ ·) ((chainBetween xl yl x y ∪ chainBetween (x + 1) (y + 1) xh yh : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
      rw [coe_union, isChain_union]
      refine ⟨chainBetween_isChain, chainBetween_isChain, ?_⟩
      simp [chainBetween, *]
      omega
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hne
    rcases hU hp hq (fun h => hne (congrArg _ h)) with h | h <;> simp [h]
  -- Thus the image of `B` under `f` is all of `I`, except for exactly one element.
  have card_eq : (I \ B.image f).card = 1 := by
    rw [Finset.card_sdiff_of_subset (by rw [← coe_subset, coe_image]; exact f_maps.image_subset), cI, card_image_of_injOn f_inj, cB]
    omega
  -- After applying `f`, both `(x + 1, y, n)` and `(x, y + 1, n)` are omitted from the image of `B`
  -- under `f`: this follows from the fact that adding either to `B` would make it still a chain,
  -- and `f` acts injectively on chains.
  obtain ⟨hleft, hright⟩ : f h(x + 1, y, n) ∉ B.image f ∧ f h(x, y + 1, n) ∉ B.image f := by
    constructor
    all_goals
      simp +contextual only [mem_image, mem_union, embed_apply, Prod.exists, «exists»,
        EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, not_exists, not_and, forall_exists_index,
        and_imp, or_imp, B, forall_and]
      constructor
      · rintro _ _ c a b hab rfl rfl rfl h
        have : (a, b) ≤ (x, y) := (Finset.mem_Icc.1 (chainBetween_subset hab)).2
        rw [← embed_apply, ← embed_apply] at h
        exact f.not_lt_of_eq h (embed_strictMono (this.trans_lt (by simp)))
      · rintro _ _ c a b hab rfl rfl rfl h
        have : (x + 1, y + 1) ≤ (a, b) := (Finset.mem_Icc.1 (chainBetween_subset hab)).1
        rw [← embed_apply, ← embed_apply] at h
        exact f.not_lt_of_eq h.symm (embed_strictMono (this.trans_lt' (by simp)))
  -- Therefore the image of both points is in `I \ B.image f`,
  replace hleft : f h(x + 1, y, n) ∈ I \ B.image f := by simpa [Finset.mem_sdiff, hleft, I] using this.1
  replace hright : f h(x, y + 1, n) ∈ I \ B.image f := by simpa [Finset.mem_sdiff, hright, I] using this.2
  -- but this set has exactly one element, so our two elements must be equal.
  exact Finset.card_le_one.1 card_eq.le _ hleft _ hright
end Hollom
