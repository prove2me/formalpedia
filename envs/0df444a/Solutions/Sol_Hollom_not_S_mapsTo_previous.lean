-- Prove2me | solution 1 for Hollom.not_S_mapsTo_previous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:36:44.94171+00:00
-- url     : https://prove2.me/submissions/478cc320-92d9-45a2-b6eb-1211ae64912a

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
import Theorems.Thm_Hollom_line_injOn
import Theorems.Thm_Hollom_line_mapsTo
import Theorems.Thm_Hollom_SpinalMap_ext
import Theorems.Thm_Hollom_SpinalMap_toFun_eq_coe
import Theorems.Thm_Hollom_SpinalMap_mem
import Theorems.Thm_Hollom_SpinalMap_eq_self_of_mem
import Theorems.Thm_Hollom_SpinalMap_idempotent
import Theorems.Thm_Hollom_SpinalMap_eq_of_le
import Theorems.Thm_Hollom_SpinalMap_injOn_of_isChain
import Theorems.Thm_Hollom_image_chainBetween_isChain
import Theorems.Thm_Hollom_card_chainBetween
import Theorems.Thm_Hollom_chainBetween_subset
import Theorems.Thm_Hollom_square_subset_S
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
open Finset
namespace Hollom
theorem _root_.solution (hC : IsChain (· ≤ ·) C)
    (hCn : (C ∩ level n).Finite) (hn : n ≠ 0)
    (h : ∀ x ∈ S n C \ (C ∩ level n), f x ∈ C ∩ level (n - 1)) :
    False := by
  -- Take `a` such that `{(x, y, n) | x ≥ a ∧ y ≥ a} ⊆ S \ (C ∩ level n)`...
  obtain ⟨a, ha⟩ := (square_subset_S hCn).exists
  -- ...then let `F` be the chain from `(a, a)` to `(3 * a, a)`...
  let F : Finset Hollom := (chainBetween a a (3 * a) a).image (embed n)
  -- ...observing that by definition of `a`, we know `F` is entirely within `S \ (C ∩ level n)`...
  have F_subs : (F : Set Hollom) ⊆ S n C \ (C ∩ level n) := calc
    (F : Set Hollom) = embed n '' chainBetween a a (3 * a) a := Finset.coe_image
    _ ⊆ embed n '' Finset.Icc (a, a) (3 * a, a) := Set.image_mono chainBetween_subset
    _ = embed n '' Set.Icc (a, a) (3 * a, a) := by simp
    _ ⊆ embed n '' Set.Ici (a, a) := Set.image_mono Set.Icc_subset_Ici_self
    _ ⊆ S n C \ (C ∩ level n) := ha
  -- ...and it has length `2a+1`.
  have card_F : #F = 2 * a + 1 := by
    rw [Finset.card_image_of_injective _ (embed n).injective,
      card_chainBetween (by omega) (by simp)]
    omega
  let T := {x ∈ C ∩ level (n - 1) | line x < 2 * a}
  -- Therefore, the image of `F` is within `C ∩ level (n - 1)`, and each of its points must be
  -- within `{(x, y, n - 1) | x + y < 2 * a}`. That is, the image of `F` under `f` is within `T`.
  have F_mapsTo : Set.MapsTo f F T := by
    intro x hx
    refine ⟨h _ (F_subs hx), ?_⟩
    set c := f x with hc
    have hc' : c ∈ C ∩ level (n - 1) := h _ (F_subs hx)
    clear_value c
    rw [coe_image, chainBetween, Ico_self, if_pos (by omega), empty_union, ← Icc_map_sectL] at hx
    simp only [embed_apply, coe_map, Function.Embedding.sectL_apply, coe_Icc,
      Set.mem_image, Set.mem_Icc, exists_exists_and_eq_and] at hx
    obtain ⟨b, ⟨hab, hba⟩, rfl⟩ := hx
    induction hc'.2 using induction_on_level with | h u v =>
    simp only [line_toHollom]
    by_contra!
    have le : h(b, a, n) ≤ h(u, v, n - 1) := by
      match n, hn with
      | n + 1, _ =>
          simp only [add_tsub_cancel_right]
          apply HollomOrder.next_add (by omega)
    have : f h(u, v, n - 1) = f h(b, a, n) := by rw [f.eq_self_of_mem hc'.1, hc]
    have := le_of_toHollom_le_toHollom (f.eq_of_le this.symm le).ge
    omega
  -- And `f` acts injectively on `F`, as it is a chain.
  have F_inj : Set.InjOn f F := f.injOn_of_isChain image_chainBetween_isChain
  -- By definition of `T`, the `line` map sends it to the interval `[0, 2a)`
  have line_mapsTo : Set.MapsTo line T (range (2 * a)) := by
    rintro x ⟨_, hx⟩
    simpa using hx
  -- and it does so injectively, as `T` is a chain.
  have line_inj : Set.InjOn line T :=
    line_injOn (n - 1)
      (hC.mono (by simp +contextual [Set.subset_def, T]))
      (by simp +contextual [Set.subset_def, T])
  -- Therefore `line ∘ f` sends `F` to `[0, 2a)` injectively
  have line_F_mapsTo : Set.MapsTo (line ∘ f) F (range (2 * a)) := line_mapsTo.comp F_mapsTo
  -- which is a contradiction by cardinality arguments.
  have := card_le_card_of_injOn _ line_F_mapsTo (line_inj.comp F_inj F_mapsTo)
  simp only [Finset.card_range] at this
  omega
end Hollom
