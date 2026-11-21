-- Prove2me | solution 1 for JardenShami.exists_wellPruned_subtree_downward
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:47:02.786039+00:00
-- url     : https://prove2.me/submissions/64eaf1e8-d681-4b16-9e01-d7bed25997a0

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
import Theorems.Thm_JardenShami_ht_subtype_of_downward
import Theorems.Thm_JardenShami_exists_le_ht_eq
import Theorems.Thm_JardenShami_exists_big_cone
import Theorems.Thm_JardenShami_exists_big_above
import Theorems.Thm_JardenShami_Kappa_coe_inj
import Theorems.Thm_JardenShami_Kappa_mk_eq
import Theorems.Thm_JardenShami_Tree_eq_of_le_of_le_of_ht_eq
import Theorems.Thm_JardenShami_Tree_ht_lt_height
import Theorems.Thm_JardenShami_Tree_lev_nonempty
import Theorems.Thm_JardenShami_le_total_of_le


set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
theorem _root_.solution (κ : Cardinal.{w}) (hκ : κ.IsRegular)
    (T : Type w) [PartialOrder T] [IsTree T] (hT : IsKappaTree κ T) :
    ∃ S : Set T, (∀ s ∈ S, ∀ t < s, t ∈ S) ∧ IsKappaTree κ S ∧ WellPruned S := by
  have hκ0 := hκ.aleph0_le
  have h0 : (0 : Ordinal.{w}) < κ.ord := Cardinal.ord_pos.2 (Cardinal.aleph0_pos.trans_le hκ0)
  -- `T` has `≥ κ` nodes
  have hTκ : κ ≤ #(Set.univ : Set T) := by
    have hl : ∀ β : Kappa κ, (Lev T (β : Ordinal.{w})).Nonempty := fun β =>
      lev_nonempty (by rw [hT.1]; exact Kappa.coe_lt_ord β)
    choose c hc using hl
    rw [Cardinal.mk_univ, ← Kappa.mk_eq κ]
    refine Cardinal.mk_le_of_injective (f := c) fun a b h => ?_
    have := (hc a).symm.trans ((congrArg ht h).trans (hc b))
    exact Kappa.coe_inj.1 this
  -- a root with `κ` nodes above it
  obtain ⟨r, hr0, hr⟩ := exists_big_cone hκ hTκ (hT.2 0 h0) (by
    intro s _
    obtain ⟨y, hys, hy⟩ := exists_le_ht_eq (zero_le : (0 : Ordinal.{w}) ≤ ht s)
    exact ⟨y, hy, hys⟩)
  have hr0' : ht r = 0 := hr0
  let S : Set T := {t | r ≤ t ∧ κ ≤ #(Set.Ici t)}
  have hdown : ∀ s ∈ S, ∀ t < s, t ∈ S := by
    rintro s ⟨hrs, hs⟩ t hts
    refine ⟨?_, hs.trans (Cardinal.mk_le_mk_of_subset fun u hu => hts.le.trans hu)⟩
    rcases le_total_of_le hrs hts.le with h | h
    · exact h
    · rcases h.lt_or_eq with h | h
      · exact absurd (ht_lt_ht h) (by rw [hr0']; exact not_lt_zero)
      · exact h ▸ le_rfl
  have hht : ∀ x : S, ht x = ht (x : T) := ht_subtype_of_downward hdown
  -- extension inside `S`
  have hext : ∀ x : S, ∀ α : Ordinal.{w}, ht (x : T) < α → α < κ.ord →
      ∃ y : S, ht (y : T) = α ∧ x < y := by
    intro x α hxα hα
    obtain ⟨y, hyL, hxy, hy⟩ := exists_big_above hκ hT x.2.2 hxα hα
    exact ⟨⟨y, x.2.1.trans hxy.le, hy⟩, hyL, hxy⟩
  have rS : r ∈ S := ⟨le_rfl, hr⟩
  have hheight : height S = κ.ord := by
    refine IsLeast.csInf_eq ⟨?_, fun α hα => ?_⟩
    · refine Set.eq_empty_of_forall_notMem fun x hx => ?_
      have : ht x = κ.ord := hx
      rw [hht] at this
      exact (hT.1 ▸ ht_lt_height (x : T)).ne this
    · by_contra hc
      have hlt := lt_of_not_ge hc
      have hne : (Lev S α).Nonempty := by
        rcases eq_or_ne α 0 with rfl | hα0
        · exact ⟨⟨r, rS⟩, (hht _).trans hr0'⟩
        · obtain ⟨y, hy, -⟩ := hext ⟨r, rS⟩ α (by rw [hr0']; exact pos_iff_ne_zero.2 hα0) hlt
          exact ⟨y, (hht y).trans hy⟩
      obtain ⟨y, hy⟩ := hne
      have hα' : Lev S α = ∅ := hα
      rw [hα'] at hy
      exact hy
  refine ⟨S, hdown, ⟨hheight, fun α hα => ?_⟩, ⟨⟨⟨r, rS⟩, (hht _).trans hr0', ?_⟩, ?_⟩⟩
  · refine (Cardinal.mk_le_of_injective (f := fun x : Lev S α =>
      (⟨x.1.1, (hht x.1).symm.trans x.2⟩ : Lev T α)) ?_).trans_lt (hT.2 α hα)
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : Lev T α => (z : T)) h))
  · intro y hy
    have hy' : ht (y : T) = 0 := (hht y).symm.trans hy
    exact Subtype.ext (eq_of_le_of_le_of_ht_eq y.2.1 le_rfl (hr0'.trans hy'.symm)).symm
  · intro x α hxα hα
    rw [hheight] at hα
    rw [hht] at hxα
    obtain ⟨y, hy, hxy⟩ := hext x α hxα hα
    exact ⟨y, (hht y).trans hy, hxy⟩
end JardenShami
