-- Prove2me | solution 1 for JardenShami.exists_big_above
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:16.491459+00:00
-- url     : https://prove2.me/submissions/14cc286b-a6dc-4a6e-ab2a-3004a1504918

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
import Theorems.Thm_JardenShami_exists_le_ht_eq
import Theorems.Thm_JardenShami_exists_big_cone
import Theorems.Thm_JardenShami_mk_levLt_lt
import Theorems.Thm_JardenShami_lt_of_le_of_le_of_ht_lt


set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
theorem _root_.solution {κ : Cardinal.{w}} (hκ : κ.IsRegular) (hT : IsKappaTree κ T) {x : T}
    (hx : κ ≤ #(Set.Ici x)) {α : Ordinal.{w}} (hxα : ht x < α) (hα : α < κ.ord) :
    ∃ y ∈ Lev T α, x < y ∧ κ ≤ #(Set.Ici y) := by
  have hκ0 := hκ.aleph0_le
  let U : Set T := {s | x ≤ s ∧ α ≤ ht s}
  have hU : κ ≤ #U := by
    by_contra hc
    have hsub : Set.Ici x ⊆ U ∪ {s : T | ht s < α} := by
      intro s hs
      by_cases h : α ≤ ht s
      · exact Or.inl ⟨hs, h⟩
      · exact Or.inr (lt_of_not_ge h)
    have := (Cardinal.mk_le_mk_of_subset hsub).trans (Cardinal.mk_union_le _ _)
    exact hx.not_gt (this.trans_lt (Cardinal.add_lt_of_lt hκ0 (lt_of_not_ge hc)
      (mk_levLt_lt hκ hT hα)))
  obtain ⟨y, ⟨hyL, hxy⟩, hy⟩ := exists_big_cone hκ (L := {y | y ∈ Lev T α ∧ x < y}) hU
    ((Cardinal.mk_le_mk_of_subset fun y hy => hy.1).trans_lt (hT.2 α hα)) (by
      rintro s ⟨hxs, hαs⟩
      obtain ⟨y, hys, hyα⟩ := exists_le_ht_eq hαs
      exact ⟨y, ⟨hyα, lt_of_le_of_le_of_ht_lt hxs hys (by rw [hyα]; exact hxα)⟩, hys⟩)
  exact ⟨y, hyL, hxy, hy⟩
end JardenShami
