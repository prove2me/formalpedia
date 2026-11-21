-- Prove2me | solution 1 for JardenShami.fiberRestr_subset_iff_histFun_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:47:30.190204+00:00
-- url     : https://prove2.me/submissions/11c78d10-7b6b-4764-9b67-a63f7fb4765b

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_Kappa_coe_lt_coe
import Theorems.Thm_JardenShami_Kappa_coe_le_coe
import Theorems.Thm_JardenShami_Kappa_coe_mk
import Theorems.Thm_JardenShami_Kappa_coe_inj
import Theorems.Thm_JardenShami_Enumeration_ht_t
import Theorems.Thm_JardenShami_Enumeration_exists_eq
import Theorems.Thm_JardenShami_Enumeration_node_spec
import Theorems.Thm_JardenShami_treeColoring_eq_iff_mem_histFun
attribute [local simp] JardenShami.Kappa.coe_mk

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
theorem _root_.solution (hT : IsKappaTree κ T) (e : Enumeration κ T)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C)
    {β₁ δ₁ β₂ δ₂ : Kappa κ} (h₁ : β₁ ≤ δ₁) (h₂ : β₂ ≤ δ₂) :
    fiberRestr C δ₁ β₁ h₁ ⊆ fiberRestr C δ₂ β₂ h₂ ↔
      histFun (e.node C β₁ δ₁ h₁) ⊆ histFun (e.node C β₂ δ₂ h₂) := by
  obtain ⟨hn₁, hn₁le⟩ := e.node_spec hT hC h₁
  obtain ⟨hn₂, hn₂le⟩ := e.node_spec hT hC h₂
  rw [fiberRestr_subset_iff, histFun_subset_iff]
  constructor
  · rintro ⟨hle, hc⟩ x hx
    have hxβ : ht x < β₁ := hn₁ ▸ ht_lt_ht hx
    have hxκ : ht x < κ.ord := hxβ.trans (Kappa.coe_lt_ord β₁)
    obtain ⟨α, hαx⟩ : ∃ α : Kappa κ, ht x = (α : Ordinal.{w}) :=
      ⟨Kappa.mk (ht x) hxκ, (Kappa.coe_mk _ _).symm⟩
    have hαβ₁ : α < β₁ := Kappa.coe_lt_coe.1 (hαx ▸ hxβ)
    have hαβ₂ : α < β₂ := hαβ₁.trans_le hle
    obtain ⟨i, hi, hix⟩ := e.exists_eq (Kappa.coe_lt_ord α) (show x ∈ Lev T α from hαx)
    rw [← hix] at hx ⊢
    have h1 := (treeColoring_eq_iff_mem_histFun hT e hC hαβ₁ h₁ hi).2
      ⟨hx, e.ht_t (Kappa.coe_lt_ord α) hi⟩
    rw [hc α hαβ₁ hαβ₂] at h1
    exact ((treeColoring_eq_iff_mem_histFun hT e hC hαβ₂ h₂ hi).1 h1).1
  · intro hsub
    have hle : β₁ ≤ β₂ := by
      rw [← Kappa.coe_le_coe, ← hn₁, ← hn₂]
      exact ht_le_ht_of_Iio_subset hsub
    refine ⟨hle, fun α hα₁ hα₂ => ?_⟩
    obtain ⟨hi, -⟩ := hC α δ₁ (hα₁.trans_le h₁)
    have m1 := (treeColoring_eq_iff_mem_histFun hT e hC hα₁ h₁ hi).1 rfl
    have m2 : ((α : Ordinal.{w}), e.t α (C.color α δ₁ (hα₁.trans_le h₁))) ∈
        histFun (e.node C β₂ δ₂ h₂) := ⟨hsub m1.1, m1.2⟩
    exact (Kappa.coe_inj.1 ((treeColoring_eq_iff_mem_histFun hT e hC hα₂ h₂ hi).2 m2)).symm
end JardenShami
