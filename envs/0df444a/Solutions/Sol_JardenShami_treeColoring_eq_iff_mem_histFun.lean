-- Prove2me | solution 1 for JardenShami.treeColoring_eq_iff_mem_histFun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:44.740569+00:00
-- url     : https://prove2.me/submissions/04fc6f6d-f37a-454c-ae7b-c1a09412d3de

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_Kappa_coe_lt_coe
import Theorems.Thm_JardenShami_Enumeration_ht_t
import Theorems.Thm_JardenShami_lt_of_le_of_le_of_ht_lt
import Theorems.Thm_JardenShami_IsTreeColoring_color_eq
import Theorems.Thm_JardenShami_Enumeration_node_spec

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
    {α β δ : Kappa κ} (hαβ : α < β) (hβδ : β ≤ δ) {i : Ordinal.{w}}
    (hi : i < (#(Lev T (α : Ordinal.{w}))).ord) :
    ((C.color α δ (hαβ.trans_le hβδ) : Ordinal.{w}) = i) ↔
      ((α : Ordinal.{w}), e.t α i) ∈ histFun (e.node C β δ hβδ) := by
  obtain ⟨hn, hnle⟩ := e.node_spec hT hC hβδ
  have hα := Kappa.coe_lt_ord α
  have hαβ' : (α : Ordinal.{w}) < β := Kappa.coe_lt_coe.2 hαβ
  constructor
  · intro hc
    obtain ⟨-, hle⟩ := hC α δ (hαβ.trans_le hβδ)
    rw [hc] at hle
    refine ⟨lt_of_le_of_le_of_ht_lt hle hnle ?_, e.ht_t hα hi⟩
    rw [e.ht_t hα hi, hn]
    exact hαβ'
  · rintro ⟨hlt, -⟩
    exact hC.color_eq _ hi (hlt.le.trans hnle)
end JardenShami
