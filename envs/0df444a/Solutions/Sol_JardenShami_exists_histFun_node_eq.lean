-- Prove2me | solution 1 for JardenShami.exists_histFun_node_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:45.373924+00:00
-- url     : https://prove2.me/submissions/4a3266c0-aa30-4b89-94fe-133a4652f307

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_Tree_eq_of_le_of_le_of_ht_eq
import Theorems.Thm_JardenShami_Kappa_coe_le_coe
import Theorems.Thm_JardenShami_Kappa_coe_mk
import Theorems.Thm_JardenShami_Enumeration_ht_t
import Theorems.Thm_JardenShami_zero_lt_ord_lev
import Theorems.Thm_JardenShami_Enumeration_node_spec
attribute [local simp] JardenShami.Kappa.coe_mk

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
theorem _root_.solution (hT : IsKappaTree κ T) (e : Enumeration κ T) (he : e.Covers)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C) (t : T) :
    ∃ (β δ : Kappa κ) (h : β ≤ δ), histFun (e.node C β δ h) = histFun t := by
  obtain ⟨δ, hδ, htδ⟩ := he t
  have htκ : ht t < κ.ord := (ht_lt_ht htδ).trans_eq (e.ht_t hδ (zero_lt_ord_lev hT hδ))
    |>.trans hδ
  let δ' : Kappa κ := Kappa.mk δ hδ
  let β : Kappa κ := Kappa.mk (ht t) htκ
  have hβδ : β ≤ δ' := by
    rw [← Kappa.coe_le_coe, Kappa.coe_mk, Kappa.coe_mk]
    exact ((ht_lt_ht htδ).trans_eq (e.ht_t hδ (zero_lt_ord_lev hT hδ))).le
  refine ⟨β, δ', hβδ, congrArg histFun ?_⟩
  obtain ⟨hn, hnle⟩ := e.node_spec hT hC hβδ
  have hδ' : ((δ' : Ordinal.{w})) = δ := Kappa.coe_mk _ _
  rw [hδ'] at hnle
  refine eq_of_le_of_le_of_ht_eq hnle htδ.le ?_
  rw [hn, Kappa.coe_mk]
end JardenShami
