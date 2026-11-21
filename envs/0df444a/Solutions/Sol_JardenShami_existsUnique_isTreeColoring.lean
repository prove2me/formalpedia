-- Prove2me | solution 1 for JardenShami.existsUnique_isTreeColoring
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:42.649001+00:00
-- url     : https://prove2.me/submissions/c2251f36-3a5f-4736-aa1b-76d77bae3005

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_Kappa_coe_lt_coe
import Theorems.Thm_JardenShami_Kappa_coe_mk
import Theorems.Thm_JardenShami_Kappa_coe_inj
import Theorems.Thm_JardenShami_Enumeration_ht_t
import Theorems.Thm_JardenShami_zero_lt_ord_lev
import Theorems.Thm_JardenShami_Enumeration_exists_eq
import Theorems.Thm_JardenShami_IsTreeColoring_color_eq
import Theorems.Thm_JardenShami_card_lev_le_levelSup
import Theorems.Thm_JardenShami_Pairs_exists_eq_mk
import Theorems.Thm_JardenShami_Pairs_mk_inj

attribute [local simp] JardenShami.Kappa.coe_mk

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
theorem _root_.solution (hT : IsKappaTree κ T) (e : Enumeration κ T) :
    ∃! C, IsTreeColoring e C := by
  classical
  have hex : ∀ p : Pairs (Kappa κ), ∃ x : Kappa (levelSup κ T), ∀ (α δ : Kappa κ) (h : α < δ),
      p = Pairs.mk α δ h.ne → (x : Ordinal.{w}) < (#(Lev T (α : Ordinal.{w}))).ord ∧
        e.t α x ≤ e.t δ 0 := by
    intro p
    obtain ⟨α, δ, h, rfl⟩ := p.exists_eq_mk
    have hδ := Kappa.coe_lt_ord δ
    have hα := Kappa.coe_lt_ord α
    have hz := e.ht_t hδ (zero_lt_ord_lev hT hδ)
    have hαz : (α : Ordinal.{w}) < ht (e.t δ 0) := by
      rw [hz]
      exact Kappa.coe_lt_coe.2 h
    obtain ⟨s, hs, hsα⟩ := exists_lt_ht_eq hαz
    obtain ⟨i, hi, rfl⟩ := e.exists_eq hα hsα
    have hiμ : i < (levelSup κ T).ord :=
      hi.trans_le (Cardinal.ord_le_ord.2 (card_lev_le_levelSup α))
    refine ⟨Kappa.mk i hiμ, fun α' δ' h' hp => ?_⟩
    obtain ⟨rfl, rfl⟩ := Pairs.mk_inj h h' hp
    rw [Kappa.coe_mk]
    exact ⟨hi, hs.le⟩
  choose C hC using hex
  refine ⟨C, fun α δ h => hC _ α δ h rfl, fun C' hC' => ?_⟩
  funext p
  obtain ⟨α, δ, h, rfl⟩ := p.exists_eq_mk
  change Coloring.color C' α δ h = Coloring.color C α δ h
  obtain ⟨hi, hle⟩ := hC _ α δ h rfl
  exact Kappa.coe_inj.1 (hC'.color_eq h hi hle)
end JardenShami
