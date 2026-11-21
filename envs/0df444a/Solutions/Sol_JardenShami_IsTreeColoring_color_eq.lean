-- Prove2me | solution 1 for JardenShami.IsTreeColoring.color_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:06.402821+00:00
-- url     : https://prove2.me/submissions/c635e7b7-9e07-45a2-9059-76f9f699a2e3

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_Tree_eq_of_le_of_le_of_ht_eq
import Theorems.Thm_JardenShami_Enumeration_ht_t

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
namespace IsTreeColoring
theorem _root_.solution {e : Enumeration κ T}
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C) {α δ : Kappa κ}
    (h : α < δ) {i : Ordinal.{w}} (hi : i < (#(Lev T (α : Ordinal.{w}))).ord)
    (hle : e.t α i ≤ e.t δ 0) : (C.color α δ h : Ordinal.{w}) = i := by
  obtain ⟨hj, hjle⟩ := hC α δ h
  have hα := Kappa.coe_lt_ord α
  refine (e.bijOn α hα).injOn hj hi (eq_of_le_of_le_of_ht_eq hjle hle ?_)
  rw [e.ht_t hα hj, e.ht_t hα hi]
end IsTreeColoring
end JardenShami
