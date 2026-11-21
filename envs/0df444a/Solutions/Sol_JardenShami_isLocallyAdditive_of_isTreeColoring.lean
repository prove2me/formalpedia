-- Prove2me | solution 1 for JardenShami.isLocallyAdditive_of_isTreeColoring
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:43.457117+00:00
-- url     : https://prove2.me/submissions/f65c3ceb-2a9e-4f62-9476-08f269d4fb59

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_Kappa_coe_lt_coe
import Theorems.Thm_JardenShami_Kappa_coe_inj
import Theorems.Thm_JardenShami_Enumeration_ht_t
import Theorems.Thm_JardenShami_lt_of_le_of_le_of_ht_lt
import Theorems.Thm_JardenShami_IsTreeColoring_color_eq

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
theorem _root_.solution (e : Enumeration κ T)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C) :
    IsLocallyAdditive C := by
  intro a b c d hab hbc hcd h
  have ha := Kappa.coe_lt_ord a
  have hb := Kappa.coe_lt_ord b
  obtain ⟨hi, hic⟩ := hC b c hbc
  obtain ⟨-, hid⟩ := hC b d (hbc.trans hcd)
  rw [← h] at hid
  obtain ⟨hj, hjc⟩ := hC a c (hab.trans hbc)
  have hlt : e.t a (C.color a c (hab.trans hbc)) < e.t b (C.color b c hbc) := by
    refine lt_of_le_of_le_of_ht_lt hjc hic ?_
    rw [e.ht_t ha hj, e.ht_t hb hi]
    exact Kappa.coe_lt_coe.2 hab
  exact Kappa.coe_inj.1 (hC.color_eq _ hj (hlt.le.trans hid)).symm
end JardenShami
