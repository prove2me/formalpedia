-- Prove2me | solution 1 for JardenShami.card_lev_treeOfColoring_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:47:47.316561+00:00
-- url     : https://prove2.me/submissions/1564a0cc-2896-4d6b-ba64-9eb43324dc96

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Theorems.Thm_JardenShami_card_lev_treeOfColoring_le_of_aleph0_le

set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution (κ μ : Cardinal.{w}) (hunc : ℵ₀ < κ)
    (C : Coloring (Kappa κ) (Kappa μ)) (hC : IsLocallyAdditive C) :
    ∀ β : Ordinal.{w}, #(Lev (treeOfColoring C) β) ≤ μ := by
  exact card_lev_treeOfColoring_le_of_aleph0_le κ μ hunc.le C hC
end JardenShami
