-- Prove2me | solution 1 for JardenShami.Kappa.card_eq_of_forall_exists_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:43:19.75949+00:00
-- url     : https://prove2.me/submissions/465fc806-2374-42d7-8920-1ab2eec314e3

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Theorems.Thm_JardenShami_Kappa_mk_eq
import Theorems.Thm_JardenShami_Kappa_exists_gt_of_card_lt

set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}}
namespace JardenShami
namespace Kappa
theorem _root_.solution (hκ : κ.IsRegular) {S : Set (Kappa κ)}
    (h : ∀ x, ∃ y ∈ S, x < y) : #S = κ := by
  refine le_antisymm ((Cardinal.mk_set_le S).trans (Kappa.mk_eq κ).le) ?_
  by_contra hS
  obtain ⟨x, hx⟩ := Kappa.exists_gt_of_card_lt hκ (lt_of_not_ge hS)
  obtain ⟨y, hy, hxy⟩ := h x
  exact (hx y hy).not_gt hxy
end Kappa
end JardenShami
