-- Prove2me | solution 1 for JardenShami.Kappa.exists_gt_of_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:43:48.051254+00:00
-- url     : https://prove2.me/submissions/2d56bc36-745d-41c8-b296-971054c848a8

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Theorems.Thm_JardenShami_Kappa_mk_Iic_lt

set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}}
namespace JardenShami
namespace Kappa
theorem _root_.solution (hκ : ℵ₀ ≤ κ) {S : Set (Kappa κ)} (hS : #S = κ)
    (x : Kappa κ) : ∃ y ∈ S, x < y := by
  by_contra h
  push Not at h
  have h1 : #S ≤ #(Set.Iic x) := Cardinal.mk_le_mk_of_subset fun y hy => h y hy
  rw [hS] at h1
  exact (h1.trans_lt (Kappa.mk_Iic_lt hκ x)).false
end Kappa
end JardenShami
