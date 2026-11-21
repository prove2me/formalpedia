-- Prove2me | solution 1 for JardenShami.Kappa.exists_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:26.604769+00:00
-- url     : https://prove2.me/submissions/34406603-da16-4a1b-abce-20ca97959223

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
import Theorems.Thm_JardenShami_Kappa_exists_gt_of_card_eq
import Theorems.Thm_JardenShami_Kappa_mk_eq


set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
namespace Kappa
theorem _root_.solution {κ : Cardinal.{w}} (hκ : ℵ₀ ≤ κ) (x : Kappa κ) : ∃ y, x < y := by
  obtain ⟨y, -, h⟩ := Kappa.exists_gt_of_card_eq hκ
    (show #(Set.univ : Set (Kappa κ)) = κ by rw [Cardinal.mk_univ, Kappa.mk_eq]) x
  exact ⟨y, h⟩
end Kappa
end JardenShami
