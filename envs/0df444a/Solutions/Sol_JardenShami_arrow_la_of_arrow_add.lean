-- Prove2me | solution 1 for JardenShami.arrow_la_of_arrow_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:20.895664+00:00
-- url     : https://prove2.me/submissions/3c8303fd-adb5-4b3e-a25c-fb228bd5ecdb

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section2
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Theorems.Thm_JardenShami_arrow_la_of_arrow_add_of_card
import Theorems.Thm_JardenShami_arrow_addLe_of_arrow_addEq

set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
variable {X : Type w} [LinearOrder X]
namespace JardenShami
theorem _root_.solution (κ μ : Cardinal.{v}) (hκ : 2 ^ μ + ℵ₀ ≤ κ) (F : Set (Set X))
    (h : Arrow F F (addEq κ)) : Arrow F F (laEq μ) := by
  have hμκ : 2 ^ μ ≤ κ := le_self_add.trans hκ
  have hω : ℵ₀ ≤ κ := le_add_self.trans hκ
  refine arrow_la_of_arrow_add_of_card (· = μ) (· ≤ κ) (fun D hD => ?_) F
    (arrow_addLe_of_arrow_addEq κ F F h)
  refine ⟨hD ▸ (Cardinal.cantor μ).le.trans hμκ, ?_⟩
  rw [← Cardinal.power_def, Cardinal.mk_option]
  rcases lt_or_ge #D ℵ₀ with hfin | hinf
  · exact (Cardinal.power_lt_aleph0 (Cardinal.add_lt_aleph0 hfin Cardinal.one_lt_aleph0)
      hfin).le.trans hω
  · rw [Cardinal.add_one_of_aleph0_le hinf, Cardinal.power_self_eq hinf, hD]
    exact hμκ
end JardenShami
