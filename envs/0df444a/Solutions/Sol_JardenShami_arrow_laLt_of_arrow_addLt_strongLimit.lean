-- Prove2me | solution 1 for JardenShami.arrow_laLt_of_arrow_addLt_strongLimit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:35.470092+00:00
-- url     : https://prove2.me/submissions/01d44455-155f-4547-a333-db5da86244b0

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section2
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Theorems.Thm_JardenShami_arrow_laLt_of_arrow_addLt_of_card

set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
variable {X : Type w} [LinearOrder X]
namespace JardenShami
theorem _root_.solution (μ : Cardinal.{v}) (hμ : μ.IsStrongLimit)
    (F : Set (Set X)) (h : Arrow F F (addLt μ)) : Arrow F F (laLt μ) := by
  refine arrow_laLt_of_arrow_addLt_of_card μ (fun D hD => ?_) F h
  rw [← Cardinal.power_def, Cardinal.mk_option]
  rcases lt_or_ge #D ℵ₀ with hfin | hinf
  · exact (Cardinal.power_lt_aleph0 (Cardinal.add_lt_aleph0 hfin Cardinal.one_lt_aleph0)
      hfin).trans_le hμ.aleph0_le
  · rw [Cardinal.add_one_of_aleph0_le hinf, Cardinal.power_self_eq hinf]
    exact hμ.isStrongPrelimit hD
end JardenShami
