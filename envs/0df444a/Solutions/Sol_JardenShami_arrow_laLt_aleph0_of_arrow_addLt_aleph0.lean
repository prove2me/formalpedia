-- Prove2me | solution 1 for JardenShami.arrow_laLt_aleph0_of_arrow_addLt_aleph0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:34.76529+00:00
-- url     : https://prove2.me/submissions/391222ed-e2e4-4321-a4b1-cf18760bd324

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
theorem _root_.solution (F : Set (Set X))
    (h : Arrow F F (addLt (ℵ₀ : Cardinal.{v}))) : Arrow F F (laLt (ℵ₀ : Cardinal.{v})) := by
  refine arrow_laLt_of_arrow_addLt_of_card ℵ₀ (fun D hD => ?_) F h
  have : Finite D := Cardinal.lt_aleph0_iff_finite.1 hD
  exact Cardinal.lt_aleph0_iff_finite.2 inferInstance
end JardenShami
