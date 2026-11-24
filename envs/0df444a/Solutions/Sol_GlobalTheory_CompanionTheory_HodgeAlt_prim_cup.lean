-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeAlt.prim_cup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:39:01.922043+00:00
-- url     : https://prove2.me/submissions/16acaeaf-3735-4e38-ba67-894977bf7c09

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_cupHyp_add_swap
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_pullHyp2_cup
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeAlt
variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]
  {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.HodgeAlt
theorem _root_.solution (m p q : CoefMap (RingHom.id R) F G)
    (hm : ∀ c, pullHyp1 m c = pullHyp1 p c + pullHyp1 q c) (c : Hyp1 F) :
    pullHyp2 m (cupHyp F c c) = pullHyp2 p (cupHyp F c c) + pullHyp2 q (cupHyp F c c) := by
  have := cupHyp_add_swap G (pullHyp1 p c) (pullHyp1 q c)
  simp only [pullHyp2_cup, hm, map_add, LinearMap.add_apply]
  linear_combination (norm := abel1) this
end GlobalTheory.CompanionTheory.HodgeAlt
