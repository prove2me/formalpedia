-- Prove2me | solution 1 for GlobalTheory.AbLaw.CubeOpen.bijective_appTop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:06:32.85862+00:00
-- url     : https://prove2.me/submissions/f9029924-45ae-4bf2-82f4-09a86d80c7c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivBasicOpenOfTrivFibre
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_isAb_pullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeOpen
namespace GlobalTheory.AbLaw.CubeOpen
theorem _root_.solution (hG : GlobalFnsSt) {S S' X : Scheme.{0}} (B : Over S) [GrpObj B]
    (hB : IsAbelianScheme B) {φ : S' ⟶ S} {π : X ⟶ B.left} {f : X ⟶ S'}
    (h : IsPullback π f B.hom φ) : Function.Bijective f.appTop.hom := by
  have h₁ : Function.Bijective (pullback.snd B.hom φ).appTop.hom :=
    hG _ _ (TLinPf.isAb_pullback φ B hB)
  have h₂ : Function.Bijective h.isoPullback.hom.appTop.hom :=
    ConcreteCategory.bijective_of_isIso (h.isoPullback.hom.app ⊤)
  rw [← h.isoPullback_hom_snd, Scheme.Hom.comp_appTop]
  exact h₂.comp h₁
end GlobalTheory.AbLaw.CubeOpen
