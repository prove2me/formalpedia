-- Prove2me | solution 1 for GlobalTheory.ThetaBaseChange.translT_cmp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:26:04.616866+00:00
-- url     : https://prove2.me/submissions/287c4097-26e8-49e7-9f14-072e45f7bfe4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Theorems.Thm_GlobalTheory_ThetaBaseChange_cmp_ext
import Theorems.Thm_GlobalTheory_ThetaBaseChange_translPt_cmp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaBaseChange
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
variable {S S' W : Scheme.{0}} {g : S' ⟶ S} {t : W ⟶ S} {t' : W ⟶ S'}
variable {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {Φ : A'.left ⟶ A.left}
namespace GlobalTheory.ThetaBaseChange
theorem _root_.solution (ht : t' ≫ g = t) (hp : IsGrpPullback A' A g Φ) {x : Over.mk t ⟶ A} {x' : Over.mk t' ⟶ A'}
    (hx : x'.left ≫ Φ = x.left) {ω : (Over.mk t ⊗ A).left ⟶ (Over.mk t' ⊗ A').left}
    (h₁ : ω ≫ (fst (Over.mk t') A').left = (fst (Over.mk t) A).left)
    (h₂ : ω ≫ (snd (Over.mk t') A').left ≫ Φ = (snd (Over.mk t) A).left) :
    (translT A x).left ≫ ω = ω ≫ (translT A' x').left := by
  unfold translT
  have e1 : (lift (fst (Over.mk t) A) (translPt A x)).left ≫ (fst (Over.mk t) A).left = (fst (Over.mk t) A).left := by
    rw [← Over.comp_left, lift_fst]
  have e2 : (lift (fst (Over.mk t') A') (translPt A' x')).left ≫ (fst (Over.mk t') A').left =
      (fst (Over.mk t') A').left := by
    rw [← Over.comp_left, lift_fst]
  have e3 : (lift (fst (Over.mk t) A) (translPt A x)).left ≫ (snd (Over.mk t) A).left = (translPt A x).left := by
    rw [← Over.comp_left, lift_snd]
  have e4 : (lift (fst (Over.mk t') A') (translPt A' x')).left ≫ (snd (Over.mk t') A').left =
      (translPt A' x').left := by
    rw [← Over.comp_left, lift_snd]
  apply cmp_ext hp.1
  · rw [Category.assoc, h₁, e1, Category.assoc, e2, h₁]
  · rw [Category.assoc, h₂, e3, Category.assoc, reassoc_of% e4, translPt_cmp ht hp hx h₁ h₂]
end GlobalTheory.ThetaBaseChange
