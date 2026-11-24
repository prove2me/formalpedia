-- Prove2me | solution 1 for GlobalTheory.ThetaBaseChange.exists_cmp_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:11:40.730944+00:00
-- url     : https://prove2.me/submissions/8be1c592-5e6e-404b-8c0d-90d180b4d7d4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
namespace GlobalTheory.ThetaBaseChange
theorem _root_.solution (ht : t' ≫ g = t) {A : Over S} {A' : Over S'} {Φ : A'.left ⟶ A.left}
    (hp : IsPullback Φ A'.hom A.hom g) :
    ∃ ω : (Over.mk t ⊗ A).left ⟶ (Over.mk t' ⊗ A').left, ω ≫ (fst (Over.mk t') A').left = (fst (Over.mk t) A).left ∧
      ω ≫ (snd (Over.mk t') A').left ≫ Φ = (snd (Over.mk t) A).left := by
  subst ht
  have hsq : (snd (Over.mk (t' ≫ g)) A).left ≫ A.hom = ((fst (Over.mk (t' ≫ g)) A).left ≫ t') ≫ g := by
    rw [Over.w, Category.assoc]
    exact (Over.w (fst (Over.mk (t' ≫ g)) A)).symm
  let c : (Over.mk (t' ≫ g) ⊗ A).left ⟶ A'.left :=
    hp.lift (snd (Over.mk (t' ≫ g)) A).left ((fst (Over.mk (t' ≫ g)) A).left ≫ t') hsq
  let U : Over S' := Over.mk ((fst (Over.mk (t' ≫ g)) A).left ≫ t')
  let a : U ⟶ Over.mk t' := Over.homMk (fst (Over.mk (t' ≫ g)) A).left rfl
  let b : U ⟶ A' := Over.homMk c (hp.lift_snd _ _ _)
  refine ⟨(lift a b).left, ?_, ?_⟩
  · rw [← Over.comp_left, lift_fst]
    rfl
  · rw [← Category.assoc, ← Over.comp_left, lift_snd]
    exact hp.lift_fst _ _ _
end GlobalTheory.ThetaBaseChange
