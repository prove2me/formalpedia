-- Prove2me | solution 1 for GlobalTheory.ThetaBaseChange.exists_cmp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:11:39.892992+00:00
-- url     : https://prove2.me/submissions/31138f7f-fbae-493e-ab6e-18f2b8d67f36

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush

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
    (w : Φ ≫ A.hom = A'.hom ≫ g) :
    ∃ Ω : (Over.mk t' ⊗ A').left ⟶ (Over.mk t ⊗ A).left, Ω ≫ (fst (Over.mk t) A).left = (fst (Over.mk t') A').left ∧
      Ω ≫ (snd (Over.mk t) A).left = (snd (Over.mk t') A').left ≫ Φ := by
  subst ht
  let U : Over S := Over.mk ((Over.mk t' ⊗ A').hom ≫ g)
  let a : U ⟶ Over.mk (t' ≫ g) := Over.homMk (fst (Over.mk t') A').left (by
    show (fst (Over.mk t') A').left ≫ t' ≫ g = (Over.mk t' ⊗ A').hom ≫ g
    rw [← Category.assoc]
    exact congrArg (· ≫ g) (Over.w (fst (Over.mk t') A')))
  let b : U ⟶ A := Over.homMk ((snd (Over.mk t') A').left ≫ Φ) (by
    rw [Category.assoc, w, ← Category.assoc]
    exact congrArg (· ≫ g) (Over.w (snd (Over.mk t') A')))
  refine ⟨(lift a b).left, ?_, ?_⟩
  · rw [← Over.comp_left, lift_fst]
    rfl
  · rw [← Over.comp_left, lift_snd]
    rfl
end GlobalTheory.ThetaBaseChange
