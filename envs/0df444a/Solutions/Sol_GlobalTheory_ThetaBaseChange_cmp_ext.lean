-- Prove2me | solution 1 for GlobalTheory.ThetaBaseChange.cmp_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:08:40.017604+00:00
-- url     : https://prove2.me/submissions/309c246d-0660-4ed8-8760-12745a6d390c

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
theorem _root_.solution {A : Over S} {A' : Over S'} {Φ : A'.left ⟶ A.left} (hp : IsPullback Φ A'.hom A.hom g)
    {Z : Scheme.{0}} {a b : Z ⟶ (Over.mk t' ⊗ A').left}
    (h₁ : a ≫ (fst (Over.mk t') A').left = b ≫ (fst (Over.mk t') A').left)
    (h₂ : a ≫ (snd (Over.mk t') A').left ≫ Φ = b ≫ (snd (Over.mk t') A').left ≫ Φ) : a = b := by
  have hs : a ≫ (snd (Over.mk t') A').left = b ≫ (snd (Over.mk t') A').left := by
    apply hp.hom_ext
    · simpa only [Category.assoc] using h₂
    · calc (a ≫ (snd (Over.mk t') A').left) ≫ A'.hom
          = a ≫ (fst (Over.mk t') A').left ≫ (Over.mk t').hom := by
            rw [Category.assoc, Over.w, Over.w]
        _ = (b ≫ (fst (Over.mk t') A').left) ≫ (Over.mk t').hom := by rw [← Category.assoc, h₁]
        _ = (b ≫ (snd (Over.mk t') A').left) ≫ A'.hom := by
            rw [Category.assoc, Category.assoc, Over.w, Over.w]
  have hb : b ≫ (Over.mk t' ⊗ A').hom = a ≫ (Over.mk t' ⊗ A').hom := by
    rw [← Over.w (fst (Over.mk t') A'), ← Category.assoc, ← Category.assoc, h₁]
  let U : Over S' := Over.mk (a ≫ (Over.mk t' ⊗ A').hom)
  let fa : U ⟶ Over.mk t' ⊗ A' := Over.homMk a rfl
  let fb : U ⟶ Over.mk t' ⊗ A' := Over.homMk b hb
  have hab : fa = fb := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      simpa only [Over.comp_left, Over.homMk_left, fa, fb] using h₁
    · apply Over.OverMorphism.ext
      simpa only [Over.comp_left, Over.homMk_left, fa, fb] using hs
  exact congrArg (fun f => f.left) hab
end GlobalTheory.ThetaBaseChange
