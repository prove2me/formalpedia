-- Prove2me | solution 1 for GlobalTheory.ThetaBaseChange.translPt_cmp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:04:51.875836+00:00
-- url     : https://prove2.me/submissions/fd49a2ad-f0a3-4888-bb59-297a34ff1a6a

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
variable {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {Φ : A'.left ⟶ A.left}
namespace GlobalTheory.ThetaBaseChange
theorem _root_.solution (ht : t' ≫ g = t) (hp : IsGrpPullback A' A g Φ) {x : Over.mk t ⟶ A} {x' : Over.mk t' ⟶ A'}
    (hx : x'.left ≫ Φ = x.left) {ω : (Over.mk t ⊗ A).left ⟶ (Over.mk t' ⊗ A').left}
    (h₁ : ω ≫ (fst (Over.mk t') A').left = (fst (Over.mk t) A).left)
    (h₂ : ω ≫ (snd (Over.mk t') A').left ≫ Φ = (snd (Over.mk t) A).left) :
    ω ≫ (translPt A' x').left ≫ Φ = (translPt A x).left := by
  subst ht
  unfold translPt
  change ω ≫ ((fst (Over.mk t') A' ≫ x') * snd (Over.mk t') A').left ≫ Φ =
    ((fst (Over.mk (t' ≫ g)) A ≫ x) * snd (Over.mk (t' ≫ g)) A).left
  have he : ω ≫ (Over.mk t' ⊗ A').hom ≫ g = (Over.mk (t' ≫ g) ⊗ A).hom := by
    rw [← Over.w (fst (Over.mk t') A'), ← Over.w (fst (Over.mk (t' ≫ g)) A), ← h₁]
    simp only [Over.mk_hom, Category.assoc]
  let V : Over S := Over.mk ((Over.mk t' ⊗ A').hom ≫ g)
  let e : Over.mk (t' ≫ g) ⊗ A ⟶ V := Over.homMk ω he
  let x₀ : V ⟶ A := Over.homMk ((fst (Over.mk t') A' ≫ x').left ≫ Φ) (by
    show ((fst (Over.mk t') A' ≫ x').left ≫ Φ) ≫ A.hom = (Over.mk t' ⊗ A').hom ≫ g
    rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w])
  let y₀ : V ⟶ A := Over.homMk ((snd (Over.mk t') A').left ≫ Φ) (by
    show ((snd (Over.mk t') A').left ≫ Φ) ≫ A.hom = (Over.mk t' ⊗ A').hom ≫ g
    rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w])
  have hm := hp.2 (Over.mk t' ⊗ A') (fst (Over.mk t') A' ≫ x') (snd (Over.mk t') A') x₀ y₀ rfl rfl
  rw [← hm]
  have h1 : e ≫ x₀ = fst (Over.mk (t' ≫ g)) A ≫ x := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.homMk_left, Category.assoc, hx, e, x₀]
    rw [← Category.assoc, h₁]
  have h2 : e ≫ y₀ = snd (Over.mk (t' ≫ g)) A := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.homMk_left, e, y₀]
    exact h₂
  have h3 : e ≫ (x₀ * y₀) = (fst (Over.mk (t' ≫ g)) A ≫ x) * snd (Over.mk (t' ≫ g)) A := by
    rw [← h1, ← h2]
    show e ≫ (lift x₀ y₀ ≫ μ) = lift (e ≫ x₀) (e ≫ y₀) ≫ μ
    rw [← Category.assoc, comp_lift]
  exact congrArg (fun f => f.left) h3
end GlobalTheory.ThetaBaseChange
