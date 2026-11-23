-- Prove2me | solution 1 for GlobalTheory.GrpDense.pushPt_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:44.71983+00:00
-- url     : https://prove2.me/submissions/8c2ec177-990a-4d69-8cee-f1acf1f50c96

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GrpDense
variable {Z U : Scheme.{0}} {j : U ⟶ Z}
variable {G : Over Z} {A : Over U} {φ : A.left ⟶ G.left}
variable [GrpObj A] (w : φ ≫ G.hom = A.hom ≫ j)
namespace GlobalTheory.GrpDense
theorem _root_.solution {m : G ⊗ G ⟶ G}
    (hm : ∀ φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ)
    {T : Over U} (x y : T ⟶ A) : lift (pushPt w x) (pushPt w y) ≫ m = pushPt w (x * y) := by
  have hsq : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare φ (lift (pushPt w (fst A A)) (pushPt w (snd A A))).left := by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare
    constructor
    · rw [← Over.comp_left, lift_fst]
      rfl
    · rw [← Over.comp_left, lift_snd]
      rfl
  have key := hm _ hsq
  have hL : lift (pushPt w x) (pushPt w y) =
      Over.homMk (U := Over.mk (T.hom ≫ j)) (V := Over.mk ((A ⊗ A).hom ≫ j)) (lift x y).left
        (by
          show (lift x y).left ≫ ((A ⊗ A).hom ≫ j) = T.hom ≫ j
          rw [← Category.assoc, Over.w]) ≫
        lift (pushPt w (fst A A)) (pushPt w (snd A A)) := by
    apply hom_ext
    · rw [lift_fst, Category.assoc, lift_fst]
      apply Over.OverMorphism.ext
      change x.left ≫ φ = (lift x y).left ≫ (fst A A).left ≫ φ
      rw [← Category.assoc, ← Over.comp_left, lift_fst]
    · rw [lift_snd, Category.assoc, lift_snd]
      apply Over.OverMorphism.ext
      change y.left ≫ φ = (lift x y).left ≫ (snd A A).left ≫ φ
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
  apply Over.OverMorphism.ext
  rw [hL, Over.comp_left, Over.comp_left, Category.assoc, key]
  change (lift x y).left ≫ (μ[A]).left ≫ φ = (x * y).left ≫ φ
  rw [Hom.mul_def, Over.comp_left, Category.assoc]
end GlobalTheory.GrpDense
