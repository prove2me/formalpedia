-- Prove2me | solution 1 for GlobalTheory.AbLaw.CubeGen.prod_face
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:53:01.054878+00:00
-- url     : https://prove2.me/submissions/17b40045-5e9d-4ae7-9f99-91ce2b5c8a9d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivPullCompIff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeGen
variable {S : Scheme.{0}} (A : Over S) [GrpObj A]
variable {A}
namespace GlobalTheory.AbLaw.CubeGen
theorem _root_.solution [IsCommMonObj A] {Z : Scheme.{0}} (r : Z ⟶ (G3 A).left) (i : Fin 3) (b : Z ⟶ S)
    (h : r ≫ (x3 A i).left = b ≫ η[A].left) (U : Type) [CommGroup U] (k : (Z ⟶ A.left) → U) :
    ∏ I, k (r ≫ thφ A (x3 A) I) ^ thε I = 1 := by
  let T : Over S := Over.mk (r ≫ (G3 A).hom)
  let x : T ⟶ G3 A := Over.homMk r rfl
  have hb : b = r ≫ (G3 A).hom := by
    have := congrArg (· ≫ A.hom) h
    simp only [Category.assoc, Over.w] at this
    exact (this.trans (Category.comp_id _)).symm
  have hi : x ≫ x3 A i = 1 := by
    apply Over.OverMorphism.ext
    rw [Hom.one_def]
    exact h.trans (by rw [hb]; rfl)
  have hx : lift (x ≫ x3 A 0) (lift (x ≫ x3 A 1) (x ≫ x3 A 2)) = x := by ext <;> simp [x3]
  have := prod_cub (x ≫ x3 A 0) (x ≫ x3 A 1) (x ≫ x3 A 2) (U := U) k
  rw [hx] at this
  refine this.trans ?_
  fin_cases i
  · rw [show x ≫ x3 A 0 = 1 from hi]
    simp only [_root_.one_mul]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel
  · rw [show x ≫ x3 A 1 = 1 from hi]
    simp only [_root_.one_mul, _root_.mul_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel
  · rw [show x ≫ x3 A 2 = 1 from hi]
    simp only [_root_.mul_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel
end GlobalTheory.AbLaw.CubeGen
