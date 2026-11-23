-- Prove2me | solution 1 for GlobalTheory.GrpDense.pushPt_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:44.171214+00:00
-- url     : https://prove2.me/submissions/9882476f-853d-4077-b7c2-c7c43fe9fde5

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
theorem _root_.solution {i : G ⟶ G} (hi : φ ≫ i.left = (ι[A]).left ≫ φ) {T : Over U} (x : T ⟶ A) :
    pushPt w x ≫ i = pushPt w x⁻¹ := by
  apply Over.OverMorphism.ext
  change (x.left ≫ φ) ≫ i.left = (x⁻¹).left ≫ φ
  rw [Category.assoc, hi, Hom.inv_def, Over.comp_left, Category.assoc]
end GlobalTheory.GrpDense
