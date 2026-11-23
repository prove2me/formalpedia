-- Prove2me | solution 1 for GlobalTheory.GrpDense.pushPt_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:53.209032+00:00
-- url     : https://prove2.me/submissions/89eba52f-ceee-4ac1-8d3c-9ccc19a657de

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
theorem _root_.solution {e : 𝟙_ (Over Z) ⟶ G} (he : j ≫ e.left = (η[A]).left ≫ φ) (T : Over U) :
    toUnit _ ≫ e = pushPt w (1 : T ⟶ A) := by
  apply Over.OverMorphism.ext
  change (toUnit (Over.mk (T.hom ≫ j))).left ≫ e.left = (1 : T ⟶ A).left ≫ φ
  rw [Hom.one_def, Over.comp_left, Category.assoc, ← he]
  have h1 : (toUnit (Over.mk (T.hom ≫ j))).left = T.hom ≫ j := by
    simp
  have h2 : (toUnit T).left = T.hom := by
    simp
  rw [h1, h2, Category.assoc]
end GlobalTheory.GrpDense
