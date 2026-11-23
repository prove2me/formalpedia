-- Prove2me | solution 1 for GlobalTheory.GrpDense.pushPt_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:34.11487+00:00
-- url     : https://prove2.me/submissions/54cff8d2-44de-4537-91c0-5b1a303d99b6

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
namespace GlobalTheory.GrpDense
theorem _root_.solution (h : IsPullback φ A.hom G.hom j) (T : Over U) (x₀ : Over.mk (T.hom ≫ j) ⟶ G) :
    ∃ x : T ⟶ A, pushPt h.w x = x₀ := by
  refine ⟨Over.homMk (h.lift x₀.left T.hom (by simp)) (h.lift_snd _ _ _), ?_⟩
  apply Over.OverMorphism.ext
  exact h.lift_fst _ _ _
end GlobalTheory.GrpDense
