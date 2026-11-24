-- Prove2me | solution 1 for GlobalTheory.GrpTangent.smooth_of_tangentMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:09:36.825467+00:00
-- url     : https://prove2.me/submissions/08bf89b5-0068-4754-ab81-d65ecc742a30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Theorems.Thm_GlobalTheory_TangentCrit_smooth_of_tangent
import Theorems.Thm_GlobalTheory_GrpTangent_epsZeroAt_epsBaseAt
import Theorems.Thm_GlobalTheory_GrpTangent_exists_lift_of_tangentMap_surjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [reassoc] GlobalTheory.GrpTangent.epsZeroAt_epsBaseAt

set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.GrpTangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR epsScaleR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (mulN torsion IsAbelianScheme)
open scoped CategoryTheory.Obj
open TangentCrit
variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H]
namespace GlobalTheory.GrpTangent
theorem _root_.solution (f : G ⟶ H) [IsMonHom f] [Smooth G.hom]
    [LocallyOfFiniteType H.hom]
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : Sp k ⟶ S),
      Function.Surjective (tangentMap ((Over.pullback p).map f))) :
    Smooth f.left := by
  have : Smooth (f.left ≫ H.hom) := by rw [Over.w]; infer_instance
  refine smooth_of_tangent f.left H.hom fun k _ _ x v h₁ h₂ => ?_
  let p : Sp k ⟶ S := x ≫ f.left ≫ H.hom
  obtain ⟨w, hw₁, hw₂⟩ := exists_lift_of_tangentMap_surjective p f (h k p)
    (Over.homMk x (by simp [p])) (Over.homMk v h₂) (Over.OverMorphism.ext h₁)
  exact ⟨w.left, congrArg Over.Hom.left hw₁, congrArg Over.Hom.left hw₂⟩
end GlobalTheory.GrpTangent
