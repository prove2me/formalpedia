-- Prove2me | solution 1 for GlobalTheory.pullbackPointEquiv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:41:46.364269+00:00
-- url     : https://prove2.me/submissions/09606e28-d139-4018-809b-ed87f8484f6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
universe u
noncomputable section
open GlobalTheory
variable {S S' : Scheme.{u}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
namespace GlobalTheory
theorem _root_.solution [GrpObj G] (h : IsPullback φ G'.hom G.hom f) {T : Over S'}
    (x y : T ⟶ G') :
    letI := grpObjOfIsPullback h
    pullbackPointEquiv h T (x * y) = pullbackPointEquiv h T x * pullbackPointEquiv h T y := by
  exact ((yonedaGrpObjIsoOfRepresentableBy G' _ (pullbackRepresentableBy h)).hom.app
    (Opposite.op T)).hom.map_mul x y
end GlobalTheory
