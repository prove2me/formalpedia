-- Prove2me | solution 1 for GlobalTheory.TangentCrit.SpecMap_fromSpecStalk_closedPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:27:43.722267+00:00
-- url     : https://prove2.me/submissions/b0171b8b-1ccb-4b17-a1ed-3dc89fdf57ad

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.TangentCrit
open AlgebraicGeometry CategoryTheory Limits
universe u
namespace GlobalTheory.TangentCrit
theorem _root_.solution {X : Scheme.{u}} {x : X} {R : CommRingCat.{u}}
    [IsLocalRing R] (φ : X.presheaf.stalk x ⟶ R) [IsLocalHom φ.hom] :
    (Spec.map φ ≫ X.fromSpecStalk x) (IsLocalRing.closedPoint R) = x := by
  exact (Scheme.Hom.comp_apply _ _ _).trans
    ((congrArg (X.fromSpecStalk x) Spec_closedPoint).trans Scheme.fromSpecStalk_closedPoint)
end GlobalTheory.TangentCrit
