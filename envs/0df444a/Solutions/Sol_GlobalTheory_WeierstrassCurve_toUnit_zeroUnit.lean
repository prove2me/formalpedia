-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.toUnit_zeroUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:55:24.372976+00:00
-- url     : https://prove2.me/submissions/4bdd49b2-72a7-4dd6-b86f-f654dcf50fff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsStandardSmoothOfRelativeDimensionAwayJacobian
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IrrelevantLeMapLinearGradedMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open HomogeneousIdeal
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.WeierstrassCurve
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable {A : Type*} [CommRing A]
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution (A : Type u) [CommRing A] [Algebra R A] :
    toUnit (specOver R A) ≫ zeroUnit W = zeroOver W A := rfl
end GlobalTheory.WeierstrassCurve
