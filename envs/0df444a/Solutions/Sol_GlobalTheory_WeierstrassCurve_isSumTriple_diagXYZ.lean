-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.isSumTriple_diagXYZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:19:55.143929+00:00
-- url     : https://prove2.me/submissions/ef59aba8-5a1c-4538-9c1c-c0a80124e393

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsStandardSmoothOfRelativeDimensionAwayJacobian
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IrrelevantLeMapLinearGradedMap
import Theorems.Thm_GlobalTheory_AddLaw_proportional_diagXYZ_addXYZ


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
open AddLaw
variable {A B : Type*} [CommRing A] [CommRing B]
variable {V : WeierstrassCurve A} {P Q T : Fin 3 → A}
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution (hP : V.toProjective.Equation P) (hQ : V.toProjective.Equation Q) :
    IsSumTriple V P Q (diagXYZ V.toProjective P Q) :=
  ⟨proportional_diagXYZ_addXYZ hP hQ, fun _ _ => mul_comm _ _⟩
end GlobalTheory.WeierstrassCurve
