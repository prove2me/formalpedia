-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.ofAffinePoint_zsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:40:35.013121+00:00
-- url     : https://prove2.me/submissions/7a603604-1121-47f6-ad2a-64d8c36e694c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IrrelevantLeMapLinearGradedMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsLiftAddOfIsReducedEq

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
open GlobalTheory.WeierstrassCurve
open AddLaw
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable [W.IsElliptic]
variable (k : Type u) [Field k] [Algebra R k]
variable [DecidableEq k]
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution (n : ℤ) (p : (W.baseChange k).toAffine.Point) :
    ofAffinePoint W k (n • p) = ofAffinePoint W k p ^ n :=
  map_zpow (affinePointMulEquiv W k) (.ofAdd p) n
end GlobalTheory.WeierstrassCurve
