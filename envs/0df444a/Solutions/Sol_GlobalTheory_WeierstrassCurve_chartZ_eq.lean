-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.chartZ_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:36:36.513244+00:00
-- url     : https://prove2.me/submissions/319e8a6d-d8bb-4af3-b16e-33a4c54b4da9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_AwayLiftCompFromZeroRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousIdeal Limits
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.WeierstrassCurve
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
open Polynomial
open scoped Polynomial.Bivariate
variable {A : Type*} [CommRing A]
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution : chartZ W = Spec.map (CommRingCat.ofHom
    (awayEquivAffine W : AwayRing W 2 →+* W.toAffine.CoordinateRing)) ≫ awayChart W 2 :=
  ptHom_eq_awayChart W 2 _ _ (isUnimodularSol_some (equation_affineX_affineY W)) isUnit_one
end GlobalTheory.WeierstrassCurve
