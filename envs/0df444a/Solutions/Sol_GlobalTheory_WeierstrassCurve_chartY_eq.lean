-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.chartY_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:36:32.693521+00:00
-- url     : https://prove2.me/submissions/f1227307-3ddc-4d27-947c-11ace3a7c45c

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
theorem _root_.solution : chartY W = Spec.map (CommRingCat.ofHom
    (awayEquivOrigin W : AwayRing W 1 →+* OriginRing W)) ≫ awayChart W 1 :=
  ptHom_eq_awayChart W 1 _ _ (isUnimodularSol_origin (equation_originZ_originW W)) isUnit_one.neg
end GlobalTheory.WeierstrassCurve
