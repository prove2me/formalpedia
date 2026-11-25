-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.isPullback_chartZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:46:45.463257+00:00
-- url     : https://prove2.me/submissions/448f6df7-6c1d-4b7e-954a-31fc6c5f8cb6

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
variable {R' R'' : Type u} [CommRing R'] [CommRing R''] {W' : WeierstrassCurve R'}
  {W'' : WeierstrassCurve R''}
variable (f : R →+* R') (h : W.map f = W')
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution : IsPullback (Spec.map (CommRingCat.ofHom (affineMap W f h)))
    (chartZ W') (chartZ W) (mapHom W f h) :=
  IsOpenImmersion.isPullback _ _ _ _
    (by rw [affineMap, SpecMap_affineEval_chartZ, chartZ, pt_eq_ptHom, ptHom_mapHom])
    (by rw [opensRange_chartZ, opensRange_chartZ, mapHom_preimage_coordOpen])
end GlobalTheory.WeierstrassCurve
