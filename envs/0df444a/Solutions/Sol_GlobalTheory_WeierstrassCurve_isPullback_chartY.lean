-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.isPullback_chartY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:46:43.504278+00:00
-- url     : https://prove2.me/submissions/3bff4363-1695-47e6-a628-8843329f24f1

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
theorem _root_.solution : IsPullback (Spec.map (CommRingCat.ofHom (originMap W f h)))
    (chartY W') (chartY W) (mapHom W f h) :=
  IsOpenImmersion.isPullback _ _ _ _
    (by rw [originMap, SpecMap_originEval_chartY, chartY, pt_eq_ptHom, ptHom_mapHom])
    (by rw [opensRange_chartY, opensRange_chartY, mapHom_preimage_coordOpen])
end GlobalTheory.WeierstrassCurve
