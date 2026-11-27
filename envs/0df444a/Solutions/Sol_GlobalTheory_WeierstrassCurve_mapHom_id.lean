-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.mapHom_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:35:37.997587+00:00
-- url     : https://prove2.me/submissions/e87faa46-917a-4cb6-b894-ccd26f5081d1

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
theorem _root_.solution : mapHom W (RingHom.id R) W.map_id = 𝟙 _ := by
  apply scheme_hom_ext
  · rw [chartY, pt_eq_ptHom, ptHom_mapHom, Category.comp_id]
    rfl
  · rw [chartZ, pt_eq_ptHom, ptHom_mapHom, Category.comp_id]
    rfl
end GlobalTheory.WeierstrassCurve
