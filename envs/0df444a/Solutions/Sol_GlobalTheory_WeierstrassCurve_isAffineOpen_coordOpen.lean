-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.isAffineOpen_coordOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:18:56.187633+00:00
-- url     : https://prove2.me/submissions/db2682e2-6b33-4a3e-8e9d-0353a0e3fa2d

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
variable (i : Fin 3)
variable {A : Type u} [CommRing A]
variable (ρ : R →+* A) (P : Fin 3 → A)
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution : IsAffineOpen (coordOpen W i) :=
  Proj.isAffineOpen_basicOpen _ _ (coord_mem W i) one_pos
end GlobalTheory.WeierstrassCurve
