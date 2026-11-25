-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.pt_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:41:40.82466+00:00
-- url     : https://prove2.me/submissions/c08b1bce-e2a5-449d-8f39-b682543ad9e1

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
variable {A B : Type u} [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable (P : Fin 3 → A) (h : IsUnimodularSol (W.baseChange A) P)
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution {P' : Fin 3 → A} (hP : P = P') (h' : IsUnimodularSol (W.baseChange A) P') :
    pt W P h = pt W P' h' := by
  subst hP
  rfl
end GlobalTheory.WeierstrassCurve
