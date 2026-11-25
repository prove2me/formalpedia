-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.evalHom_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:46:41.486522+00:00
-- url     : https://prove2.me/submissions/aa1732c1-8595-4afa-b852-3df34efa5f8c

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
variable {A B : Type*} [CommRing A] [CommRing B]
variable (ρ : R →+* A) (P : Fin 3 → A) (h : (W.map ρ).toProjective.Equation P)
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution (p : MvPolynomial (Fin 3) R) :
    evalHom W ρ P h (Ideal.Quotient.mk _ p) = MvPolynomial.eval₂ ρ P p := rfl
end GlobalTheory.WeierstrassCurve
