-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.mem_grading_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:35:41.786575+00:00
-- url     : https://prove2.me/submissions/169d388c-ebba-430b-a100-fb17d6cf1445

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
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution {n : ℕ} {a : HomRing W} :
    a ∈ grading W n ↔ ∃ p : MvPolynomial (Fin 3) R, p.IsHomogeneous n ∧
      Ideal.Quotient.mk _ p = a := Iff.rfl
end GlobalTheory.WeierstrassCurve
