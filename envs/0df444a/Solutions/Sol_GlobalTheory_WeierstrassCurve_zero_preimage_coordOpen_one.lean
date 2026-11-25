-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.zero_preimage_coordOpen_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:41:42.163471+00:00
-- url     : https://prove2.me/submissions/5117f98b-4900-4197-8a83-b77d77d0c003

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
theorem _root_.solution : zero W ⁻¹ᵁ coordOpen W 1 = ⊤ := by
  rw [zero, pt_preimage_coordOpen]
  exact PrimeSpectrum.basicOpen_one
end GlobalTheory.WeierstrassCurve
