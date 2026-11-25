-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.chartY_preimage_coordOpen_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:46:38.909872+00:00
-- url     : https://prove2.me/submissions/de6ae686-255d-47a4-84bb-7d06917e83f5

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
theorem _root_.solution :
    chartY W ⁻¹ᵁ coordOpen W 2 = PrimeSpectrum.basicOpen (originW W) :=
  pt_preimage_coordOpen ..
end GlobalTheory.WeierstrassCurve
