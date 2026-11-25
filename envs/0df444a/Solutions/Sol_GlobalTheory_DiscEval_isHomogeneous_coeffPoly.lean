-- Prove2me | solution 1 for GlobalTheory.DiscEval.isHomogeneous_coeffPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:03:20.509422+00:00
-- url     : https://prove2.me/submissions/a7038d35-34e9-441d-b6f6-5f5927ca7cbc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscEval
open Filter Topology IsLocalRing
open scoped PowerSeries LaurentSeries
open MvPolynomial
variable {K : Type*} [Field K] {σ τ : Type*}
namespace GlobalTheory.DiscEval
theorem _root_.solution (m : ℤ) {G : MvPolynomial σ K⸨X⸩} {d : ℕ}
    (hG : G.IsHomogeneous d) : (coeffPoly m G).IsHomogeneous d := fun μ hμ =>
  hG fun h => hμ (by rw [coeff_coeffPoly, h, HahnSeries.coeff_zero])
end GlobalTheory.DiscEval
