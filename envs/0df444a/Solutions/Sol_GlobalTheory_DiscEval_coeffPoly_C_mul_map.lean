-- Prove2me | solution 1 for GlobalTheory.DiscEval.coeffPoly_C_mul_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:59:08.35989+00:00
-- url     : https://prove2.me/submissions/e673bade-4f90-4418-a671-715f2b8497d7

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
theorem _root_.solution (m : ℤ) (c : K⸨X⸩) (Q : MvPolynomial σ K) :
    coeffPoly m (C c * map (HahnSeries.C : K →+* K⸨X⸩) Q) = C (c.coeff m) * Q := by
  ext μ
  rw [coeff_coeffPoly, coeff_C_mul, coeff_C_mul, coeff_map, HahnSeries.C_apply,
    HahnSeries.coeff_mul_single_zero]
end GlobalTheory.DiscEval
