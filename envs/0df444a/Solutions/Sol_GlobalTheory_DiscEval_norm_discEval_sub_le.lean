-- Prove2me | solution 1 for GlobalTheory.DiscEval.norm_discEval_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:00:45.355253+00:00
-- url     : https://prove2.me/submissions/a03655d1-c5bd-42f4-ae31-8833666b0919

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
variable {K : Type*} [NormedField K] [CompleteSpace K] {O : Type*} [CommRing O]
  (i : O →+* K) (hi : ∀ x, ‖i x‖ ≤ 1) {t : K} (ht : ‖t‖ < 1)
namespace GlobalTheory.DiscEval
theorem _root_.solution [IsUltrametricDist K] (f : O⟦X⟧) :
    ‖discEval i hi ht f - i (PowerSeries.constantCoeff f)‖ ≤ ‖t‖ := by
  have h := congrArg (discEval i hi ht) (PowerSeries.eq_X_mul_shift_add_const f)
  rw [map_add, map_mul, discEval_X, discEval_C] at h
  rw [h, add_sub_cancel_right, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_discEval_le_one i hi ht _)
end GlobalTheory.DiscEval
