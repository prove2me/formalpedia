-- Prove2me | solution 1 for GlobalTheory.DiscEval.discEval_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:03:06.144552+00:00
-- url     : https://prove2.me/submissions/7d7a3044-4a61-47c4-8c91-37cd67217270

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
theorem _root_.solution {B : Subring K} (hB : IsClosed (B : Set K)) (hiB : ∀ x, i x ∈ B)
    (htB : t ∈ B) (f : O⟦X⟧) : discEval i hi ht f ∈ B :=
  hB.mem_of_tendsto (hasSum_discEval i hi ht f) (Eventually.of_forall fun _ =>
    B.sum_mem fun _ _ => B.mul_mem (hiB _) (B.pow_mem htB _))
end GlobalTheory.DiscEval
