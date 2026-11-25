-- Prove2me | solution 1 for GlobalTheory.DiscEval.exists_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:03:16.890807+00:00
-- url     : https://prove2.me/submissions/ffca732c-9c38-433b-9856-b838a91d4e16

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
variable {K : Type*} {O : Type*} [CommRing O] (π : O)
  (A : Type*) [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]
namespace GlobalTheory.DiscEval
theorem _root_.solution (f : A) : ∃ (a b : ℕ) (f₀ : O⟦X⟧),
    f * algebraMap O⟦X⟧ A (PowerSeries.C π ^ a * PowerSeries.X ^ b) = algebraMap O⟦X⟧ A f₀ := by
  obtain ⟨k, f₀, h⟩ := IsLocalization.Away.surj (PowerSeries.C π * PowerSeries.X : O⟦X⟧) f
  exact ⟨k, k, f₀, by rw [← mul_pow, map_pow, h]⟩
end GlobalTheory.DiscEval
