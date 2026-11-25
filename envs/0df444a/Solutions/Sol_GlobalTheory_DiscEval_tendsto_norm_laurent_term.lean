-- Prove2me | solution 1 for GlobalTheory.DiscEval.tendsto_norm_laurent_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:43:07.734804+00:00
-- url     : https://prove2.me/submissions/f08554d1-db97-4262-84f9-8c5e2d6d0e27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Theorems.Thm_GlobalTheory_DiscEval_hasSum_laurent
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_C
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_X



set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscEval
open Filter Topology IsLocalRing
open scoped PowerSeries LaurentSeries
variable {K : Type*} {O : Type*} [CommRing O] (π : O)
  (A : Type*) [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]
variable [NormedField K] [CompleteSpace K] (i : O →+* K) (hi : ∀ x, ‖i x‖ ≤ 1) (hπ : i π ≠ 0)
  {t : K} (ht0 : t ≠ 0) (ht : ‖t‖ < 1)
variable {π A}
include hi ht0 ht
namespace GlobalTheory.DiscEval
theorem _root_.solution (f : A) :
    Tendsto (fun n : ℤ => ‖(laurent π A i hπ f).coeff n * t ^ n‖) cofinite (𝓝 0) := by
  simpa using (hasSum_laurent i hi hπ ht0 ht f).summable.tendsto_cofinite_zero.norm
end GlobalTheory.DiscEval
