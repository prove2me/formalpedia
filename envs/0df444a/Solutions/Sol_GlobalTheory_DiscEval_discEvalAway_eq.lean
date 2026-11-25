-- Prove2me | solution 1 for GlobalTheory.DiscEval.discEvalAway_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:02:53.551959+00:00
-- url     : https://prove2.me/submissions/59516d26-fda1-4850-bb99-e10dfa6b7593

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
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
namespace GlobalTheory.DiscEval
theorem _root_.solution {f : A} {a b : ℕ} {f₀ : O⟦X⟧}
    (h : f * algebraMap O⟦X⟧ A (PowerSeries.C π ^ a * PowerSeries.X ^ b) = algebraMap O⟦X⟧ A f₀) :
    discEvalAway π A i hi hπ ht0 ht f = (i π)⁻¹ ^ a * t⁻¹ ^ b * discEval i hi ht f₀ := by
  have h1 := congrArg (discEvalAway π A i hi hπ ht0 ht) h
  simp only [map_mul, discEvalAway_algebraMap, map_pow, discEval_C, discEval_X] at h1
  rw [← h1, inv_pow, inv_pow]
  field_simp
end GlobalTheory.DiscEval
