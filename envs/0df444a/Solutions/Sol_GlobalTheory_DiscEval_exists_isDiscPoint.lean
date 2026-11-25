-- Prove2me | solution 1 for GlobalTheory.DiscEval.exists_isDiscPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:36:51.11486+00:00
-- url     : https://prove2.me/submissions/d84e5824-58b4-4f22-9e44-4e43a13803f7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Theorems.Thm_GlobalTheory_DiscEval_discEvalAway_mem
import Theorems.Thm_GlobalTheory_DiscEval_isClosed_fieldRange
import Theorems.Thm_GlobalTheory_DiscEval_exists_intEmb_eq_discEval

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
variable (p : ℕ) [Fact p.Prime]
variable {p}
variable {O : Type*} [CommRing O] (i : O →+* ℂ_[p]) (hi : ∀ x, ‖i x‖ ≤ 1) {π : O} (hπ : i π ≠ 0)
  (A : Type*) [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]
namespace GlobalTheory.DiscEval
theorem _root_.solution (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L]
    (hiL : ∀ x, i x ∈ (fieldEmb L).fieldRange) {t : ℂ_[p]} (htL : t ∈ (fieldEmb L).fieldRange)
    (ht0 : t ≠ 0) (ht : ‖t‖ < 1) : ∃ ev evA, IsDiscPoint i hi hπ A L ht0 ht ev evA := by
  obtain ⟨ev, hev⟩ := exists_intEmb_eq_discEval i hi L hiL htL ht
  obtain ⟨evA, hevA⟩ := exists_comp_eq_of_mem_range _ (fieldEmb L).injective
    (discEvalAway π A i hi hπ ht0 ht)
    fun f => discEvalAway_mem i hi hπ ht0 ht (isClosed_fieldRange L) hiL htL f
  exact ⟨ev, evA, hev, hevA⟩
end GlobalTheory.DiscEval
