-- Prove2me | solution 1 for GlobalTheory.DiscEval.exists_intEmb_eq_discEval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:21:27.273251+00:00
-- url     : https://prove2.me/submissions/e025411e-dd64-4558-92c3-872624f950d3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Theorems.Thm_GlobalTheory_DiscEval_discEval_mem
import Theorems.Thm_GlobalTheory_DiscEval_isClosed_fieldRange

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
variable {O : Type*} [CommRing O] [Algebra ℤ_[p] O] (i : O →+* ℂ_[p]) (hi : ∀ x, ‖i x‖ ≤ 1)
variable [Module.Finite ℤ_[p] O]
include hi
variable (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L]
omit [Module.Finite ℤ_[p] O] [Algebra ℤ_[p] O]
namespace GlobalTheory.DiscEval
theorem _root_.solution (hiL : ∀ x, i x ∈ (fieldEmb L).fieldRange) {t : ℂ_[p]}
    (htL : t ∈ (fieldEmb L).fieldRange) (ht : ‖t‖ < 1) :
    ∃ ev : O⟦X⟧ →+* integralClosure ℤ_[p] L, ∀ f, intEmb L (ev f) = discEval i hi ht f :=
  exists_comp_eq_of_mem_range _ (intEmb_injective L) _ fun f =>
    (mem_range_intEmb_iff L _).2 ⟨discEval_mem i hi ht (B := (fieldEmb L).fieldRange.toSubring)
      (isClosed_fieldRange L) hiL htL f, norm_discEval_le_one i hi ht f⟩
end GlobalTheory.DiscEval
