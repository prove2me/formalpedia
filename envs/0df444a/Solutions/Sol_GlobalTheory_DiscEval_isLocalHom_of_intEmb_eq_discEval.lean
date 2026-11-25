-- Prove2me | solution 1 for GlobalTheory.DiscEval.isLocalHom_of_intEmb_eq_discEval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:12:22.763354+00:00
-- url     : https://prove2.me/submissions/c0655ff9-314c-4bdc-8035-79e8980fd2a7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Theorems.Thm_GlobalTheory_DiscEval_norm_discEval_sub_le
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
import Theorems.Thm_GlobalTheory_IsPolynomialFunction_comp
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
variable (p : ℕ) [Fact p.Prime]
variable {p}
variable {O : Type*} [CommRing O] [Algebra ℤ_[p] O] (i : O →+* ℂ_[p]) (hi : ∀ x, ‖i x‖ ≤ 1)
variable [Module.Finite ℤ_[p] O]
include hi
variable (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L]
omit [Module.Finite ℤ_[p] O]
namespace GlobalTheory.DiscEval
theorem _root_.solution (hinj : Function.Injective i) {t : ℂ_[p]} (ht : ‖t‖ < 1)
    {ev : O⟦X⟧ →+* integralClosure ℤ_[p] L} (hev : ∀ f, intEmb L (ev f) = discEval i hi ht f) :
    IsLocalHom ev := by
  have hj : ∀ a, intEmb L (ev.comp PowerSeries.C a) = i a := fun a => by simp [hev]
  have := isLocalHom_of_intEmb_eq i hi L hinj hj
  refine ⟨fun f hf => PowerSeries.isUnit_iff_constantCoeff.2 ?_⟩
  rw [← isUnit_map_iff (ev.comp PowerSeries.C), isUnit_iff_norm, hj]
  rw [isUnit_iff_norm, hev] at hf
  refine le_antisymm (hi _) (not_lt.1 fun h => hf.not_lt ?_)
  rw [← sub_add_cancel (discEval i hi ht f) (i (PowerSeries.constantCoeff f))]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
    (max_lt ((norm_discEval_sub_le i hi ht f).trans_lt ht) h)
end GlobalTheory.DiscEval
