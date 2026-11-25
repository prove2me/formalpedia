-- Prove2me | solution 1 for GlobalTheory.DiscEval.IsDiscPoint.comp_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:57:59.121797+00:00
-- url     : https://prove2.me/submissions/3cca6b9c-cad7-4827-a716-5c5f77eb8fcc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Theorems.Thm_GlobalTheory_IsPolynomialFunction_comp


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
variable {i hi hπ A}
namespace GlobalTheory.DiscEval
namespace IsDiscPoint
theorem _root_.solution {L : IntermediateField ℚ_[p] (PadicAlgCl p)} {t : ℂ_[p]}
    {ht0 : t ≠ 0} {ht : ‖t‖ < 1} {ev : O⟦X⟧ →+* integralClosure ℤ_[p] L} {evA : A →+* L}
    (h : IsDiscPoint i hi hπ A L ht0 ht ev evA) :
    evA.comp (algebraMap O⟦X⟧ A) = (algebraMap (integralClosure ℤ_[p] L) L).comp ev :=
  RingHom.ext fun f => (fieldEmb L).injective (by
    rw [RingHom.comp_apply, h.2, discEvalAway_algebraMap, ← h.1]
    rfl)
end IsDiscPoint
end GlobalTheory.DiscEval
