-- Prove2me | solution 1 for GlobalTheory.DiscEval.isUnit_algInt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:15:58.105746+00:00
-- url     : https://prove2.me/submissions/2be438a6-27f7-4054-b359-5a2e48881f0e

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
variable (p : ℕ) [Fact p.Prime]
variable {p}
open MvPolynomial
namespace GlobalTheory.DiscEval
theorem _root_.solution (x : algInt p) : IsUnit x ↔ ‖(x : ℂ_[p])‖ = 1 := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := h.exists_right_inv
    have h1 : ‖(x : ℂ_[p])‖ * ‖(y : ℂ_[p])‖ = 1 := by
      rw [← norm_mul, ← Subring.coe_mul, hy, Subring.coe_one, norm_one]
    exact le_antisymm x.2.2 (h1.ge.trans (mul_le_of_le_one_right (norm_nonneg _) y.2.2))
  · intro h
    have h0 : (x : ℂ_[p]) ≠ 0 := norm_pos_iff.1 (h ▸ one_pos)
    exact IsUnit.of_mul_eq_one ⟨(x : ℂ_[p])⁻¹, inv_mem x.2.1, by rw [norm_inv, h, inv_one]⟩
      (Subtype.ext (mul_inv_cancel₀ h0))
end GlobalTheory.DiscEval
