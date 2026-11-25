-- Prove2me | solution 1 for GlobalTheory.DiscEval.BoundedOnFrames.norm_coeff_linear_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:39:02.983401+00:00
-- url     : https://prove2.me/submissions/76b2cb24-e65f-4ad3-af9e-f5748b5b47ad

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Theorems.Thm_P2M_GlobalTheory_DiscEval_coeffPoly_bind__ea251764de75
import Theorems.Thm_GlobalTheory_DiscEval_isHomogeneous_coeffPoly
import Theorems.Thm_GlobalTheory_DiscEval_BoundedOnFrames_coeffPoly_integral
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_basisChange_holds
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
open MvPolynomial
variable {O : Type*} [CommRing O] (i : O →+* ℂ_[p]) (hi : ∀ x, ‖i x‖ ≤ 1) {π : O} (hπ : i π ≠ 0)
  {A : Type*} [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]
  {ι : Type} [Fintype ι] {n : ι → Type} [∀ s, Fintype (n s)] [∀ s, DecidableEq (n s)]
variable {i hi hπ} {F : MvPolynomial (EntryIndex n n) A}
namespace GlobalTheory.DiscEval
namespace BoundedOnFrames
theorem _root_.solution (hF : BoundedOnFrames i hi hπ F) {d : ℕ}
    (hd : F.IsHomogeneous d) {B : EntryIndex n n → EntryIndex n n → ℂ_[p]} {c : ℝ}
    (hc : 1 ≤ c) (hB : ∀ k l, ‖B k l‖ ≤ c) (μ : EntryIndex n n →₀ ℕ) (m : ℤ) :
    ‖(coeff μ (bind₁ (fun k => ∑ l, C (HahnSeries.C (B k l)) * X l)
        (map (laurent π A i hπ) F))).coeff m‖ ≤ c ^ d ∧
      (m < 0 → (coeff μ (bind₁ (fun k => ∑ l, C (HahnSeries.C (B k l)) * X l)
        (map (laurent π A i hπ) F))).coeff m = 0) := by
  have h : (fun k => ∑ l, C (HahnSeries.C (B k l)) * X l :
      EntryIndex n n → MvPolynomial (EntryIndex n n) ℂ_[p]⸨X⸩) =
      fun k => map HahnSeries.C (∑ l, C (B k l) * X l) := by
    funext k
    simp only [map_sum, map_mul, map_C, map_X]
  rw [h, ← coeff_coeffPoly, coeffPoly_bind₁]
  exact ⟨ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.basisChange_holds _ _ _ d (isHomogeneous_coeffPoly m (hd.map _))
    (hF.coeffPoly_integral m).1 B c hc hB μ, fun hm => by simp [(hF.coeffPoly_integral m).2 hm]⟩
end BoundedOnFrames
end GlobalTheory.DiscEval
