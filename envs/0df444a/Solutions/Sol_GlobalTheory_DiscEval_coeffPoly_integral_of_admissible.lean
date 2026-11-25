-- Prove2me | solution 1 for GlobalTheory.DiscEval.coeffPoly_integral_of_admissible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:16:15.447634+00:00
-- url     : https://prove2.me/submissions/c8a5bfc2-d8e3-49aa-be36-7aa55bf0b6a5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Theorems.Thm_GlobalTheory_DiscEval_exists_coeffPoly_eq_zero
import Theorems.Thm_GlobalTheory_DiscEval_hasSum_coeffPoly
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_finCore_holds
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
open MvPolynomial
variable {O : Type*} [CommRing O] {π : O}
  {A : Type*} [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]
variable {K : Type} [NormedField K] [IsUltrametricDist K]
variable [CompleteSpace K]
namespace GlobalTheory.DiscEval
theorem _root_.solution (K₀ : Subfield K)
    (hres : ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (K₀ : Set K)) (S : Set K)
    (hS : ∀ t ∈ S, 0 < ‖t‖ ∧ ‖t‖ < 1)
    (hdense : ∀ r : ℝ, 0 < r → r < 1 → ∀ ε > (0 : ℝ), ∃ t ∈ S, |‖t‖ - r| < ε)
    (hrot : ∀ t ∈ S, ∀ τ ∈ K₀, ‖τ‖ = 1 → t * τ ∈ S)
    (i : O →+* K) (hi : ∀ x, ‖i x‖ ≤ 1) (hπ : i π ≠ 0) {σ : Type} [Fintype σ]
    (δ : MvPolynomial σ K) (hδ : ∀ μ, ‖coeff μ δ‖ ≤ 1) (hδ1 : ∃ μ, ‖coeff μ δ‖ = 1)
    (F : MvPolynomial σ A)
    (hF : ∀ t ∈ S, ∀ (ht0 : t ≠ 0) (ht : ‖t‖ < 1) (x : σ → K), (∀ k, x k ∈ K₀ ∧ ‖x k‖ ≤ 1) →
      ‖eval x δ‖ = 1 → ‖eval₂ (discEvalAway π A i hi hπ ht0 ht) x F‖ ≤ 1) (m : ℤ) :
    (∀ μ, ‖coeff μ (coeffPoly m (map (laurent π A i hπ) F))‖ ≤ 1) ∧
      (m < 0 → coeffPoly m (map (laurent π A i hπ) F) = 0) := by
  obtain ⟨b, hb⟩ := exists_coeffPoly_eq_zero (map (laurent π A i hπ) F)
  refine ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.finCore_holds K K₀ hres S hS hdense hrot σ δ hδ hδ1 _ b hb
    (fun t htS x hx hxδ => ?_) m
  have ht0 := norm_pos_iff.1 (hS t htS).1
  have h := hasSum_coeffPoly i hi hπ ht0 (hS t htS).2 F x
  refine ⟨by simpa using h.summable.tendsto_cofinite_zero.norm, ?_⟩
  rw [h.tsum_eq]
  exact hF t htS ht0 _ x hx hxδ
end GlobalTheory.DiscEval
