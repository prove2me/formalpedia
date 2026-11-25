-- Prove2me | solution 1 for GlobalTheory.DiscEval.hasSum_coeffPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:41:31.765462+00:00
-- url     : https://prove2.me/submissions/cbbcbe94-524c-40ab-b1e8-dbddbe480eee

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
open MvPolynomial
variable {O : Type*} [CommRing O] {π : O}
  {A : Type*} [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]
namespace GlobalTheory.DiscEval
theorem _root_.solution {K : Type*} [NormedField K] [CompleteSpace K] (i : O →+* K)
    (hi : ∀ x, ‖i x‖ ≤ 1) (hπ : i π ≠ 0) {t : K} (ht0 : t ≠ 0) (ht : ‖t‖ < 1) {σ : Type*}
    (F : MvPolynomial σ A) (x : σ → K) :
    HasSum (fun m : ℤ => eval x (coeffPoly m (map (laurent π A i hπ) F)) * t ^ m)
      (eval₂ (discEvalAway π A i hi hπ ht0 ht) x F) := by
  have h : ∀ m : ℤ, coeffPoly m (map (laurent π A i hπ) F) =
      ∑ μ ∈ F.support, monomial μ ((laurent π A i hπ (coeff μ F)).coeff m) := fun m => by
    classical
    ext μ
    simp only [coeff_coeffPoly, coeff_map, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · simp [notMem_support_iff.1 h]
  rw [eval₂_eq]
  refine Eq.mpr (congrArg (HasSum · _) (funext fun m => ?_))
    (hasSum_sum fun μ (_ : μ ∈ F.support) =>
      (hasSum_laurent i hi hπ ht0 ht (coeff μ F)).mul_right (∏ k ∈ μ.support, x k ^ μ k))
  rw [h, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [eval_monomial, Finsupp.prod]
  ring
end GlobalTheory.DiscEval
