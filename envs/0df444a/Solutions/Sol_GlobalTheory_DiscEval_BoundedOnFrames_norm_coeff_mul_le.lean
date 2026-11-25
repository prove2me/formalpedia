-- Prove2me | solution 1 for GlobalTheory.DiscEval.BoundedOnFrames.norm_coeff_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:51:08.693469+00:00
-- url     : https://prove2.me/submissions/d6f0ed3d-94f3-4173-8bf6-d039f509f088

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Theorems.Thm_P2M_GlobalTheory_DiscEval_norm_coeff_bind__le_6e00ba114732
import Theorems.Thm_P2M_GlobalTheory_DiscEval_BoundedOnFrames_norm_coeff_bind__le_90ad7e439400
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
    (hd : F.IsHomogeneous d) {κ : ι → Type*} [∀ s, Fintype (κ s)]
    {w : ∀ s, Matrix (n s) (κ s) ℂ_[p]} {c : ℝ} (hc : 0 ≤ c) (hw : ∀ s a b, ‖w s a b‖ ≤ c)
    (μ : EntryIndex κ n →₀ ℕ) (m : ℤ) :
    ‖(coeff μ (bind₁ (fun k => ∑ j, C (HahnSeries.C (w k.1 k.2.1 j)) * X ⟨k.1, j, k.2.2⟩)
        (map (laurent π A i hπ) F))).coeff m‖ ≤ c ^ d ∧
      (m < 0 → (coeff μ (bind₁ (fun k => ∑ j, C (HahnSeries.C (w k.1 k.2.1 j)) * X ⟨k.1, j, k.2.2⟩)
        (map (laurent π A i hπ) F))).coeff m = 0) := by
  classical
  have h : (fun k => ∑ j, C (HahnSeries.C (w k.1 k.2.1 j)) * X ⟨k.1, j, k.2.2⟩ :
      EntryIndex n n → MvPolynomial (EntryIndex κ n) ℂ_[p]⸨X⸩) =
      fun k => map HahnSeries.C (∑ j, C (w k.1 k.2.1 j) * X ⟨k.1, j, k.2.2⟩) := by
    funext k
    simp only [map_sum, map_mul, map_C, map_X]
  rw [h]
  refine hF.norm_coeff_bind₁_le hd hc (fun k ν => ?_) μ m
  rw [coeff_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hc fun j _ => ?_
  rw [coeff_C_mul, coeff_X]
  split_ifs <;> simp [hw, hc]
end BoundedOnFrames
end GlobalTheory.DiscEval
