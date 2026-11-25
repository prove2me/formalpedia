-- Prove2me | solution 1 for GlobalTheory.DiscEval.hasSum_laurent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:27:22.694802+00:00
-- url     : https://prove2.me/submissions/803cb0b6-244c-4646-a2dd-b9b15e2643a7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Theorems.Thm_GlobalTheory_DiscEval_coeff_laurent
import Theorems.Thm_GlobalTheory_DiscEval_exists_mul_eq
import Theorems.Thm_GlobalTheory_DiscEval_discEvalAway_eq
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
theorem _root_.solution (f : A) :
    HasSum (fun n : ℤ => (laurent π A i hπ f).coeff n * t ^ n)
      (discEvalAway π A i hi hπ ht0 ht f) := by
  obtain ⟨a, b, f₀, h⟩ := exists_mul_eq π A f
  have hinj : Function.Injective fun k : ℕ => (k : ℤ) - b := fun k l hkl => by simpa using hkl
  rw [← hinj.hasSum_iff, discEvalAway_eq i hi hπ ht0 ht h]
  · refine Eq.mpr (congrArg (HasSum · _) (funext fun k => ?_))
      ((hasSum_discEval i hi ht f₀).mul_left ((i π)⁻¹ ^ a * t⁻¹ ^ b))
    rw [Function.comp_apply, coeff_laurent i hπ h, sub_add_cancel, if_neg (by omega), Int.natAbs_natCast,
      zpow_sub₀ ht0, zpow_natCast, zpow_natCast, inv_pow t]
    ring
  · intro n hn
    rw [coeff_laurent i hπ h, if_pos, zero_mul]
    by_contra h0
    exact hn ⟨(n + b).toNat, by simp only; omega⟩
end GlobalTheory.DiscEval
