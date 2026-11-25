-- Prove2me | solution 1 for GlobalTheory.DiscEval.coeff_laurent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:58:01.018775+00:00
-- url     : https://prove2.me/submissions/45027d25-a8f7-4d5c-a388-821097ba29a0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
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
variable [Field K] (i : O →+* K) (hπ : i π ≠ 0)
variable {π A}
namespace GlobalTheory.DiscEval
theorem _root_.solution {f : A} {a b : ℕ} {f₀ : O⟦X⟧}
    (h : f * algebraMap O⟦X⟧ A (PowerSeries.C π ^ a * PowerSeries.X ^ b) = algebraMap O⟦X⟧ A f₀)
    (n : ℤ) : (laurent π A i hπ f).coeff n =
      if n + b < 0 then 0 else (i π)⁻¹ ^ a * i (PowerSeries.coeff (n + b).natAbs f₀) := by
  have h1 := congrArg (laurent π A i hπ) h
  rw [map_mul, laurent_algebraMap, laurent_algebraMap] at h1
  have h2 : HahnSeries.ofPowerSeries ℤ K (PowerSeries.map i
      (PowerSeries.C π ^ a * PowerSeries.X ^ b)) = HahnSeries.single (b : ℤ) (i π ^ a) := by
    rw [map_mul, map_pow, map_pow, PowerSeries.map_C, PowerSeries.map_X,
      ← map_pow PowerSeries.C, map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X_pow,
      HahnSeries.C_apply, HahnSeries.single_mul_single]
    simp
  have h3 := congrArg (fun g : K⸨X⸩ => g.coeff (n + b)) h1
  simp only [h2, HahnSeries.coeff_mul_single_add] at h3
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_map] at h3
  have h4 : i π ^ a ≠ 0 := pow_ne_zero _ hπ
  split_ifs at h3 ⊢
  · exact (mul_eq_zero.1 h3).resolve_right h4
  · rw [← h3, inv_pow]
    field_simp
end GlobalTheory.DiscEval
