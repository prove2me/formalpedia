-- Prove2me | solution 1 for GlobalTheory.Hk.LogDeriv.norm_lamChi_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:15.663524+00:00
-- url     : https://prove2.me/submissions/70ebf9f2-6011-4efe-b812-1e4bf1398303

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LogDeriv
open LSeries
open scoped LSeries.notation
variable (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ)
namespace GlobalTheory.Hk.LogDeriv
theorem _root_.solution (n : ℕ) : ‖𝓕.lamChi χ n‖ ≤ 2 * Λ n := by
  show ‖∑ g, χ g * (𝓕.lam g n : ℂ)‖ ≤ 2 * Λ n
  calc ‖∑ g, χ g * (𝓕.lam g n : ℂ)‖ ≤ ∑ g, ‖χ g * (𝓕.lam g n : ℂ)‖ := norm_sum_le _ _
    _ = ∑ g, 𝓕.lam g n := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [norm_mul, AddChar.norm_apply, one_mul, Complex.norm_of_nonneg (𝓕.lam_nonneg g n)]
    _ ≤ 2 * Λ n := 𝓕.lam_le n
end GlobalTheory.Hk.LogDeriv
