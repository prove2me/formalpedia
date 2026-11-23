-- Prove2me | solution 1 for GlobalTheory.Hk.LogDerivHalf.norm_lamChi_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:14.117806+00:00
-- url     : https://prove2.me/submissions/169a6206-ece4-4251-9f40-d1175047c852

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionLogDerivLocalFormulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivSubExceptionalLe

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
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LogDerivHalf
namespace GlobalTheory.Hk.LogDerivHalf
theorem _root_.solution (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (n : ℕ) : ‖𝓕.lamChi χ n‖ ≤ 2 * Λ n := by
  unfold LFam.lamChi
  calc ‖∑ g, χ g * (𝓕.lam g n : ℂ)‖ ≤ ∑ g, ‖χ g * (𝓕.lam g n : ℂ)‖ := norm_sum_le _ _
    _ = ∑ g, 𝓕.lam g n := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [norm_mul, AddChar.norm_apply, one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (𝓕.lam_nonneg g n)]
    _ ≤ 2 * Λ n := 𝓕.lam_le n
end GlobalTheory.Hk.LogDerivHalf
