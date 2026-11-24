-- Prove2me | solution 1 for GlobalTheory.RapidFourier.norm_linForm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:34.491803+00:00
-- url     : https://prove2.me/submissions/d4fd4534-362a-40e0-95f3-c0d36baf62e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid
import Theorems.Thm_GlobalTheory_RapidFourier_linForm_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory
open GlobalTheory.RapidFourier
namespace GlobalTheory.RapidFourier
theorem _root_.solution {n : ℕ} (ν : Fin n → ℤ) : ‖linForm ν‖ ≤ ∑ k, |(ν k : ℝ)| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun k _ => abs_nonneg _) fun x => ?_
  calc ‖linForm ν x‖ = |∑ k, (ν k : ℝ) * x k| := by rw [linForm_apply, Real.norm_eq_abs]
    _ ≤ ∑ k, |(ν k : ℝ) * x k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, |(ν k : ℝ)| * ‖x‖ := Finset.sum_le_sum fun k _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x k)
          (abs_nonneg _)
    _ = (∑ k, |(ν k : ℝ)|) * ‖x‖ := by rw [Finset.sum_mul]
end GlobalTheory.RapidFourier
