-- Prove2me | solution 1 for GlobalTheory.Hk.LFam.summable_norm_aChi_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:52.069064+00:00
-- url     : https://prove2.me/submissions/88cd10ea-eae4-4246-b444-87fa6fe3b229

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBounds
import Theorems.Thm_GlobalTheory_Hk_summable_nat_mul_exp_neg
import Theorems.Thm_GlobalTheory_Hk_LFam_norm_aChi_le

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
open GlobalTheory GlobalTheory.Hk
namespace GlobalTheory.Hk
namespace LFam
theorem _root_.solution (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => ‖𝓕.aChi χ n‖ * Real.exp (-(t * n))) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_nat_mul_exp_neg ht).mul_left (14 * 𝓕.B))
  rw [← mul_assoc]
  gcongr
  exact 𝓕.norm_aChi_le χ n
end LFam
end GlobalTheory.Hk
