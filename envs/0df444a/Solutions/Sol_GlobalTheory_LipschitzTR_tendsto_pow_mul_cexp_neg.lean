-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.tendsto_pow_mul_cexp_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:46:57.132919+00:00
-- url     : https://prove2.me/submissions/55a44f6b-e836-404b-91c8-ee4572a16b59

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierLipschitzOneVariableKernelEq
import Theorems.Thm_GlobalTheory_LipschitzTR_norm_pow_mul_cexp_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.LipschitzTR
open Set Filter Topology
namespace GlobalTheory.LipschitzTR
theorem _root_.solution (n : ℕ) {r : ℂ} (hr : 0 < r.re) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ n * Complex.exp (-(r * t))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) r.re hr
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [norm_pow_mul_cexp_neg n r ht, Real.rpow_one]
end GlobalTheory.LipschitzTR
