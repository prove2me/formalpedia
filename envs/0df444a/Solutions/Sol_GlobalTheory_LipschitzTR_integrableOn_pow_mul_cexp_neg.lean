-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.integrableOn_pow_mul_cexp_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:46.481751+00:00
-- url     : https://prove2.me/submissions/edb7dc62-0ebe-4d1b-a520-0b13b0adf9cc

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
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * Complex.exp (-(r * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := r.re)
    (by have := n.cast_nonneg (α := ℝ); linarith) one_pos hr
  refine h.mono' ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_pow_mul_cexp_neg n r ht]
end GlobalTheory.LipschitzTR
