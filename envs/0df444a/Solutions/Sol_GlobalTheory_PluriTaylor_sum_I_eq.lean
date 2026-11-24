-- Prove2me | solution 1 for GlobalTheory.PluriTaylor.sum_I_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:26:50.668969+00:00
-- url     : https://prove2.me/submissions/0f1fb82b-3a3c-49f6-983f-11ccbfda2550

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformTaylorBoundLeviPluriharmonicSplit
import Theorems.Thm_GlobalTheory_PluriTaylor_smul_decomp
import Theorems.Thm_P2M_GlobalTheory_PluriTaylor_vec_expand__9b356877c8c0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
open GlobalTheory GlobalTheory.PluriTaylor
open Complex Set
variable {n : ℕ}
namespace GlobalTheory.PluriTaylor
theorem _root_.solution (w : V n) :
    (∑ k, ((w k).re • (I • bas n k) - (w k).im • bas n k)) = I • w := by
  have h : ∀ k, (w k).re • (I • bas n k) - (w k).im • bas n k = (I * w k) • bas n k := by
    intro k
    rw [smul_decomp (I * w k) (bas n k)]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_sub, zero_add, neg_smul]
    abel
  rw [Finset.sum_congr rfl fun k _ => h k]
  simp_rw [mul_smul]
  rw [← Finset.smul_sum, ← vec_expand']
end GlobalTheory.PluriTaylor
