-- Prove2me | solution 1 for GlobalTheory.PluriTaylor.sum_re_im_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:27:02.875447+00:00
-- url     : https://prove2.me/submissions/83882647-146b-41e6-903f-7a0b9bc416ba

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
    (∑ k, ((w k).re • bas n k + (w k).im • (I • bas n k))) = w := by
  rw [Finset.sum_congr rfl fun k _ => (smul_decomp (w k) (bas n k)).symm]
  exact (vec_expand' w).symm
end GlobalTheory.PluriTaylor
