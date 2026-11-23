-- Prove2me | solution 1 for GlobalTheory.PluriTaylor.smul_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:05.887357+00:00
-- url     : https://prove2.me/submissions/2e40c47f-40a3-4a66-972c-630eca6f0a58

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformTaylorBoundLeviPluriharmonicSplit

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
theorem _root_.solution (c : ℂ) (v : V n) : c • v = c.re • v + c.im • (I • v) := by
  ext j
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Complex.real_smul]
  conv_lhs => rw [← Complex.re_add_im c]
  ring
end GlobalTheory.PluriTaylor
