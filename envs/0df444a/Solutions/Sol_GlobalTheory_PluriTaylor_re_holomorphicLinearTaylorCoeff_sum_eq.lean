-- Prove2me | solution 1 for GlobalTheory.PluriTaylor.re_holomorphicLinearTaylorCoeff_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:27:14.938834+00:00
-- url     : https://prove2.me/submissions/c94f8a82-4668-4ea7-b1f0-073d379b46fb

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
noncomputable section
namespace GlobalTheory.PluriTaylor
theorem _root_.solution (F : V n →L[ℝ] ℝ) (a c : Fin n → ℝ) :
    2 * (∑ j, ((a j : ℂ) + (c j : ℂ) * I) * lc F j).re =
      F (∑ k, (a k • bas n k + c k • (I • bas n k))) := by
  simp only [map_sum, map_add, map_smul, smul_eq_mul, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [lc, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.sub_re, Complex.sub_im]
  ring
end GlobalTheory.PluriTaylor
