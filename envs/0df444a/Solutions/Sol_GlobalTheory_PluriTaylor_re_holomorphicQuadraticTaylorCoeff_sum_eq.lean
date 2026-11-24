-- Prove2me | solution 1 for GlobalTheory.PluriTaylor.re_holomorphicQuadraticTaylorCoeff_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:27:15.543691+00:00
-- url     : https://prove2.me/submissions/3c920788-1ad2-4a58-939f-b5e92ed06589

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
theorem _root_.solution (B : V n →L[ℝ] V n →L[ℝ] ℝ) (a c : Fin n → ℝ) :
    8 * (∑ j, ∑ k, ((a j : ℂ) + (c j : ℂ) * I) * ((a k : ℂ) + (c k : ℂ) * I) * qc B j k).re =
      B (∑ k, (a k • bas n k + c k • (I • bas n k))) (∑ k, (a k • bas n k + c k • (I • bas n k))) -
      B (∑ k, (a k • (I • bas n k) - c k • bas n k)) (∑ k, (a k • (I • bas n k) - c k • bas n k)) := by
  have e : ∀ x y : Fin n → V n, B (∑ j, x j) (∑ k, y k) = ∑ j, ∑ k, B (x j) (y k) := by
    intro x y
    rw [map_sum B, ContinuousLinearMap.sum_apply]
    simp_rw [map_sum]
  rw [e, e, Complex.re_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [map_add, map_sub, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, qc,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.sub_re, Complex.sub_im]
  ring
end GlobalTheory.PluriTaylor
