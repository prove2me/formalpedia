-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.integral_opT_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:08:06.470141+00:00
-- url     : https://prove2.me/submissions/aa28f9a2-5b4e-4070-b54a-04b75ac357f8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_hasCompactSupport_iteratedDeriv
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integral_iteratedDeriv_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution (a : ℕ → ℝ) (n : ℕ) {F ψ : ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    ∫ u, opT a n F u * ψ u =
      ∫ u, F u * ∑ p ∈ Finset.range (n + 1), (coef a n p : ℂ) * iteratedDeriv p ψ u := by
  have hint : ∀ p, Integrable fun u => sc a n p * iteratedDeriv p F u * ψ u := fun p =>
    ((continuous_const.mul (hF.continuous_iteratedDeriv p (by exact_mod_cast le_top))).mul
      hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
  have hint' : ∀ p, Integrable fun u => F u * ((coef a n p : ℂ) * iteratedDeriv p ψ u) := fun p =>
    (hF.continuous.mul (continuous_const.mul
      (hψ.continuous_iteratedDeriv p (by exact_mod_cast le_top)))).integrable_of_hasCompactSupport
      ((hasCompactSupport_iteratedDeriv hψc p).mul_left.mul_left)
  simp only [opT, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ fun p _ => hint p, integral_finsetSum _ fun p _ => hint' p]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [mul_assoc]
  rw [integral_const_mul, integral_iteratedDeriv_mul hF hψ hψc p, sc]
  have : ∫ u, F u * ((coef a n p : ℂ) * iteratedDeriv p ψ u) =
      (coef a n p : ℂ) * ∫ u, F u * iteratedDeriv p ψ u := by
    rw [← integral_const_mul]; congr 1; funext u; ring
  rw [this]
  have h1 : ((-1 : ℂ) ^ p) * ((-1) ^ p) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  linear_combination ((coef a n p : ℂ) * ∫ u, F u * iteratedDeriv p ψ u) * h1
end GroundTheory.Automorphic.LineKernel
