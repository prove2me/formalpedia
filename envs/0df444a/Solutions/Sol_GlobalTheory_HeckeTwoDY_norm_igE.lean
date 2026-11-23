-- Prove2me | solution 1 for GlobalTheory.HeckeTwoDY.norm_igE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:26.019875+00:00
-- url     : https://prove2.me/submissions/2a4ed726-feec-4980-8f5e-b8d10f098cf9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABHasDerivAtY
import Theorems.Thm_GlobalTheory_HeckeTwoDY_q_pos
import Theorems.Thm_GlobalTheory_HeckeTwoDY_norm_wt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoDY
open MeasureTheory
namespace GlobalTheory.HeckeTwoDY
theorem _root_.solution {a b : ℕ} {σ : ℂ} {ν y : ℝ} (hy : y ≠ 0) (t : ℝ) :
    ‖igE a b σ ν y t‖ = Real.exp (-(((a : ℝ) + b + 2 * σ.re) / 2) * Real.log (t ^ 2 + y ^ 2)) := by
  have hq := q_pos (t := t) hy
  have hs : √(t ^ 2 + y ^ 2) = Real.exp (Real.log (t ^ 2 + y ^ 2) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hq]; ring_nf
  unfold igE
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_inv, norm_inv, Complex.norm_conj, norm_wt, hs,
    Complex.norm_exp, Complex.norm_exp]
  have h0 : (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))).re = 0 := by simp
  rw [h0, Real.exp_zero, mul_one, ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  congr 1
  simp [Complex.mul_re]
  ring
end GlobalTheory.HeckeTwoDY
