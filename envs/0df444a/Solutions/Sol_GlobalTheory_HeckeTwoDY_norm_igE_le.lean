-- Prove2me | solution 1 for GlobalTheory.HeckeTwoDY.norm_igE_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:24:56.778721+00:00
-- url     : https://prove2.me/submissions/f0e89280-3ac8-4c1c-85e5-ad2b97b5cc32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABHasDerivAtY
import Theorems.Thm_GlobalTheory_HeckeTwoDY_q_pos
import Theorems.Thm_GlobalTheory_HeckeTwoDY_norm_igE

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
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoDY
open MeasureTheory
namespace GlobalTheory.HeckeTwoDY
theorem _root_.solution {a b : ℕ} {σ : ℂ} {ν y y' : ℝ} (hk : 0 ≤ (a : ℝ) + b + 2 * σ.re) (hy : y ≠ 0)
    (hy' : |y' - y| < |y| / 2) (t : ℝ) :
    ‖igE a b σ ν y' t‖ ≤ Real.exp (-(((a : ℝ) + b + 2 * σ.re) / 2) * Real.log (t ^ 2 + (y / 2) ^ 2)) := by
  have h1 : |y| / 2 < |y'| := by
    have := abs_sub_abs_le_abs_sub y y'
    rw [abs_sub_comm] at this; linarith
  have hypos : 0 < |y| := abs_pos.2 hy
  have hy'0 : y' ≠ 0 := by
    intro h; rw [h, abs_zero] at h1; linarith
  have h2 : (y / 2) ^ 2 ≤ y' ^ 2 := by
    rw [← sq_abs y', show (y / 2) ^ 2 = (|y| / 2) ^ 2 by rw [div_pow, div_pow, sq_abs]]
    nlinarith
  have hq0 : 0 < t ^ 2 + (y / 2) ^ 2 := q_pos (div_ne_zero hy two_ne_zero)
  have hlog : Real.log (t ^ 2 + (y / 2) ^ 2) ≤ Real.log (t ^ 2 + y' ^ 2) := Real.log_le_log hq0 (by linarith)
  rw [norm_igE hy'0]
  apply Real.exp_le_exp.2
  nlinarith [mul_le_mul_of_nonneg_left hlog hk]
end GlobalTheory.HeckeTwoDY
