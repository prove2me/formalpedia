-- Prove2me | solution 1 for GlobalTheory.norm_latPt_le_two_mul_of_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:27:23.466593+00:00
-- url     : https://prove2.me/submissions/bec44ada-b44a-4be6-8a55-c3df161024cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_NormFderivLeOfClosedBallSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinSeriesLatticeDifferentiableOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open Metric Complex
open GlobalTheory
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
namespace GlobalTheory
theorem _root_.solution {F : Type} [Field F] [NumberField F] {z z₀ : Emb F → ℂ} {r : ℝ}
    (hr : ∀ τ, 2 * r ≤ (z₀ τ).im) (hz : ‖z - z₀‖ < r) (p : F × F) (τ : Emb F) :
    ‖latPt z₀ p τ‖ ≤ 2 * ‖latPt z p τ‖ := by
  have h1 : ‖z τ - z₀ τ‖ < r := lt_of_le_of_lt (norm_le_pi_norm (z - z₀) τ) hz
  have h2 : r ≤ (z τ).im := by
    have h3 := abs_im_le_norm (z τ - z₀ τ)
    rw [sub_im] at h3
    have h4 := (abs_le.1 (h3.trans h1.le)).1
    linarith [hr τ]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have e : latPt z₀ p τ = latPt z p τ + 2 * (Real.pi : ℂ) * I * ((τ p.2 : ℝ) : ℂ) * (z₀ τ - z τ) := by
    simp only [latPt]; ring
  have hn : ∀ w : ℂ, ‖2 * (Real.pi : ℂ) * I * w‖ = 2 * Real.pi * ‖w‖ := by
    intro w
    rw [norm_mul, norm_mul, norm_mul, norm_I, Complex.norm_real, Real.norm_of_nonneg hpi.le]
    norm_num
  have hlow : 2 * Real.pi * (|τ p.2| * r) ≤ ‖latPt z p τ‖ := by
    rw [latPt, hn]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans ?_ (abs_im_le_norm _)
    simp only [add_im, ofReal_im, mul_im, ofReal_re, zero_mul, add_zero, zero_add]
    rw [abs_mul, abs_of_pos (lt_of_lt_of_le (lt_of_le_of_lt (norm_nonneg _) hz) h2)]
    exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have hup : ‖2 * (Real.pi : ℂ) * I * ((τ p.2 : ℝ) : ℂ) * (z₀ τ - z τ)‖ ≤ 2 * Real.pi * (|τ p.2| * r) := by
    rw [show 2 * (Real.pi : ℂ) * I * ((τ p.2 : ℝ) : ℂ) * (z₀ τ - z τ) = 2 * (Real.pi : ℂ) * I * (((τ p.2 : ℝ) : ℂ) * (z₀ τ - z τ)) by ring, hn, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_sub_rev]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1.le (abs_nonneg _)) (by positivity)
  rw [e]
  linarith [norm_add_le (latPt z p τ) (2 * (Real.pi : ℂ) * I * ((τ p.2 : ℝ) : ℂ) * (z₀ τ - z τ))]
end GlobalTheory
