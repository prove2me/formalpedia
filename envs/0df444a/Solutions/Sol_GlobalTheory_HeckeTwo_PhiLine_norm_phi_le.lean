-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.PhiLine.norm_phi_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:45:46.5828+00:00
-- url     : https://prove2.me/submissions/c95d952e-e91a-4b28-a319-a8d2a27d808d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoKernelPhiLineContinuousIntegrable
import Theorems.Thm_GlobalTheory_HeckeTwo_PhiLine_norm_line_sq
import Theorems.Thm_GlobalTheory_HeckeTwo_PhiLine_abs_le_norm_line

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex MeasureTheory
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.PhiLine
namespace GlobalTheory.HeckeTwo.PhiLine
theorem _root_.solution (σ : ℂ) (hσ : 0 < σ.re) (y : ℝ) (hy : y ≠ 0) (t : ℝ) :
    ‖GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      |y| ^ (-2 * σ.re) * (min 1 (y ^ 2))⁻¹ * (1 + t ^ 2)⁻¹ := by
  set w : ℂ := (t : ℂ) + (y : ℂ) * Complex.I with hw
  have hay : 0 < |y| := abs_pos.2 hy
  have hle : |y| ≤ ‖w‖ := abs_le_norm_line t y
  have hpos : 0 < ‖w‖ := lt_of_lt_of_le hay hle
  have hsq : ‖w‖ ^ 2 = t ^ 2 + y ^ 2 := norm_line_sq t y
  unfold GlobalTheory.HeckeTwo.phi
  rw [norm_mul, norm_pow, norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have hre : (-2 * σ).re = -2 * σ.re := by simp
  rw [hre]
  have h1 : ‖w‖ ^ (-2 * σ.re) ≤ |y| ^ (-2 * σ.re) :=
    Real.rpow_le_rpow_of_nonpos hay hle (by linarith)
  have hy2 : 0 < y ^ 2 := by positivity
  have hm : 0 < min 1 (y ^ 2) := lt_min one_pos hy2
  have h2 : ‖w‖⁻¹ ^ 2 ≤ (min 1 (y ^ 2))⁻¹ * (1 + t ^ 2)⁻¹ := by
    rw [inv_pow, hsq, ← mul_inv]
    apply inv_anti₀ (by positivity)
    have := min_le_left 1 (y ^ 2)
    have := min_le_right 1 (y ^ 2)
    nlinarith [sq_nonneg t]
  calc ‖w‖⁻¹ ^ 2 * ‖w‖ ^ (-2 * σ.re) ≤ ((min 1 (y ^ 2))⁻¹ * (1 + t ^ 2)⁻¹) * |y| ^ (-2 * σ.re) :=
        mul_le_mul h2 h1 (by positivity) (by positivity)
    _ = _ := by ring
end GlobalTheory.HeckeTwo.PhiLine
