-- Prove2me | solution 1 for GlobalTheory.HeckeShift.factor_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:32:25.285347+00:00
-- url     : https://prove2.me/submissions/25c408ab-ed4d-4d2d-a683-807304a4b4fa

import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeMellinGaussIntegrandUnitMul
import Theorems.Thm_GlobalTheory_HeckeShift_hmon_mul_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.HeckeShift
namespace GlobalTheory.HeckeShift
theorem _root_.solution (n : ℤ) (y : ℝ) {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    GlobalTheory.HeckeTheta.hmon n ((Real.exp (y / 2) : ℂ) * (z * w)) *
                 Complex.exp ((-2 * Real.pi * ‖(Real.exp (y / 2) : ℂ) * (z * w)‖ ^ 2 : ℝ) : ℂ) =
      (z / ((‖z‖ : ℝ) : ℂ)) ^ (-n) *
        (GlobalTheory.HeckeTheta.hmon n ((Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) : ℂ) * w) *
          Complex.exp ((-2 * Real.pi * ‖(Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) : ℂ) * w‖ ^ 2 : ℝ) : ℂ)) := by
  have hn0 : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hz
  have hE : Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) = Real.exp (y / 2) * ‖z‖ := by
    rw [Real.log_pow, add_div, Real.exp_add]
    congr 1
    rw [show ((2 : ℕ) : ℝ) * Real.log ‖z‖ / 2 = Real.log ‖z‖ by push_cast; ring, Real.exp_log hn0]
  have hzc : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hζ : ‖z / ((‖z‖ : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hn0.ne']
  have hv : (Real.exp (y / 2) : ℂ) * (z * w) =
      (z / ((‖z‖ : ℝ) : ℂ)) * ((Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) : ℂ) * w) := by
    rw [hE]; push_cast; field_simp
  rw [hv, hmon_mul_unit hζ, norm_mul, hζ, one_mul, mul_assoc]
end GlobalTheory.HeckeShift
