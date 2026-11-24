-- Prove2me | solution 1 for GlobalTheory.HeckeMellinOne.complex_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:49:52.085576+00:00
-- url     : https://prove2.me/submissions/2a13590d-fc46-4e55-b712-ce74982a6b09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralHeckeMellinGaussIntegrandEqProdGammaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypeProdNormSqEqAbsNormSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeMellinGaussIntegralNonzeroInteger
import Theorems.Thm_GlobalTheory_HeckeMellinOne_hmon_eq_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField MeasureTheory
open GlobalTheory GlobalTheory.HeckeMellinOne
namespace GlobalTheory.HeckeMellinOne
theorem _root_.solution (z : ℂ) (hz : z ≠ 0) (n : ℤ) (s G : ℂ) :
    2 * (GlobalTheory.HeckeTheta.hmon n z * G *
      ((2 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-(s + ((|n| : ℤ) : ℂ) / 2))) =
      2 * (2 * (Real.pi : ℂ)) ^ (-(s + ((|n| : ℤ) : ℂ) / 2)) * G *
        ((z / ((‖z‖ : ℝ) : ℂ)) ^ (-n) * ((‖z‖ ^ 2 : ℝ) : ℂ) ^ (-s)) := by
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h2π : 0 < 2 * Real.pi := by positivity
  have e2 : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  have hk : ((n.natAbs : ℕ) : ℂ) = ((|n| : ℤ) : ℂ) := by
    rw [← Int.cast_natCast, Int.natCast_natAbs]
  rw [hmon_eq_mul n hz, e2, ← Complex.cpow_natCast,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (by positivity : (0:ℝ) < 2 * Real.pi * ‖z‖ ^ 2).ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast h2π.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (by positivity : (0:ℝ) < ‖z‖ ^ 2).ne'),
    ← Complex.ofReal_log hr.le, ← Complex.ofReal_log (by positivity), ← Complex.ofReal_log h2π.le,
    ← Complex.ofReal_log (by positivity), Real.log_mul h2π.ne' (by positivity), Real.log_pow, hk]
  have key : Complex.exp (((Real.log ‖z‖ : ℝ) : ℂ) * ((|n| : ℤ) : ℂ)) *
      Complex.exp (((Real.log (2 * Real.pi) + (2 : ℕ) * Real.log ‖z‖ : ℝ) : ℂ) * -(s + ((|n| : ℤ) : ℂ) / 2)) =
      Complex.exp (((Real.log (2 * Real.pi) : ℝ) : ℂ) * -(s + ((|n| : ℤ) : ℂ) / 2)) *
      Complex.exp ((((2 : ℕ) * Real.log ‖z‖ : ℝ) : ℂ) * -s) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  linear_combination (2 * (z / ((‖z‖ : ℝ) : ℂ)) ^ (-n) * G) * key
end GlobalTheory.HeckeMellinOne
