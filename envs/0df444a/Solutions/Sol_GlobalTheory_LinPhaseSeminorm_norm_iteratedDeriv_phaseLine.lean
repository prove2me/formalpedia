-- Prove2me | solution 1 for GlobalTheory.LinPhaseSeminorm.norm_iteratedDeriv_phaseLine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:00:47.641779+00:00
-- url     : https://prove2.me/submissions/59b1a61e-afc1-45b5-847b-23f3c7f3af06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormSmulLeftLinearPhaseLe
import Theorems.Thm_GlobalTheory_LinPhaseSeminorm_iteratedDeriv_const_mul_cexp
import Theorems.Thm_GlobalTheory_LinPhaseSeminorm_norm_cexp_neg_two_pi_I_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
open Complex
open GlobalTheory GlobalTheory.LinPhaseSeminorm
namespace GlobalTheory.LinPhaseSeminorm
theorem _root_.solution (c t : ℝ) (i : ℕ) (y : ℝ) :
    ‖iteratedDeriv i (phaseLine c t) y‖ = (2 * Real.pi * |t|) ^ i := by
  have e : phaseLine c t = fun y : ℝ =>
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t ^ 2 * c : ℝ) : ℂ)) *
        Complex.exp ((-(2 * Real.pi * Complex.I) * (t : ℂ)) * (y : ℂ)) := rfl
  rw [e, iteratedDeriv_const_mul_cexp]
  have h2 : (-(2 * Real.pi * Complex.I) * (t : ℂ)) * (y : ℂ)
      = -(2 * Real.pi * Complex.I) * ((t * y : ℝ) : ℂ) := by push_cast; ring
  simp only
  rw [h2, norm_mul, norm_mul, norm_cexp_neg_two_pi_I_mul, norm_cexp_neg_two_pi_I_mul, norm_pow]
  simp [abs_of_pos Real.pi_pos]
end GlobalTheory.LinPhaseSeminorm
