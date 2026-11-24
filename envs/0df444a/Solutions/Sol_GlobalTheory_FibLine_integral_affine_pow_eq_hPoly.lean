-- Prove2me | solution 1 for GlobalTheory.FibLine.integral_affine_pow_eq_hPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:26:48.796632+00:00
-- url     : https://prove2.me/submissions/6c0aedd7-547e-4dcf-9916-98ec11258da5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralAffinePowEqHPoly
import Theorems.Thm_GlobalTheory_FibLine_sub_mul_eval_hPoly
import Theorems.Thm_GlobalTheory_FibLine_eval_hPoly_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MeasureTheory MvPolynomial GlobalTheory.FibLine
open GlobalTheory GlobalTheory.FibLine
namespace GlobalTheory.FibLine
theorem _root_.solution (k : ℕ) (a b : ℂ) :
    ∫ t in (0 : ℝ)..1, ((t : ℂ) * a + (1 - (t : ℂ)) * b) ^ k
      = MvPolynomial.eval ![a + b, a * b] (hPoly k) / ((k : ℂ) + 1) := by
  have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  by_cases hab : a = b
  · subst hab
    have : ∀ t : ℝ, ((t : ℂ) * a + (1 - (t : ℂ)) * a) ^ k = a ^ k := fun t => by ring
    simp only [this]
    rw [eval_hPoly_diag]
    simp
    field_simp
  · have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
    have hder : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt
        (fun t : ℝ => ((t : ℂ) * a + (1 - (t : ℂ)) * b) ^ (k + 1) / (((k : ℂ) + 1) * (a - b)))
        (((t : ℂ) * a + (1 - (t : ℂ)) * b) ^ k) t := by
      intro t _
      have h1 : HasDerivAt (fun z : ℂ => z * a + (1 - z) * b) (a - b) (t : ℂ) := by
        have := ((hasDerivAt_id (t : ℂ)).mul_const a).add
          (((hasDerivAt_id (t : ℂ)).const_sub 1).mul_const b)
        exact this.congr_deriv (by ring)
      have h2 := ((h1.pow (k + 1)).div_const (((k : ℂ) + 1) * (a - b))).comp_ofReal
      refine h2.congr_deriv ?_
      simp only [Nat.add_sub_cancel]
      push_cast
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    have h := sub_mul_eval_hPoly a b k
    simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, sub_self, zero_mul, add_zero, zero_add, sub_zero]
    rw [← sub_div, ← h]
    field_simp
end GlobalTheory.FibLine
