-- Prove2me | solution 1 for GlobalTheory.LLeft.norm_diffPow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:12:09.344442+00:00
-- url     : https://prove2.me/submissions/968437ec-d692-4240-995f-1aa398d1239a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNinePowMulInvSqSucc
import Theorems.Thm_GlobalTheory_LLeft_hasDerivAt_diffPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory
open GlobalTheory.LLeft
namespace GlobalTheory.LLeft
theorem _root_.solution (k : ℕ) : ∀ (s : ℂ) (x : ℝ), 0 < x → 0 ≤ s.re + k →
    ‖diffPow k s x‖ ≤ (‖s‖ + k) ^ k * x ^ (-(s.re + k)) := by
  induction k with
  | zero =>
    intro s x hx _
    simp [diffPow, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  | succ k ih =>
    intro s x hx hs
    have hs' : 0 ≤ (s + 1).re + k := by
      simp only [add_re, one_re]; push_cast at hs; linarith
    have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := diffPow k s)
      (f' := fun y => -s * diffPow k (s + 1) y) (a := x) (b := x + 1)
      (C := (‖s‖ + (k + 1 : ℕ)) ^ (k + 1) * x ^ (-(s.re + (k + 1 : ℕ))))
      (fun y hy => (hasDerivAt_diffPow k s y (hx.trans_le hy.1)).hasDerivWithinAt)
      (by
        intro y hy
        have hy0 : 0 < y := hx.trans_le hy.1
        have h1 := ih (s + 1) y hy0 hs'
        have h2 : y ^ (-((s + 1).re + k)) ≤ x ^ (-((s + 1).re + k)) :=
          Real.rpow_le_rpow_of_nonpos hx hy.1 (by linarith)
        have h3 : ‖s + 1‖ + k ≤ ‖s‖ + (k + 1 : ℕ) := by
          have := norm_add_le s 1
          push_cast; simp only [norm_one] at this; linarith
        have h4 : ‖s‖ ≤ ‖s‖ + (k + 1 : ℕ) := le_add_of_nonneg_right (by positivity)
        have e : -(s.re + (k + 1 : ℕ)) = -((s + 1).re + k) := by
          simp only [add_re, one_re]; push_cast; ring
        rw [norm_mul, norm_neg, e, pow_succ', mul_assoc]
        refine mul_le_mul h4 (h1.trans ?_) (norm_nonneg _) (by positivity)
        gcongr)
      (x + 1) ⟨by linarith, le_rfl⟩
    simp only [diffPow]
    rw [norm_sub_rev]
    simpa using key
end GlobalTheory.LLeft
