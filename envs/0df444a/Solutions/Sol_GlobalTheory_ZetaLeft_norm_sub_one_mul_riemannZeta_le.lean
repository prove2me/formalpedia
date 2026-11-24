-- Prove2me | solution 1 for GlobalTheory.ZetaLeft.norm_sub_one_mul_riemannZeta_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:59:08.119966+00:00
-- url     : https://prove2.me/submissions/edd4cdb4-88be-4f00-804f-2ba767d566f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
import Theorems.Thm_GlobalTheory_ZetaLeft_norm_emE_le
import Theorems.Thm_GlobalTheory_ZetaLeft_summable_nine_pow_mul_inv_sq_succ
import Theorems.Thm_GlobalTheory_ZetaLeft_eq_of_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open GlobalTheory GlobalTheory.ZetaLeft
namespace GlobalTheory.ZetaLeft
theorem _root_.solution :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -(7/4 : ℝ) ≤ s.re → s ≠ 1 →
      ‖(s - 1) * riemannZeta s‖ ≤ C * (‖s‖ + 2) ^ 5 := by
  set K : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(9/8 : ℝ)) with hK
  have hK0 : 0 ≤ K := tsum_nonneg fun n => by positivity
  refine ⟨3 + K, by linarith, fun s hs h1 => ?_⟩
  rw [eq_of_lt (by linarith) h1]
  set R := ‖s‖ + 2 with hR
  have hR1 : 1 ≤ R := by have := norm_nonneg s; linarith
  have h2 : ‖∑' n : ℕ, emE ((n : ℝ) + 1) s‖ ≤ R ^ 4 * K :=
    tsum_of_norm_bounded (summable_nine_pow_mul_inv_sq_succ.hasSum.mul_left (R ^ 4))
      (fun n => norm_emE_le (by simp) (by linarith))
  have c0 : ‖1 - s‖ ≤ R := by
    have := norm_sub_le 1 s
    rw [norm_one] at this; linarith
  have c1 : ‖1 - s - 1‖ ≤ R := by simp [hR]
  have h3 : ‖emT 1 s‖ ≤ 1 + R / 2 + R * R / 12 := by
    simp only [emT, Complex.ofReal_one, Complex.one_cpow, mul_one]
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) ?_)
    · simp only [norm_one, norm_div, Complex.norm_ofNat]; gcongr
    · simp only [norm_mul, norm_div, Complex.norm_ofNat]; gcongr
  have p0 : 1 ≤ R ^ 5 := one_le_pow₀ hR1
  have p1 : R ^ 1 ≤ R ^ 5 := pow_le_pow_right₀ hR1 (by norm_num)
  have p2 : R ^ 2 ≤ R ^ 5 := pow_le_pow_right₀ hR1 (by norm_num)
  have p4 : R ^ 4 ≤ R ^ 5 := pow_le_pow_right₀ hR1 (by norm_num)
  have p5 : R ^ 4 * K ≤ R ^ 5 * K := by gcongr
  refine (norm_add_le _ _).trans ?_
  nlinarith
end GlobalTheory.ZetaLeft
