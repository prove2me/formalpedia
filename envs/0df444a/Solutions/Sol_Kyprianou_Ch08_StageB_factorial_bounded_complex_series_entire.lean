-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.factorial_bounded_complex_series_entire
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T00:16:33.486932+00:00
-- url     : https://prove2.me/submissions/93540892-c0b3-4557-8a19-6cd1a880047b

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false

open Kyprianou.Ch08.StageB

theorem solution (a : ℕ → ℝ) (M R : ℝ)
    (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hbound : ∀ n : ℕ, ‖((a n : ℝ) : ℂ)‖ ≤
        M * R ^ n / (Nat.factorial n : ℝ)) :
    Differentiable ℂ (fun z : ℂ => ∑' n : ℕ,
      z ^ n * ((a n : ℝ) : ℂ)) := by
  intro z
  let B : ℝ := (‖z‖ + 1) * R
  have hB : 0 ≤ B := mul_nonneg (by positivity) hR
  have hu : Summable (fun n : ℕ =>
      M * B ^ n / (Nat.factorial n : ℝ)) := by
    simpa only [mul_div_assoc] using
      (Real.summable_pow_div_factorial B).mul_left M
  have hOn : DifferentiableOn ℂ
      (fun w : ℂ => ∑' n : ℕ, w ^ n * ((a n : ℝ) : ℂ))
      (Metric.ball z 1) := by
    apply Complex.differentiableOn_tsum_of_summable_norm hu
    · intro n
      fun_prop
    · exact Metric.isOpen_ball
    · intro n w hw
      have hd : ‖w - z‖ < 1 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hw
      have hn : ‖w‖ ≤ ‖z‖ + 1 := by
        calc
          ‖w‖ = ‖(w - z) + z‖ := by ring
          _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
          _ ≤ ‖z‖ + 1 := by linarith
      have hpow : ‖w‖ ^ n ≤ (‖z‖ + 1) ^ n := by
        gcongr
      have hfac : 0 ≤ M * R ^ n / (Nat.factorial n : ℝ) := by positivity
      calc
        ‖w ^ n * ((a n : ℝ) : ℂ)‖ =
            ‖w‖ ^ n * ‖((a n : ℝ) : ℂ)‖ := by
              rw [norm_mul, norm_pow]
        _ ≤ ‖w‖ ^ n * (M * R ^ n / (Nat.factorial n : ℝ)) :=
          mul_le_mul_of_nonneg_left (hbound n) (pow_nonneg (norm_nonneg w) n)
        _ ≤ (‖z‖ + 1)^n * (M * R ^ n / (Nat.factorial n : ℝ)) :=
          mul_le_mul_of_nonneg_right hpow hfac
        _ = M * B^n / (Nat.factorial n : ℝ) := by
          dsimp [B]
          rw [mul_pow]
          ring
  exact hOn.differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))
