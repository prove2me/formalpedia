-- Prove2me | solution 1 for OAI.PiExponent.exp_beats_affine_after
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T09:21:32.550896+00:00
-- url     : https://prove2.me/submissions/c7da89d3-a436-4cef-b463-7043b23530c9

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic
import Theorems.Thm_OAI_PiExponent_exp_beats_quadratic_after

 theorem solution
    (R p q : ℝ) (hR : 1 < R) (M : ℕ) :
    ∃ m : ℕ, M ≤ m ∧ 0 < m ∧
      p * (m : ℝ) + q < R ^ m / (8 * ((m : ℝ) + 1)) := by
  let A : ℝ := |p| + |q| + 1
  have hA : 0 < A := by
    dsimp [A]
    positivity
  obtain ⟨m, hm, hpow⟩ :=
    OAI.PiExponent.exp_beats_quadratic_after R (8 * A) hR (M + 1) (by positivity)
  refine ⟨m, le_trans (Nat.le_succ M) hm, Nat.lt_of_lt_of_le (Nat.zero_lt_succ M) hm, ?_⟩
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hpm : p * (m : ℝ) ≤ |p| * (m : ℝ) :=
    mul_le_mul_of_nonneg_right (le_abs_self p) hm0
  have hlin : p * (m : ℝ) + q < A * ((m : ℝ) + 1) := by
    dsimp [A]
    nlinarith [abs_nonneg p, abs_nonneg q, hpm, le_abs_self q]
  let d : ℝ := (m : ℝ) + 1
  have hd : 0 < 8 * d := by
    dsimp [d]
    positivity
  have hquot : A * d < R ^ m / (8 * d) := by
    rw [lt_div_iff₀ hd]
    calc
      A * d * (8 * d) = (8 * A) * ((m : ℝ) + 1) ^ 2 := by
        dsimp [d]
        ring
      _ < R ^ m := by simpa using hpow
  exact lt_trans hlin (by simpa [d] using hquot)