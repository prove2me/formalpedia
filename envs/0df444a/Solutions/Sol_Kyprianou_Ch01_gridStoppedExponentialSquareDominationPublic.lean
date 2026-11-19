-- Prove2me | solution 1 for Kyprianou.Ch01.gridStoppedExponentialSquareDominationPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T10:02:33.415457+00:00
-- url     : https://prove2.me/submissions/469e05c1-2237-499e-8912-84df41230d95

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
set_option autoImplicit false

/-- A stopped exponential square is dominated by the doubled-parameter martingale. -/
theorem solution {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma theta q : ℝ)
    (hroot : sigma ^ 2 * theta ^ 2 / 2 + gamma * theta = q)
    (delta : ℝ≥0) (tau : Ω → ℕ) (N : ℕ)
    (hBound : ∀ ω, tau ω ≤ N) (ω : Ω) :
    Real.exp (theta * X ((tau ω : ℝ≥0) * delta) ω -
      q * (((tau ω : ℝ≥0) * delta) : ℝ)) ^ 2 ≤
    Real.exp (sigma ^ 2 * theta ^ 2 * (((N : ℝ≥0) * delta) : ℝ)) *
      Real.exp ((2 * theta) * X ((tau ω : ℝ≥0) * delta) ω -
        (sigma ^ 2 * (2 * theta) ^ 2 / 2 + gamma * (2 * theta)) *
          (((tau ω : ℝ≥0) * delta) : ℝ)) := by
  let t : ℝ≥0 := (tau ω : ℝ≥0) * delta
  let T : ℝ≥0 := (N : ℝ≥0) * delta
  let z : ℝ := X t ω
  have htN : t ≤ T := by
    dsimp [t, T]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast hBound ω) (by positivity)
  have ht : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast htN
  have hcoeff : 0 ≤ sigma ^ 2 * theta ^ 2 :=
    mul_nonneg (sq_nonneg sigma) (sq_nonneg theta)
  have hExp :
      Real.exp (theta * z - q * (t : ℝ)) ^ 2 =
      Real.exp (sigma ^ 2 * theta ^ 2 * (t : ℝ)) *
        Real.exp ((2 * theta) * z -
          (sigma ^ 2 * (2 * theta) ^ 2 / 2 + gamma * (2 * theta)) *
            (t : ℝ)) := by
    calc
      _ = Real.exp ((theta * z - q * (t : ℝ)) +
          (theta * z - q * (t : ℝ))) := by
            rw [pow_two, ← Real.exp_add]
      _ = Real.exp (sigma ^ 2 * theta ^ 2 * (t : ℝ) +
          ((2 * theta) * z -
           (sigma ^ 2 * (2 * theta) ^ 2 / 2 + gamma * (2 * theta)) *
             (t : ℝ))) := by
            congr 1
            rw [← hroot]
            ring
      _ = _ := Real.exp_add _ _
  change Real.exp (theta * z - q * (t : ℝ)) ^ 2 ≤
      Real.exp (sigma ^ 2 * theta ^ 2 * (T : ℝ)) *
        Real.exp ((2 * theta) * z -
          (sigma ^ 2 * (2 * theta) ^ 2 / 2 + gamma * (2 * theta)) *
            (t : ℝ))
  rw [hExp]
  apply mul_le_mul_of_nonneg_right
  · exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left ht hcoeff)
  · exact (Real.exp_pos _).le
