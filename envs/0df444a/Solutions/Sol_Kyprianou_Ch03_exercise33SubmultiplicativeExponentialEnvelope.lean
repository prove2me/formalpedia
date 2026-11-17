-- Prove2me | solution 1 for Kyprianou.Ch03.exercise33SubmultiplicativeExponentialEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:29:07.097374+00:00
-- url     : https://prove2.me/submissions/b175f664-1184-4c76-b124-05b24749af88

import Mathlib
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem exercise33SubmultiplicativeExponentialEnvelope
(g : ℝ → ℝ)
    (hg : IsSubmultiplicative g)
    (hgBounded : ∀ R : ℝ, 0 ≤ R →
       ∃ M : ℝ, ∀ x, |x| ≤ R → g x ≤ M) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
       ∀ x : ℝ, g x ≤ a * Real.exp (b * |x|) := by
  obtain ⟨hnn, c, hc, hmul⟩ := hg
  obtain ⟨M, hM⟩ := hgBounded 1 zero_le_one
  set A := max c 1 * max M 1 with hA
  have hA1 : 1 ≤ A := by
    have h1 : 1 ≤ max c 1 := le_max_right _ _
    have h2 : 1 ≤ max M 1 := le_max_right _ _
    nlinarith
  have hcM : ∀ y, |y| ≤ 1 → c * g y ≤ A := by
    intro y hy
    have : g y ≤ max M 1 := (hM y hy).trans (le_max_left _ _)
    calc c * g y ≤ max c 1 * max M 1 :=
          mul_le_mul (le_max_left _ _) this (hnn y) (by positivity)
      _ = A := rfl
  have hM1 : ∀ y, |y| ≤ 1 → g y ≤ A := by
    intro y hy
    calc g y ≤ max M 1 := (hM y hy).trans (le_max_left _ _)
      _ = 1 * max M 1 := by ring
      _ ≤ A := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have key : ∀ n : ℕ, ∀ x, |x| ≤ (n : ℝ) + 1 → g x ≤ A ^ (n + 1) := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hM1 x (by simpa using hx)
    | succ k ih =>
      intro x hx
      by_cases hx1 : |x| ≤ 1
      · calc g x ≤ A := hM1 x hx1
          _ = A ^ 1 := (pow_one A).symm
          _ ≤ A ^ (k + 1 + 1) := pow_le_pow_right₀ hA1 (by omega)
      · push Not at hx1
        set s : ℝ := if 0 ≤ x then 1 else -1 with hs
        have hs1 : |s| ≤ 1 := by simp only [hs]; split_ifs <;> simp
        have hy : |x - s| ≤ (k : ℝ) + 1 := by
          simp only [hs]
          split_ifs with h0
          · rw [abs_of_nonneg h0] at hx1 hx
            rw [abs_of_nonneg (by linarith)]; push_cast at hx; linarith
          · push Not at h0
            rw [abs_of_neg h0] at hx1 hx
            rw [abs_of_neg (by linarith)]; push_cast at hx; linarith
        have hxs : x = (x - s) + s := by ring
        calc g x = g ((x - s) + s) := by rw [← hxs]
          _ ≤ c * g (x - s) * g s := hmul _ _
          _ = g (x - s) * (c * g s) := by ring
          _ ≤ A ^ (k + 1) * A :=
              mul_le_mul (ih _ hy) (hcM s hs1) (by have := hnn s; positivity) (by positivity)
          _ = A ^ (k + 1 + 1) := by ring
  refine ⟨A, Real.log A + 1, by linarith, by linarith [Real.log_nonneg hA1], fun x => ?_⟩
  set n := ⌊|x|⌋₊ with hn
  have hn1 : |x| < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hn2 : (n : ℝ) ≤ |x| := Nat.floor_le (abs_nonneg x)
  have hg := key n x hn1.le
  have hApos : 0 < A := by linarith
  calc g x ≤ A ^ (n + 1) := hg
    _ = A * Real.exp (Real.log A * n) := by
        rw [pow_succ, mul_comm, Real.exp_mul, Real.exp_log hApos, Real.rpow_natCast]
    _ ≤ A * Real.exp ((Real.log A + 1) * |x|) := by
        apply mul_le_mul_of_nonneg_left _ hApos.le
        apply Real.exp_le_exp.2
        have := Real.log_nonneg hA1
        nlinarith [abs_nonneg x]

end Kyprianou.Ch03

theorem solution
(g : ℝ → ℝ)
    (hg : Kyprianou.Ch03.IsSubmultiplicative g)
    (hgBounded : ∀ R : ℝ, 0 ≤ R →
       ∃ M : ℝ, ∀ x, |x| ≤ R → g x ≤ M) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
       ∀ x : ℝ, g x ≤ a * Real.exp (b * |x|) :=
  Kyprianou.Ch03.exercise33SubmultiplicativeExponentialEnvelope g hg hgBounded
