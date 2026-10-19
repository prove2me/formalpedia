-- Prove2me | solution 1 for MarketInterference.FiniteSample.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T08:05:05.826085+00:00
-- url     : https://prove2.me/submissions/4116bb78-2da9-48ce-8599-465ede473786

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory NNReal

lemma l5_shift (r : ℝ≥0) (n : ℕ) :
    Real.exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) / (Nat.factorial (n + 1) : ℕ) * ((n + 1 : ℕ) : ℝ)
      = (r : ℝ) * (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (Nat.factorial n : ℕ)) := by
  rw [Nat.factorial_succ]
  push_cast
  have : ((Nat.factorial n : ℕ) : ℝ) ≠ 0 := by positivity
  have : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

lemma l5_int_iff (r : ℝ≥0) (hr : r ≠ 0) (f : ℕ → ℝ) :
    Integrable (fun d : ℕ => (d : ℝ) * f d) (poissonMeasure r) ↔
      Integrable (fun d : ℕ => f (d + 1)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff, integrable_poissonMeasure_iff]
  refine Iff.trans (_root_.summable_nat_add_iff 1).symm ?_
  have h : ∀ n : ℕ, Real.exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) / (Nat.factorial (n + 1) : ℕ) *
      ‖((n + 1 : ℕ) : ℝ) * f (n + 1)‖
      = (r : ℝ) * (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (Nat.factorial n : ℕ) * ‖f (n + 1)‖) := by
    intro n
    rw [norm_mul, Real.norm_natCast, ← mul_assoc, ← mul_assoc, l5_shift]
  simp only [h]
  exact summable_mul_left_iff (by exact_mod_cast hr)

theorem solution (r : ℝ≥0) (f : ℕ → ℝ) (hf : Integrable f (poissonMeasure r)) :
    ∫ d, (d : ℝ) * f d ∂(poissonMeasure r) = (r : ℝ) * ∫ d, f (d + 1) ∂(poissonMeasure r) := by
  rcases eq_or_ne r 0 with rfl | hr
  · have : ∀ n : ℕ, (Real.exp (-((0 : ℝ≥0) : ℝ)) * ((0 : ℝ≥0) : ℝ) ^ n / (Nat.factorial n : ℕ)) •
        ((n : ℝ) * f n) = 0 := by
      intro n
      cases n <;> simp
    rw [integral_poissonMeasure]
    rw [tsum_congr this]
    simp
  · by_cases h : Integrable (fun d : ℕ => f (d + 1)) (poissonMeasure r)
    · have h2 := (l5_int_iff r hr f).2 h
      rw [integral_poissonMeasure' h2, integral_poissonMeasure' h,
        ← _root_.tsum_mul_left]
      rw [Summable.tsum_eq_zero_add]
      · simp only [smul_eq_mul, Nat.cast_zero, zero_mul, mul_zero, zero_add]
        refine _root_.tsum_congr fun n => ?_
        rw [← mul_assoc, l5_shift]
        ring
      · exact (hasSum_integral_poissonMeasure h2).summable
    · have h2 : ¬ Integrable (fun d : ℕ => (d : ℝ) * f d) (poissonMeasure r) :=
        fun h' => h ((l5_int_iff r hr f).1 h')
      rw [integral_undef h, integral_undef h2]
      simp
