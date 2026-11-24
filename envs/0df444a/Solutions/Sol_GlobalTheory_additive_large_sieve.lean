-- Prove2me | solution 1 for GlobalTheory.additive_large_sieve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:44:40.526188+00:00
-- url     : https://prove2.me/submissions/ea60a137-9fc3-47f3-a38c-d074762ea0d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIntervalIntegralLeOfSpaced
import Theorems.Thm_GlobalTheory_gallagher_interval
import Theorems.Thm_GlobalTheory_norm_expSum_shift
import Theorems.Thm_GlobalTheory_integral_norm_sq_expSum
import Theorems.Thm_GlobalTheory_sum_intervalIntegral_le_of_spaced
import Theorems.Thm_GlobalTheory_expSum_sub_int

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
namespace GlobalTheory
theorem _root_.solution : ∀ (M N : ℕ) (a : ℕ → ℂ) (S : Finset ℝ) (δ : ℝ), 0 < δ → δ ≤ 1 → (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∀ k : ℤ, δ ≤ |x - y - k|) → ∑ x ∈ S, ‖∑ n ∈ Finset.Ioc M (M + N), a n * Complex.exp (2 * Real.pi * I * n * x)‖ ^ 2 ≤ (1 / δ + 2 * Real.pi * N) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  intro M N a S δ hδ hδ1 hS
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rcases S.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
  · simp only [Finset.sum_empty]; positivity
  set s := Finset.Ioc M (M + N) with hs
  set c : ℝ := M + N / 2 with hc
  set L : ℝ := Real.pi * N with hL
  have hL0 : 0 < L := by positivity
  set b : ℕ → ℂ := fun n => a n * (2 * Real.pi * I * ((n : ℂ) - c)) with hb
  set T : ℝ → ℂ := fun t => ∑ n ∈ s, a n * Complex.exp (2 * Real.pi * I * ((n : ℂ) - c) * t) with hT
  set T' : ℝ → ℂ := fun t => ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * ((n : ℂ) - c) * t) with hT'
  have hd : ∀ t, HasDerivAt T (T' t) t := by
    intro t
    apply HasDerivAt.fun_sum
    intro n _
    have h1 : HasDerivAt (fun t : ℝ => 2 * Real.pi * I * ((n : ℂ) - c) * (t : ℂ))
        (2 * Real.pi * I * ((n : ℂ) - c)) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (2 * Real.pi * I * ((n : ℂ) - c))
    exact ((h1.cexp).const_mul (a n)).congr_deriv (by simp only [hb]; ring)
  have hTc : Continuous T := by simp only [hT]; fun_prop
  have hTc' : Continuous T' := by simp only [hT']; fun_prop
  have hG : ∀ x, ‖T x‖ ^ 2 ≤ ∫ t in x..(x + δ), (‖T t‖ ^ 2 / δ + (L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L)) := by
    intro x
    refine gallagher_interval (fun t => ‖T t‖ ^ 2) (fun t => 2 * inner ℝ (T t) (T' t))
      (fun t => L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L) (fun t => (hd t).norm_sq) (by fun_prop) (by fun_prop) ?_ x δ hδ
    intro t
    have h1 := abs_real_inner_le_norm (T t) (T' t)
    rw [abs_mul, abs_two]
    have h2 : L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L - 2 * (‖T t‖ * ‖T' t‖)
        = (L * ‖T t‖ - ‖T' t‖) ^ 2 / L := by field_simp; ring
    have h3 : 0 ≤ (L * ‖T t‖ - ‖T' t‖) ^ 2 / L := by positivity
    linarith
  set p : ℝ → ℝ := fun x => x - (⌊x - y⌋ : ℤ) with hp
  have hsum := sum_intervalIntegral_le_of_spaced
    (fun t => ‖T t‖ ^ 2 / δ + (L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L)) (by fun_prop) (fun t => by positivity)
    S p δ y hδ (fun x _ => by simp only [hp]; linarith [Int.floor_le (x - y)]) ?_ ?_
  · have e1 : ∫ t in y..(y + 1), ‖T t‖ ^ 2 = ∑ n ∈ s, ‖a n‖ ^ 2 := by
      simp only [hT, norm_expSum_shift]; exact integral_norm_sq_expSum s a y
    have e2 : ∫ t in y..(y + 1), ‖T' t‖ ^ 2 = ∑ n ∈ s, ‖b n‖ ^ 2 := by
      simp only [hT', norm_expSum_shift]; exact integral_norm_sq_expSum s b y
    have e3 : ∑ n ∈ s, ‖b n‖ ^ 2 ≤ L ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      rw [hs, Finset.mem_Ioc] at hn
      have hn1 : (M : ℝ) < n := by exact_mod_cast hn.1
      have hn2 : (n : ℝ) ≤ M + N := by exact_mod_cast hn.2
      have h4 : ‖(n : ℂ) - c‖ ≤ N / 2 := by
        rw [show (n : ℂ) - c = ((n - c : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_le]
        constructor <;> linarith
      have h5 : ‖b n‖ ≤ L * ‖a n‖ := by
        simp only [hb, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos, Complex.norm_ofNat]
        calc ‖a n‖ * (2 * Real.pi * 1 * ‖(n : ℂ) - c‖) ≤ ‖a n‖ * (2 * Real.pi * 1 * (N / 2)) := by
              gcongr
          _ = L * ‖a n‖ := by rw [hL]; ring
      rw [← mul_pow]
      gcongr
    have e4 : ∫ t in y..(y + 1), (‖T t‖ ^ 2 / δ + (L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L))
        = (∑ n ∈ s, ‖a n‖ ^ 2) / δ + (L * ∑ n ∈ s, ‖a n‖ ^ 2 + (∑ n ∈ s, ‖b n‖ ^ 2) / L) := by
      rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
        intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_div,
        intervalIntegral.integral_div, intervalIntegral.integral_const_mul, e1, e2]
    have e5 : (∑ n ∈ s, ‖b n‖ ^ 2) / L ≤ L * ∑ n ∈ s, ‖a n‖ ^ 2 := by
      rw [div_le_iff₀ hL0]; nlinarith
    calc _ = ∑ x ∈ S, ‖T (p x)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [hT, hp]
          rw [norm_expSum_shift, expSum_sub_int]
      _ ≤ _ := Finset.sum_le_sum fun x _ => hG (p x)
      _ ≤ _ := hsum
      _ = _ := e4
      _ ≤ (∑ n ∈ s, ‖a n‖ ^ 2) / δ + (L * ∑ n ∈ s, ‖a n‖ ^ 2 + L * ∑ n ∈ s, ‖a n‖ ^ 2) := by
          linarith
      _ = _ := by rw [hL]; ring
  · intro x hx
    simp only [hp]
    by_cases hxy : x = y
    · subst hxy; simp [hδ1]
    · have h1 := hS x hx y hy hxy (⌊x - y⌋ + 1)
      have h2 := Int.lt_floor_add_one (x - y)
      push_cast at h1
      rw [abs_of_neg (by linarith)] at h1
      linarith
  · intro x hx z hz hxz
    have h1 := hS x hx z hz hxz (⌊x - y⌋ - ⌊z - y⌋)
    simp only [hp]
    convert h1 using 2
    push_cast; ring
end GlobalTheory
