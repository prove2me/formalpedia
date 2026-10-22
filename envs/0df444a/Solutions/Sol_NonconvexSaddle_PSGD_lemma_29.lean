-- Prove2me | solution 1 for NonconvexSaddle.PSGD.lemma_29
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:39:46.280286+00:00
-- url     : https://prove2.me/submissions/c1c079d2-b3ca-46ee-a396-6793079f5f24

import Mathlib
import Definitions.Def_NonconvexSaddle_PSGD_Setting
set_option autoImplicit false
open NonconvexSaddle.PSGD

theorem ww_geom (a : ℝ) (ha : 0 < a) (t : ℕ) :
    ∑ τ ∈ Finset.range t, (1 + a) ^ (2 * (t - 1 - τ)) = ((1 + a) ^ (2 * t) - 1) / (a * (2 + a)) := by
  have h1 : ∑ τ ∈ Finset.range t, (1 + a) ^ (2 * (t - 1 - τ))
      = ∑ k ∈ Finset.range t, ((1 + a) ^ 2) ^ k := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have : t - 1 - (t - 1 - k) = k := by omega
    rw [this, pow_mul]
  rw [h1, geom_sum_eq]
  · rw [← pow_mul]
    have : (1 + a) ^ 2 - 1 = a * (2 + a) := by ring
    rw [this]
  · intro h
    have : (1 + a) ^ 2 - 1 = 0 := by rw [h]; ring
    nlinarith

theorem solution (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (∀ t : ℕ, alphaL a t ≤ betaL a t) ∧
      ∀ t : ℕ, Real.log 2 / a ≤ (t : ℝ) → betaL a t / Real.sqrt 3 ≤ alphaL a t := by
  have h2a : (0 : ℝ) < 2 * a := by linarith
  have hsq : ∀ t : ℕ, (betaL a t) ^ 2 = (1 + a) ^ (2 * t) / (2 * a) := by
    intro t
    unfold betaL
    rw [div_pow, Real.sq_sqrt h2a.le, ← pow_mul, mul_comm t 2]
  have hβ0 : ∀ t : ℕ, 0 ≤ betaL a t := by
    intro t
    unfold betaL
    positivity
  constructor
  · intro t
    unfold alphaL
    rw [Real.sqrt_le_iff]
    refine ⟨hβ0 t, ?_⟩
    rw [hsq t, ww_geom a ha t]
    have hP : 0 < (1 + a) ^ (2 * t) := by positivity
    rw [div_le_div_iff₀ (by positivity) h2a]
    nlinarith [mul_pos ha hP]
  · intro t ht
    unfold alphaL
    have hP2 : 2 ≤ (1 + a) ^ (2 * t) := by
      have hlog : Real.log (1 + a) ≥ a / 2 := by
        have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 + a by linarith)
        have h3 : a / 2 ≤ 1 - (1 + a)⁻¹ := by
          have : 1 - (1 + a)⁻¹ = a / (1 + a) := by field_simp; ring
          rw [this, div_le_div_iff₀ (by norm_num) (by linarith)]
          nlinarith
        linarith
      have h4 : Real.log 2 ≤ (2 * t : ℝ) * Real.log (1 + a) := by
        have h5 : Real.log 2 ≤ t * a := by
          rw [div_le_iff₀ ha] at ht
          exact ht
        have h6 : (t : ℝ) * (a / 2) ≤ t * Real.log (1 + a) :=
          mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg t)
        nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num), Nat.cast_nonneg (α := ℝ) t]
      have h7 : Real.log 2 ≤ Real.log ((1 + a) ^ (2 * t)) := by
        rw [Real.log_pow]
        push_cast
        exact h4
      exact (Real.log_le_log_iff (by norm_num) (by positivity)).1 h7
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 3)]
    have hS : 0 ≤ ∑ τ ∈ Finset.range t, (1 + a) ^ (2 * (t - 1 - τ)) :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    have key : (betaL a t) ^ 2 ≤ (Real.sqrt (∑ τ ∈ Finset.range t, (1 + a) ^ (2 * (t - 1 - τ))) *
        Real.sqrt 3) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hS, Real.sq_sqrt (by norm_num), hsq t, ww_geom a ha t]
      rw [div_le_iff₀ h2a]
      have hP : 0 < (1 + a) ^ (2 * t) := by positivity
      have e : ((1 + a) ^ (2 * t) - 1) / (a * (2 + a)) * 3 * (2 * a)
          = 6 * ((1 + a) ^ (2 * t) - 1) / (2 + a) := by
        field_simp
        ring
      rw [e, le_div_iff₀ (by linarith)]
      nlinarith
    exact abs_le_of_sq_le_sq' (by simpa using key) (by positivity) |>.2
