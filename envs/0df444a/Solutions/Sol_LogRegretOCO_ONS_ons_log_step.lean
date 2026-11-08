-- Prove2me | solution 1 for LogRegretOCO.ONS.ons_log_step
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:24:53.608803+00:00
-- url     : https://prove2.me/submissions/5c4b6038-5c0c-4507-8e16-f5caacbbb18e

import Mathlib
import Definitions.Def_LogRegretOCO_ONS_onsBeta

open LogRegretOCO.ONS in
theorem solution {n : ℕ} {G D α : ℝ} (hG : 0 < G) (hD : 0 < D) (hα : 0 < α) :
    ∀ T : ℕ, 2 ≤ T →
      n / (2 * onsBeta G D α) * Real.log (T * G ^ 2 * onsBeta G D α ^ 2 * D ^ 2 + 1)
        ≤ n / (2 * onsBeta G D α) * Real.log T := by
  intro T hT
  have hGD : 0 < G * D := mul_pos hG hD
  have hβ0 : 0 < onsBeta G D α := by
    unfold onsBeta
    have : 0 < min (1 / (4 * G * D)) α := lt_min (by positivity) hα
    linarith
  have hβle : G * D * onsBeta G D α ≤ 1 / 8 := by
    unfold onsBeta
    have hm := min_le_left (1 / (4 * G * D)) α
    have e : G * D * (1 / (4 * G * D)) = 1 / 4 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hm hGD.le]
  have hT' : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hsq : (G * D * onsBeta G D α) ^ 2 ≤ 1 / 64 := by
    have h0 : 0 ≤ G * D * onsBeta G D α := by positivity
    nlinarith
  have key : (T : ℝ) * G ^ 2 * onsBeta G D α ^ 2 * D ^ 2 ≤ T / 64 := by
    have e : (T : ℝ) * G ^ 2 * onsBeta G D α ^ 2 * D ^ 2 = T * (G * D * onsBeta G D α) ^ 2 := by
      ring
    rw [e]
    have : (0 : ℝ) ≤ T := by linarith
    nlinarith
  have hx0 : 0 ≤ (T : ℝ) * G ^ 2 * onsBeta G D α ^ 2 * D ^ 2 := by positivity
  have hlog : Real.log ((T : ℝ) * G ^ 2 * onsBeta G D α ^ 2 * D ^ 2 + 1) ≤ Real.log T :=
    Real.log_le_log (by linarith) (by linarith)
  exact mul_le_mul_of_nonneg_left hlog (div_nonneg (Nat.cast_nonneg n) (by positivity))
