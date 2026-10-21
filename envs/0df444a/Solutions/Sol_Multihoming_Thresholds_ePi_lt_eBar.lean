-- Prove2me | solution 1 for Multihoming.Thresholds.ePi_lt_eBar
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:05:54.635482+00:00
-- url     : https://prove2.me/submissions/1dc4d0b9-576f-45f9-9fae-d7c9a1b86406

import Mathlib
import Definitions.Def_Multihoming_Thresholds_Model
set_option autoImplicit false


open Multihoming.Thresholds

lemma mt_D_pos (t μ : ℝ) (ht : 0 < t) (hμ : 0 ≤ μ) (hμt : μ < t) : 0 < 4 * t ^ 2 - 3 * t * μ + μ ^ 2 := by
  nlinarith [sq_nonneg (2 * t - 3 * μ / 4), sq_nonneg μ]

lemma mt_sub (t μ : ℝ) (ht : 0 < t) (hμ : 0 ≤ μ) (hμt : μ < t) :
    eBar t μ - ePi t μ =
      (2 * t - μ) * (μ ^ 3 - t * μ ^ 2 + 2 * t ^ 3 - 2 * t ^ 2 * Real.sqrt (t ^ 2 - μ ^ 2)) /
        (t * (4 * t ^ 2 - 3 * t * μ + μ ^ 2)) := by
  have hD := (mt_D_pos t μ ht hμ hμt).ne'
  have ht' : t ≠ 0 := ht.ne'
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = 4 * t ^ 2 - 3 * t * μ + μ ^ 2 := ⟨_, rfl⟩
  rw [← hDdef] at hD ⊢
  unfold eBar ePi
  rw [← hDdef]
  field_simp
  rw [hDdef]
  ring

theorem solution (t μ : ℝ) (ht : 0 < t) (hμ : 0 < μ) (hμt : μ < t) :
    0 < 4 * t ^ 2 - 3 * t * μ + μ ^ 2 ∧
    (μ ^ 3 - t * μ ^ 2 + 2 * t ^ 3) ^ 2 - 4 * t ^ 4 * (-μ ^ 2 + t ^ 2) =
      μ ^ 3 * (t + μ) * (4 * t ^ 2 - 3 * t * μ + μ ^ 2) ∧
    ePi t μ < eBar t μ := by
  have hD := mt_D_pos t μ ht hμ.le hμt
  refine ⟨hD, by ring, ?_⟩
  have hsub := mt_sub t μ ht hμ.le hμt
  have hS : Real.sqrt (t ^ 2 - μ ^ 2) ^ 2 = t ^ 2 - μ ^ 2 :=
    Real.sq_sqrt (by nlinarith)
  have hS0 : 0 ≤ Real.sqrt (t ^ 2 - μ ^ 2) := Real.sqrt_nonneg _
  have hL : 0 < μ ^ 3 - t * μ ^ 2 + 2 * t ^ 3 := by
    have : 0 < μ ^ 3 := by positivity
    nlinarith [mul_pos ht (show 0 < 2 * t ^ 2 - μ ^ 2 by nlinarith)]
  have hsq : (2 * t ^ 2 * Real.sqrt (t ^ 2 - μ ^ 2)) ^ 2 < (μ ^ 3 - t * μ ^ 2 + 2 * t ^ 3) ^ 2 := by
    have e : (2 * t ^ 2 * Real.sqrt (t ^ 2 - μ ^ 2)) ^ 2 = 4 * t ^ 4 * (t ^ 2 - μ ^ 2) := by
      rw [mul_pow, hS]; ring
    rw [e]
    have : 0 < μ ^ 3 * (t + μ) * (4 * t ^ 2 - 3 * t * μ + μ ^ 2) := by positivity
    nlinarith
  have hlt : 2 * t ^ 2 * Real.sqrt (t ^ 2 - μ ^ 2) < μ ^ 3 - t * μ ^ 2 + 2 * t ^ 3 := by
    by_contra hcon
    replace hcon := not_lt.mp hcon
    have := pow_le_pow_left₀ hL.le hcon 2
    linarith
  have : 0 < eBar t μ - ePi t μ := by
    rw [hsub]
    apply div_pos
    · apply mul_pos (by linarith) (by linarith)
    · positivity
  linarith
