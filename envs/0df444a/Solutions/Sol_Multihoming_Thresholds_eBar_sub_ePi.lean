-- Prove2me | solution 1 for Multihoming.Thresholds.eBar_sub_ePi
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:05:53.417128+00:00
-- url     : https://prove2.me/submissions/4e9baed2-b1a1-47c8-9697-4ad3bd0cb7fe

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

theorem solution (t μ : ℝ) (ht : 0 < t) (hμ : 0 ≤ μ) (hμt : μ < t) :
    eBar t μ - ePi t μ =
      (2 * t - μ) * (μ ^ 3 - t * μ ^ 2 + 2 * t ^ 3 - 2 * t ^ 2 * Real.sqrt (t ^ 2 - μ ^ 2)) /
        (t * (4 * t ^ 2 - 3 * t * μ + μ ^ 2)) := mt_sub t μ ht hμ hμt
