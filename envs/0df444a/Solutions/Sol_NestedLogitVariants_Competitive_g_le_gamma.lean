-- Prove2me | solution 1 for NestedLogitVariants.Competitive.g_le_gamma
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T02:07:37.533354+00:00
-- url     : https://prove2.me/submissions/61db4f0b-e903-4aed-96ab-9a7cf173eb58

import Mathlib
import Definitions.Def_NestedLogitVariants_Competitive_Model

open NestedLogitVariants.Competitive in
theorem solution (γ α : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hα0 : 0 < α) (hα1 : α < 1) :
    (1 - α ^ γ) / (α ^ (γ - 1) - α ^ γ) ≤ γ := by
  have ha : 0 < α ^ γ := Real.rpow_pos_of_pos hα0 γ
  have hsub : α ^ (γ - 1) = α ^ γ / α := Real.rpow_sub_one hα0.ne' γ
  have hb := rpow_one_add_le_one_add_mul_self (s := α⁻¹ - 1)
    (by have := inv_pos.mpr hα0; linarith) hγ0.le hγ1
  rw [show (1 : ℝ) + (α⁻¹ - 1) = α⁻¹ by ring, Real.inv_rpow hα0.le] at hb
  have hden : 0 < α ^ γ / α - α ^ γ := by
    rw [sub_pos, lt_div_iff₀ hα0]; nlinarith
  rw [hsub, div_le_iff₀ hden]
  have h1 : 1 ≤ α ^ γ * (1 + γ * (α⁻¹ - 1)) := by
    have := mul_le_mul_of_nonneg_left hb ha.le
    rwa [mul_inv_cancel₀ ha.ne'] at this
  have h2 : α ^ γ * (1 + γ * (α⁻¹ - 1)) = α ^ γ + γ * (α ^ γ / α - α ^ γ) := by
    rw [div_eq_mul_inv]; ring
  linarith
