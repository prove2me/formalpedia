-- Prove2me | solution 1 for HessianDamping.IGAHD.tK_facts
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:22:36.456837+00:00
-- url     : https://prove2.me/submissions/27b9c273-f9ef-443c-b843-c129f70e2cb3

import Mathlib
import Definitions.Def_HessianDamping_IGAHD_Setting
set_option autoImplicit false
open HessianDamping.IGAHD

theorem solution (α : ℝ) (hα : 3 ≤ α) (k : ℕ) (hk : 1 ≤ k) :
    tK α k = 1 + tK α (k + 1) * (1 - α / (k : ℝ)) ∧
    tK α (k + 1) ^ 2 - tK α (k + 1) - tK α k ^ 2 ≤ 0 := by
  have hα1 : 0 < α - 1 := by linarith
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (k : ℝ) ≠ 0 := by positivity
  unfold tK
  push_cast
  constructor
  · field_simp
    ring
  · have e : (((k : ℝ) + 1 - 1) / (α - 1)) ^ 2 - ((k : ℝ) + 1 - 1) / (α - 1) - (((k : ℝ) - 1) / (α - 1)) ^ 2
        = (3 * k - 1 - k * α) / (α - 1) ^ 2 := by
      field_simp
      ring
    rw [e]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    nlinarith
