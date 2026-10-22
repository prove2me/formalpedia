-- Prove2me | solution 1 for LSWCuttingPlane.ChasingZero.alpha_choice
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:30:08.543594+00:00
-- url     : https://prove2.me/submissions/3c8d1fc8-5305-403e-89be-0c2bc5ebd197

import Mathlib
import Definitions.Def_LSWCuttingPlane_ChasingZero_Setting

set_option autoImplicit false

theorem solution (c R α : ℝ) (hc : 0 < c) (hR : 0 < R) (hα : α = 1 / (2 * (c + R))) :
    Real.exp (2 * α * (c + R)) * (α * (c + R)) ^ 2 ≤ 1 ∧
      α ^ 2 * Real.exp (α * c) * c ^ 2 ≤ Real.exp (-(α * (R + c))) := by
  have hcR : 0 < c + R := by linarith
  have h1 : α * (c + R) = 1 / 2 := by
    rw [hα]; field_simp
  have h1' : α * (R + c) = 1 / 2 := by rw [add_comm]; exact h1
  have hαpos : 0 < α := by rw [hα]; positivity
  have he : Real.exp 1 < 4 := by
    have := Real.exp_one_lt_d9; linarith
  have hhalf : Real.exp (1/2) * Real.exp (1/2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have hpos : 0 < Real.exp (1/2) := Real.exp_pos _
  refine ⟨?_, ?_⟩
  · have : 2 * α * (c + R) = 1 := by
      have : 2 * α * (c + R) = 2 * (α * (c + R)) := by ring
      rw [this, h1]; norm_num
    rw [this, h1]
    nlinarith
  · rw [h1']
    set x := α * c with hx
    have hx0 : 0 < x := mul_pos hαpos hc
    have hxle : x ≤ 1 / 2 := by
      have : α * c ≤ α * (c + R) := by nlinarith
      linarith
    have hsq : α ^ 2 * c ^ 2 = x ^ 2 := by rw [hx]; ring
    have : α ^ 2 * Real.exp x * c ^ 2 = Real.exp x * x ^ 2 := by rw [← hsq]; ring
    rw [this]
    have h2 : Real.exp x * x ^ 2 ≤ Real.exp (1/2) * (1/4) := by
      apply mul_le_mul (Real.exp_le_exp.2 hxle) _ (by positivity) hpos.le
      nlinarith
    have h3 : Real.exp (-(1/2:ℝ)) * Real.exp (1/2) = 1 := by
      rw [← Real.exp_add]; norm_num
    have h4 : Real.exp (1/2) * (1/4) ≤ Real.exp (-(1/2:ℝ)) := by
      have hneg : 0 < Real.exp (-(1/2:ℝ)) := Real.exp_pos _
      nlinarith
    linarith
