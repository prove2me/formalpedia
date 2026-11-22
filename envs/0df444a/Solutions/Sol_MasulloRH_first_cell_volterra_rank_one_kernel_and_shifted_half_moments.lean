-- Prove2me | solution 1 for MasulloRH.first_cell_volterra_rank_one_kernel_and_shifted_half_moments
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T19:07:40.932897+00:00
-- url     : https://prove2.me/submissions/a831fa45-9eaf-46c3-a171-e48343ea9526

import Mathlib
open MeasureTheory
theorem solution (p : ℝ) (hp : 1 < p) (f : ℝ → ℝ) (hf : Continuous f) :
    (∀ x ∈ Set.Icc 0 (Real.log p), ∀ y ∈ Set.Icc 0 (Real.log p),
      Real.exp (|x-y|/2) + (∫ t in (0:ℝ)..min x y,
        Real.exp ((x-t)/2) * Real.exp ((y-t)/2)) =
      Real.exp (x/2) * Real.exp (y/2)) ∧
    (1/p) * (∫ s in (0:ℝ)..Real.log p,
      f s * (∫ x in s..Real.log p, Real.exp ((x-s)/2) * Real.exp (x/2))) =
      (∫ s in (0:ℝ)..Real.log p, f s * Real.exp (-s/2)) -
      (1/p) * (∫ s in (0:ℝ)..Real.log p, f s * Real.exp (s/2)) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  constructor
  · intro x hx y hy
    have hrew (t : ℝ) : Real.exp ((x-t)/2) * Real.exp ((y-t)/2) =
        Real.exp ((x+y)/2 - t) := by
      rw [← Real.exp_add]
      congr 1 <;> ring
    simp_rw [hrew]
    rw [intervalIntegral.integral_comp_sub_left Real.exp, integral_exp, sub_zero,
      ← Real.exp_add]
    have heq : (x+y)/2 - min x y = |x-y|/2 := by
      rcases le_total x y with h | h
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
        ring
      · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
        ring
    rw [heq, show x / 2 + y / 2 = (x+y)/2 by ring]
    ring
  · have hcell (s : ℝ) : (∫ x in s..Real.log p,
          Real.exp ((x-s)/2) * Real.exp (x/2)) =
        p * Real.exp (-s/2) - Real.exp (s/2) := by
      have hrew (x : ℝ) : Real.exp ((x-s)/2) * Real.exp (x/2) =
          Real.exp (-s/2) * Real.exp x := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1 <;> ring
      simp_rw [hrew]
      rw [intervalIntegral.integral_const_mul, integral_exp, Real.exp_log hp0,
        mul_sub, ← Real.exp_add, show -s/2+s=s/2 by ring]
      ring
    simp_rw [hcell]
    have hrew (s : ℝ) : f s * (p * Real.exp (-s/2) - Real.exp (s/2)) =
        p * (f s * Real.exp (-s/2)) - f s * Real.exp (s/2) := by ring
    simp_rw [hrew]
    have c₁ : Continuous (fun s : ℝ => p * (f s * Real.exp (-s/2))) := by fun_prop
    have c₂ : Continuous (fun s : ℝ => f s * Real.exp (s/2)) := by fun_prop
    rw [intervalIntegral.integral_sub (c₁.intervalIntegrable _ _) (c₂.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul]
    field_simp
