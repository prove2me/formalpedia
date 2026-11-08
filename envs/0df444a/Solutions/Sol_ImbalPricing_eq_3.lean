-- Prove2me | solution 1 for ImbalPricing.eq_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:00:22.679136+00:00
-- url     : https://prove2.me/submissions/da90f8cf-a941-4800-8186-ffd13ad8dae8

import Mathlib
import Definitions.Def_ImbalPricing_HCGCost

open ImbalPricing in
theorem solution (α₁ α₂ H₁ H₂ : ℝ) :
    ImbalPricing.hcgCost α₁ α₂ H₁ H₂ = α₁ * (H₁ + H₂) ^ 2 / 2 + (α₂ - α₁) * H₂ ^ 2 / 2 := by
  unfold ImbalPricing.hcgCost
  have i1 : IntervalIntegrable (fun _ : ℝ => α₁ * H₁) MeasureTheory.volume H₁ (H₁ + H₂) :=
    intervalIntegrable_const
  have i2 : IntervalIntegrable (fun h : ℝ => α₂ * (h - H₁)) MeasureTheory.volume H₁ (H₁ + H₂) := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add i1 i2,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (fun x => x), integral_id, integral_id, smul_eq_mul]
  ring
