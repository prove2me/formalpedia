-- Prove2me | solution 1 for Kyprianou.Ch01.finitePositiveSupportDiscountIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:01:30.097081+00:00
-- url     : https://prove2.me/submissions/24904d8a-b099-4f62-b01b-b096e83709a2

import Mathlib.MeasureTheory.Integral.IntegrableOn
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (mu : Measure ℝ)
    (hfin : mu Set.univ < ∞)
    (hsupp : ∀ᵐ x ∂mu, 0 ≤ x)
    (q : ℝ) (hq : 0 ≤ q) :
    Integrable (fun x : ℝ => Real.exp (-q * x)) mu := by
  letI : IsFiniteMeasure mu := ⟨hfin⟩
  have hf : Measurable (fun x : ℝ => Real.exp (-q * x)) := by
    fun_prop
  apply Integrable.of_bound hf.aestronglyMeasurable 1
  filter_upwards [hsupp] with x hx
  have hle : -q * x ≤ 0 := by
    simpa only [neg_mul] using (neg_nonpos.mpr (mul_nonneg hq hx))
  have hExp : Real.exp (-q * x) ≤ 1 := Real.exp_le_one_iff.mpr hle
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hExp
