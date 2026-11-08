-- Prove2me | solution 1 for ImbalPricing.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:42:40.695508+00:00
-- url     : https://prove2.me/submissions/3a555a26-80b7-4de2-8bdc-813a5ee0af08

import Mathlib
import Definitions.Def_ImbalPricing_HCGCost

namespace Aux_ImbalPricing_eq_4

lemma closed (α₁ α₂ H₁ H₂ : ℝ) :
    ImbalPricing.hcgCost α₁ α₂ H₁ H₂ = α₁ * H₁ ^ 2 / 2 + α₁ * H₁ * H₂ + α₂ * H₂ ^ 2 / 2 := by
  unfold ImbalPricing.hcgCost
  rw [intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_add,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub, integral_id, intervalIntegral.integral_const]
  · simp only [smul_eq_mul]; ring
  all_goals (apply Continuous.intervalIntegrable; fun_prop)

end Aux_ImbalPricing_eq_4

open ImbalPricing in
theorem solution (α₁ α₂ H₁ H₂ : ℝ) :
    dwl α₁ α₂ H₁ H₂ = (α₂ - α₁) * H₂ ^ 2 / 2 ∧
      (α₁ ≤ α₂ → hcgCost α₁ α₂ (H₁ + H₂) 0 ≤ hcgCost α₁ α₂ H₁ H₂) := by
  have hd : dwl α₁ α₂ H₁ H₂ = (α₂ - α₁) * H₂ ^ 2 / 2 := by
    unfold dwl
    rw [Aux_ImbalPricing_eq_4.closed, Aux_ImbalPricing_eq_4.closed]
    ring
  refine ⟨hd, fun h => ?_⟩
  have : 0 ≤ (α₂ - α₁) * H₂ ^ 2 / 2 := by
    apply div_nonneg _ (by norm_num)
    exact mul_nonneg (by linarith) (sq_nonneg _)
  unfold dwl at hd
  linarith
