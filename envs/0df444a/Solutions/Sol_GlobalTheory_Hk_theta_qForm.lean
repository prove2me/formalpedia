-- Prove2me | solution 1 for GlobalTheory.Hk.theta_qForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:55:57.309962+00:00
-- url     : https://prove2.me/submissions/8f2c61e6-6d31-4b20-aed4-dc03d3aff785

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableExpNegMulSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ThetaQForm
import Theorems.Thm_GlobalTheory_Hk_tsum_prod_weight_approx
import Theorems.Thm_GlobalTheory_ShiftedTheta_shifted_theta_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk
namespace GlobalTheory.Hk
theorem _root_.solution : ∀ α γ l θ₁ θ₂ t : ℝ, 0 < α → 0 < γ → 0 < t → Summable (fun v : ℤ × ℤ => Real.exp (-(t * qForm α γ l θ₁ θ₂ v))) ∧ |∑' v : ℤ × ℤ, Real.exp (-(t * qForm α γ l θ₁ θ₂ v)) - Real.pi / Real.sqrt (α * γ) / t| ≤ Real.pi / Real.sqrt (α * γ) / t * ((α * t) ^ 2 + (γ * t) ^ 2 + (α * t) ^ 2 * (γ * t) ^ 2) := by
  intro α γ l θ₁ θ₂ t hα hγ ht
  have h := tsum_prod_weight_approx
    (fun (m : ℤ) (k : ℤ) => Real.exp (-((α * t) * (m + (θ₁ + l * k)) ^ 2)))
    (fun k : ℤ => Real.exp (-((γ * t) * (k + θ₂) ^ 2)))
    (Real.sqrt (Real.pi / (α * t))) ((α * t) ^ 2) (Real.sqrt (Real.pi / (γ * t))) ((γ * t) ^ 2)
    (Real.sqrt_nonneg _) (sq_nonneg _) (fun _ _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
    (fun k => GlobalTheory.ShiftedTheta.shifted_theta_bound (α * t) (θ₁ + l * k) (mul_pos hα ht))
    (GlobalTheory.ShiftedTheta.shifted_theta_bound (γ * t) θ₂ (mul_pos hγ ht))
  have e1 : (fun v : ℤ × ℤ => Real.exp (-(t * qForm α γ l θ₁ θ₂ v))) =
      fun v : ℤ × ℤ => Real.exp (-((α * t) * (v.1 + (θ₁ + l * v.2)) ^ 2)) *
        Real.exp (-((γ * t) * (v.2 + θ₂) ^ 2)) := by
    funext v
    rw [← Real.exp_add]
    congr 1
    unfold qForm
    ring
  have e2 : Real.pi / Real.sqrt (α * γ) / t =
      Real.sqrt (Real.pi / (α * t)) * Real.sqrt (Real.pi / (γ * t)) := by
    have hp := Real.pi_pos
    rw [← Real.sqrt_mul (by positivity)]
    symm
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    have hs : Real.sqrt (α * γ) * Real.sqrt (α * γ) = α * γ := Real.mul_self_sqrt (by positivity)
    have hs0 : 0 < Real.sqrt (α * γ) := Real.sqrt_pos.mpr (by positivity)
    rw [div_div, div_mul_div_comm, div_mul_div_comm]
    congr 1
    linear_combination -t ^ 2 * hs
  rw [e1, e2]
  exact h
end GlobalTheory.Hk
