-- Prove2me | solution 1 for GlobalTheory.ThetaGauss.eq_exp_of_ode
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:02:46.543245+00:00
-- url     : https://prove2.me/submissions/5c900305-e760-4695-b451-1803508aaff5

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Theorems.Thm_GlobalTheory_ThetaGauss_transl_apply
import Theorems.Thm_GlobalTheory_ThetaGauss_not_eventually_zero
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk


attribute [local simp] GlobalTheory.ThetaGauss.transl_apply

set_option autoImplicit false
open Matrix Filter Topology Metric
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaGauss
variable {g : ℕ}
namespace GlobalTheory.ThetaGauss
theorem _root_.solution {h h₁ h₂ : ℂ → ℂ} (hd : ∀ t, HasDerivAt h (h₁ t) t)
    (hd₁ : ∀ t, HasDerivAt h₁ (h₂ t) t) (c : ℂ) (he : ∀ t, h t * h₂ t - h₁ t ^ 2 = c * h t ^ 2)
    (h0 : h 0 ≠ 0) : ∃ α : ℂ, ∀ t, h t = h 0 * Complex.exp (α * t + c / 2 * t ^ 2) := by
  have hh : Differentiable ℂ h := fun t => (hd t).differentiableAt
  have hh₁ : Differentiable ℂ h₁ := fun t => (hd₁ t).differentiableAt
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff_ball.1 ((hh 0).continuousAt.eventually_ne h0)
  have hq : ∀ t ∈ ball (0 : ℂ) ε, HasDerivAt (fun t => h₁ t / h t - c * t) 0 t := fun t ht => by
    have := ((hd₁ t).div (hd t) (hb t ht)).sub ((hasDerivAt_id t).const_mul c)
    refine this.congr_deriv ?_
    have := hb t ht
    field_simp
    linear_combination he t
  refine ⟨h₁ 0 / h 0, ?_⟩
  set α := h₁ 0 / h 0 with hα
  have hc : ∀ t ∈ ball (0 : ℂ) ε, h₁ t / h t - c * t = α := fun t ht => by
    have := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ _).isPreconnected
      (fun t ht => (hq t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hq t ht).deriv) ht (mem_ball_self hε)
    simpa using this
  have h1 : ∀ t, h₁ t - (α + c * t) * h t = 0 := by
    by_contra hn
    push_neg at hn
    refine not_eventually_zero (by fun_prop) hn 0 ?_
    filter_upwards [ball_mem_nhds 0 hε] with t ht
    rw [← hc t ht, sub_add_cancel, div_mul_cancel₀ _ (hb t ht), sub_self]
  have h2 : ∀ t, HasDerivAt (fun t => h t * Complex.exp (-(α * t + c / 2 * t ^ 2))) 0 t := fun t => by
    have := (hd t).mul ((((hasDerivAt_id t).const_mul α).add
      (((hasDerivAt_id t).pow 2).const_mul (c / 2))).neg.cexp)
    refine this.congr_deriv ?_
    simp only [id, Pi.neg_apply, Pi.add_apply, Pi.pow_apply]
    push_cast
    linear_combination Complex.exp (-(α * t + c / 2 * t ^ 2)) * h1 t
  intro t
  have := is_const_of_deriv_eq_zero (fun t => (h2 t).differentiableAt) (fun t => (h2 t).deriv) t 0
  simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, neg_zero,
    Complex.exp_zero, mul_one] at this
  rw [← this, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
end GlobalTheory.ThetaGauss
