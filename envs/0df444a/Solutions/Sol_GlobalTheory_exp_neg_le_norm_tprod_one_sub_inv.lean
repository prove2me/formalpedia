-- Prove2me | solution 1 for GlobalTheory.exp_neg_le_norm_tprod_one_sub_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:41:26.508326+00:00
-- url     : https://prove2.me/submissions/77e57a0a-5492-4863-af0d-a70911e4edb3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExpNegLeNormTprodOneSubInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory IsDedekindDomain NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {ι : Type} (x : ι → ℂ) (B : ℝ)
    (h : ∀ a, ‖x a‖ ≤ 1 / 2) (hs : Summable (fun a => ‖x a‖)) (hB : ∑' a, ‖x a‖ ≤ B) :
    Real.exp (-B) ≤ ‖∏' a, (1 - x a)⁻¹‖ := by
  have hlow : ∀ a, 1 / 2 ≤ ‖1 - x a‖ := by
    intro a
    have h1 := norm_sub_norm_le (1 : ℂ) (x a)
    rw [norm_one] at h1
    linarith [h a]
  have hne : ∀ a, 1 - x a ≠ 0 := by
    intro a h0
    have := hlow a
    rw [h0, norm_zero] at this
    linarith
  have heq : ∀ a, (1 - x a)⁻¹ = 1 + x a * (1 - x a)⁻¹ := by
    intro a
    have := hne a
    field_simp
    ring
  have hsum : Summable (fun a => ‖x a * (1 - x a)⁻¹‖) := by
    refine Summable.of_nonneg_of_le (fun a => norm_nonneg _) (fun a => ?_) (hs.mul_right 2)
    rw [norm_mul, norm_inv]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [inv_le_comm₀ (by linarith [hlow a]) (by norm_num)]
    linarith [hlow a]
  have hm : Multipliable (fun a => (1 - x a)⁻¹) := by
    have := multipliable_one_add_of_summable hsum
    simpa only [← heq] using this
  have hfac : ∀ a, Real.exp (-‖x a‖) ≤ ‖(1 - x a)⁻¹‖ := by
    intro a
    rw [norm_inv, Real.exp_neg]
    refine inv_anti₀ (by linarith [hlow a]) ?_
    have h1 := norm_sub_le (1 : ℂ) (x a)
    rw [norm_one] at h1
    linarith [Real.add_one_le_exp ‖x a‖]
  have ht := (continuous_norm.tendsto _).comp hm.hasProd
  refine ge_of_tendsto' ht (fun s => ?_)
  have hsle : ∑ a ∈ s, ‖x a‖ ≤ B :=
    (hs.sum_le_tsum s (fun a _ => norm_nonneg _)).trans hB
  calc Real.exp (-B) ≤ Real.exp (∑ a ∈ s, -‖x a‖) := by
        rw [Finset.sum_neg_distrib]
        exact Real.exp_le_exp.2 (neg_le_neg hsle)
    _ = ∏ a ∈ s, Real.exp (-‖x a‖) := Real.exp_sum _ _
    _ ≤ ∏ a ∈ s, ‖(1 - x a)⁻¹‖ :=
        Finset.prod_le_prod (fun a _ => (Real.exp_pos _).le) (fun a _ => hfac a)
    _ = _ := by simp only [Function.comp, norm_prod]
end GlobalTheory
