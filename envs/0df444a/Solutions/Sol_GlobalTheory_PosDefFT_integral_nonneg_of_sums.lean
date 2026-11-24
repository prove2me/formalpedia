-- Prove2me | solution 1 for GlobalTheory.PosDefFT.integral_nonneg_of_sums
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:42:38.311198+00:00
-- url     : https://prove2.me/submissions/d858781c-cae2-4e21-83e3-e495b37661a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegralNonnegOfSums
import Theorems.Thm_GlobalTheory_PosDefFT_integral_prod_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ComplexOrder
open GlobalTheory GlobalTheory.PosDefFT
namespace GlobalTheory.PosDefFT
theorem _root_.solution (ψ : ℝ → ℂ) (hc : Continuous ψ) (C : ℝ) (hb : ∀ s, ‖ψ s‖ ≤ C)
    (hi : Integrable ψ)
    (hp : ∀ (k : ℕ) (t : Fin k → ℝ), 0 ≤ ∑ i, ∑ j, ψ (t j - t i)) :
    0 ≤ ∫ s, ψ s := by
  let μ : Measure ℝ := volume.restrict (Set.Ioo 0 1)
  haveI : IsProbabilityMeasure μ := ⟨by simp [μ]⟩
  let G : ℕ → ℝ → ℂ := fun n x => ∫ s in (-((n : ℝ) * x))..((n : ℝ) * (1 - x)), ψ s
  have hG : ∀ n x, G n x = (n : ℝ) • ∫ y, ψ ((n : ℝ) * (y - x)) ∂μ := by
    intro n x
    have h := intervalIntegral.smul_integral_comp_mul_sub (f := ψ) (a := 0) (b := 1) (n : ℝ)
      ((n : ℝ) * x)
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at h
    simp only [G, μ, mul_sub]
    rw [h]
    simp
  have hint : ∀ n : ℕ, Integrable (fun p : ℝ × ℝ => ψ ((n : ℝ) * (p.2 - p.1))) (μ.prod μ) := by
    intro n
    refine Integrable.of_bound ?_ C (Eventually.of_forall fun t => hb _)
    exact (hc.comp (by fun_prop)).aestronglyMeasurable
  have hnn : ∀ n, 0 ≤ ∫ x, G n x ∂μ := by
    intro n
    have h := integral_prod_nonneg (fun s => ψ ((n : ℝ) * s)) (hc.comp (by fun_prop)) C
      (fun s => hb _) (fun k t => by simpa [mul_sub] using hp k (fun i => (n : ℝ) * t i)) μ
    rw [integral_prod _ (hint n)] at h
    simp_rw [hG, integral_smul]
    exact smul_nonneg (Nat.cast_nonneg n) h
  have hlim : Tendsto (fun n => ∫ x, G n x ∂μ) atTop (𝓝 (∫ _x, (∫ s, ψ s) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ∫ s, ‖ψ s‖) ?_
      (integrable_const _) ?_ ?_
    · intro n
      have : G n = fun x => (n : ℝ) • ∫ y, ψ ((n : ℝ) * (y - x)) ∂μ := funext (hG n)
      rw [this]
      exact ((hint n).integral_prod_left.smul (n : ℝ)).aestronglyMeasurable
    · intro n
      refine Eventually.of_forall fun x => ?_
      refine (intervalIntegral.norm_integral_le_integral_norm_uIoc).trans ?_
      exact setIntegral_le_integral hi.norm (Eventually.of_forall fun _ => norm_nonneg _)
    · refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx => ?_)
      refine intervalIntegral_tendsto_integral hi ?_ ?_
      · exact tendsto_neg_atTop_atBot.comp
          (tendsto_natCast_atTop_atTop.atTop_mul_const hx.1)
      · exact tendsto_natCast_atTop_atTop.atTop_mul_const (sub_pos.2 hx.2)
  simpa using ge_of_tendsto' hlim hnn
end GlobalTheory.PosDefFT
