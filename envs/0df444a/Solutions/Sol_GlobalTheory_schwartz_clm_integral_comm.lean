-- Prove2me | solution 1 for GlobalTheory.schwartz_clm_integral_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:32:40.291455+00:00
-- url     : https://prove2.me/submissions/90988a8d-0c5d-4399-880d-5c9f40d23ead

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzIntegralSuperposition
import Theorems.Thm_GlobalTheory_SchwartzIntegralExchange_exists_factor
import Theorems.Thm_GlobalTheory_SchwartzIntegralExchange_le_norm_wtFun
import Theorems.Thm_GlobalTheory_SchwartzIntegralExchange_integrable_wt
import Theorems.Thm_GlobalTheory_SchwartzIntegralExchange_wt_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
open SchwartzIntegralExchange
namespace GlobalTheory
theorem _root_.solution :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Type) [TopologicalSpace P]
    [SecondCountableTopology P] [MeasurableSpace P] [OpensMeasurableSpace P] (ν : Measure P)
    (Φ : P → SchwartzMap E ℂ), Continuous Φ → ∀ (c : P → ℂ), AEStronglyMeasurable c ν →
    (∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) ν) →
    ∀ (u : SchwartzMap E ℂ), (∀ x, u x = ∫ ξ, c ξ * Φ ξ x ∂ν) →
    ∀ (Λ : SchwartzMap E ℂ →L[ℂ] ℂ), Λ u = ∫ ξ, c ξ * Λ (Φ ξ) ∂ν := by
  intro E _ _ P _ _ _ _ ν Φ hΦ c hc hi u hu Λ
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ)
    ((normSeminorm ℂ ℂ).comp Λ.toLinearMap) (continuous_norm.comp Λ.continuous)
  let J : SchwartzMap E ℂ →L[ℂ] (∀ i : s, BoundedContinuousFunction E
      (ContinuousMultilinearMap ℝ (fun _ : Fin i.1.2 => E) ℂ)) :=
    ContinuousLinearMap.pi fun i => wt i.1.1 i.1.2
  obtain ⟨g, hg⟩ := exists_factor J.toLinearMap Λ.toLinearMap C (fun w => by
    have h1 : ‖Λ w‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ E ℂ)) w := hC w
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ C.2)
    refine Seminorm.finset_sup_apply_le (norm_nonneg _) fun i hi => ?_
    exact (le_norm_wtFun i.1 i.2 w).trans (norm_le_pi_norm (J w) ⟨i, hi⟩))
  have hg' : ∀ w, g (J w) = Λ w := hg
  have hint : Integrable (fun ξ => c ξ • J (Φ ξ)) ν :=
    integrable_pi_iff.2 fun i => integrable_wt hΦ hc hi i.1.1 i.1.2
  have hJ : J u = ∫ ξ, c ξ • J (Φ ξ) ∂ν := by
    funext i
    rw [eval_integral (integrable_pi_iff.1 hint)]
    exact wt_integral hΦ hc hi u hu i.1.1 i.1.2
  rw [← hg', hJ, ← g.integral_comp_comm hint]
  simp [hg']
end GlobalTheory
