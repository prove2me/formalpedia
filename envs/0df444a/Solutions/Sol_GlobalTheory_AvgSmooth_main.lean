-- Prove2me | solution 1 for GlobalTheory.AvgSmooth.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:28:45.598004+00:00
-- url     : https://prove2.me/submissions/9df94aca-a44f-451c-8fae-b7b9d2cd5f20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ContDiffCompactAverageOfClosedPartials
import Theorems.Thm_GlobalTheory_AvgSmooth_integrable_cont
import Theorems.Thm_GlobalTheory_AvgSmooth_hasFDerivAt_avg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
noncomputable section
open GlobalTheory.AvgSmooth
namespace GlobalTheory.AvgSmooth
theorem _root_.solution : ∀ (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (n : ℕ) (φ : Fin n → (Fin n → ℝ) → ℂ), (∀ i, ContDiff ℝ ∞ (φ i)) → ∀ 𝒢 : Set (K → (Fin n → ℝ) → ℂ), (∀ F ∈ 𝒢, Continuous fun p : K × (Fin n → ℝ) => F p.1 p.2) → (∀ F ∈ 𝒢, ∀ k, Differentiable ℝ (F k)) → (∀ F ∈ 𝒢, ∀ i, ∃ F' ∈ 𝒢, ∀ k t, fderiv ℝ (F k) t (Pi.single i 1) = F' k t + φ i t * F k t) → ∀ F ∈ 𝒢, ContDiff ℝ ∞ fun t => ∫ k, F k t ∂μ := by
  intro K _ _ _ _ μ _ n φ hφ 𝒢 hc hd hder
  have hk : ∀ F ∈ 𝒢, ∀ t, Integrable (fun k => F k t) μ := fun F hF t =>
    integrable_cont μ ((hc F hF).comp (continuous_id.prodMk continuous_const))
  have hD : ∀ F ∈ 𝒢, ∃ F' : Fin n → K → (Fin n → ℝ) → ℂ, (∀ i, F' i ∈ 𝒢) ∧ ∀ t₀,
      HasFDerivAt (fun t => ∫ k, F k t ∂μ)
        (∑ i, ((∫ k, F' i k t₀ ∂μ) + φ i t₀ * ∫ k, F k t₀ ∂μ) • coordC n i) t₀ := by
    intro F hF
    choose F' hF' he using hder F hF
    refine ⟨F', hF', fun t₀ => ?_⟩
    have h := hasFDerivAt_avg μ (G := fun i k t => F' i k t + φ i t * F k t) (hc F hF)
      (fun i => (hc _ (hF' i)).add (((hφ i).continuous.comp continuous_snd).mul (hc F hF))) (hd F hF) he t₀
    refine h.congr_fderiv (Finset.sum_congr rfl fun i _ => ?_)
    rw [integral_add (hk _ (hF' i) t₀) ((hk F hF t₀).const_mul _), integral_const_mul]
  have solution : ∀ m : ℕ, ∀ F ∈ 𝒢, ContDiff ℝ m fun t => ∫ k, F k t ∂μ := by
    intro m
    induction m with
    | zero =>
      intro F hF
      obtain ⟨F', -, h⟩ := hD F hF
      exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t => (h t).continuousAt)
    | succ m ih =>
      intro F hF
      obtain ⟨F', hF', h⟩ := hD F hF
      rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by norm_cast, contDiff_succ_iff_hasFDerivAt]
      refine ⟨_, ?_, h⟩
      refine ContDiff.sum fun i _ => ContDiff.smul_const ?_ _
      exact (ih _ (hF' i)).add ((contDiff_infty.1 (hφ i) m).mul (ih F hF))
  intro F hF
  exact contDiff_infty.2 fun m => solution m F hF
end GlobalTheory.AvgSmooth
