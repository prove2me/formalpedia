-- Prove2me | solution 1 for GlobalTheory.AvgSmooth.hasFDerivAt_avg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:13:27.434634+00:00
-- url     : https://prove2.me/submissions/79e59174-ca47-4b6e-a1b3-00ccaf08007e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ContDiffCompactAverageOfClosedPartials
import Theorems.Thm_GlobalTheory_AvgSmooth_integrable_cont
import Theorems.Thm_GlobalTheory_AvgSmooth_clm_expand

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
open GlobalTheory GlobalTheory.AvgSmooth
variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] {n : ℕ}
namespace GlobalTheory.AvgSmooth
theorem _root_.solution (μ : Measure K) [IsFiniteMeasure μ] {F : K → (Fin n → ℝ) → ℂ}
    {G : Fin n → K → (Fin n → ℝ) → ℂ} (hF : Continuous fun p : K × (Fin n → ℝ) => F p.1 p.2)
    (hG : ∀ i, Continuous fun p : K × (Fin n → ℝ) => G i p.1 p.2) (hd : ∀ k, Differentiable ℝ (F k))
    (he : ∀ i k t, fderiv ℝ (F k) t (Pi.single i 1) = G i k t) (t₀ : Fin n → ℝ) :
    HasFDerivAt (fun t => ∫ k, F k t ∂μ) (∑ i, (∫ k, G i k t₀ ∂μ) • coordC n i) t₀ := by
  have hFk : ∀ t, Continuous fun k => F k t := fun t => hF.comp (continuous_id.prodMk continuous_const)
  have hGk : ∀ i t, Continuous fun k => G i k t := fun i t => (hG i).comp (continuous_id.prodMk continuous_const)
  have hM : ∀ i, ∃ M : ℝ, ∀ p ∈ (Set.univ : Set K) ×ˢ Metric.closedBall t₀ 1, ‖G i p.1 p.2‖ ≤ M := fun i =>
    (isCompact_univ.prod (isCompact_closedBall t₀ 1)).exists_bound_of_continuousOn (hG i).continuousOn
  choose M hM using hM
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ)
    (F := fun t k => F k t) (F' := fun t k => ∑ i, G i k t • coordC n i)
    (bound := fun _ => ∑ i, M i * ‖coordC n i‖) (Metric.ball_mem_nhds t₀ one_pos)
    (Filter.Eventually.of_forall fun t => (hFk t).aestronglyMeasurable)
    (integrable_cont μ (hFk t₀))
    (Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hGk i t₀).aestronglyMeasurable.smul_const _)
    (Filter.Eventually.of_forall fun k t ht => by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_smul]
      gcongr
      exact hM i (k, t) ⟨Set.mem_univ _, Metric.ball_subset_closedBall ht⟩)
    (integrable_const _)
    (Filter.Eventually.of_forall fun k t _ => by
      have h := (hd k t).hasFDerivAt
      rw [clm_expand (fderiv ℝ (F k) t)] at h
      simpa only [he] using h)
  refine key.congr_fderiv ?_
  rw [integral_finset_sum _ fun i _ => (integrable_cont μ (hGk i t₀)).smul_const _]
  exact Finset.sum_congr rfl fun i _ => integral_smul_const _ _
end GlobalTheory.AvgSmooth
