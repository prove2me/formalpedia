-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.isGood_of_tsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:48:51.566373+00:00
-- url     : https://prove2.me/submissions/598ff054-0ce8-491d-a698-7027f1dbd1a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoIsGoodOfTsum
import Theorems.Thm_GlobalTheory_HeckeTwo_SumGood_contDiffOn_tsum_infty
import Theorems.Thm_GlobalTheory_HeckeTwo_SumGood_wirtWord_congr
import Theorems.Thm_GlobalTheory_HeckeTwo_SumGood_norm_iteratedFDeriv_wirtWord
import Theorems.Thm_GlobalTheory_HeckeTwo_SumGood_wirtWord_tsum
import Theorems.Thm_GlobalTheory_HeckeTwo_GoodAdd_upperHalf_isOpen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory.HeckeTwo.SumGood
namespace GlobalTheory.HeckeTwo
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (ι : Type)
    (g : ι → ℂ → (Emb F → ℂ) → ℂ) (P : ℂ → (Emb F → ℂ) → ℂ),
    (∀ i, ∀ σ ∈ halfPlane, ContDiffOn ℝ ∞ (g i σ) (upperHalf F)) →
    (∀ i, ∀ w : List (Emb F × Bool), ∀ z ∈ upperHalf F,
      DifferentiableOn ℂ (fun σ => wirtWord w (g i σ) z) halfPlane) →
    (∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F →
      ∀ n : ℕ, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ σ ∈ K, ∀ z ∈ L, ‖iteratedFDeriv ℝ n (g i σ) z‖ ≤ u i) →
    (∀ σ ∈ halfPlane, ∀ z ∈ upperHalf F, P σ z = ∑' i, g i σ z) →
    IsGood P := by
  intro F _ _ ι g P h1 h2 h3 h4
  have hU := GoodAdd.upperHalf_isOpen F
  have hfam : ∀ σ ∈ halfPlane, GoodFam (upperHalf F) (fun i => g i σ) := fun σ hσ =>
    ⟨fun i => h1 i σ hσ, fun L hL hLU k => by
      obtain ⟨u, hu, hb⟩ := h3 {σ} isCompact_singleton (Set.singleton_subset_iff.2 hσ) L hL hLU k
      exact ⟨u, hu, fun i z hz => hb i σ rfl z hz⟩⟩
  have hPeq : ∀ σ ∈ halfPlane, Set.EqOn (P σ) (fun z => ∑' i, g i σ z) (upperHalf F) :=
    fun σ hσ z hz => h4 σ hσ z hz
  refine ⟨fun σ hσ => (contDiffOn_tsum_infty hU (hfam σ hσ)).congr (hPeq σ hσ), fun w z hz => ?_⟩
  have heq : ∀ σ ∈ halfPlane, wirtWord w (P σ) z = ∑' i, wirtWord w (g i σ) z := fun σ hσ => by
    rw [wirtWord_congr hU w (hPeq σ hσ) hz]
    exact wirtWord_tsum hU (hfam σ hσ) w hz
  obtain ⟨C, hC0, hC⟩ := norm_iteratedFDeriv_wirtWord hU w
  have hHo : IsOpen (halfPlane : Set ℂ) := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.congr ?_ heq
  intro σ₀ hσ₀
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hHo σ₀ hσ₀
  have hsub : Metric.closedBall σ₀ (r / 2) ⊆ halfPlane :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrU
  obtain ⟨u, hu, hb⟩ := h3 _ (isCompact_closedBall σ₀ (r / 2)) hsub {z} isCompact_singleton
    (Set.singleton_subset_iff.2 hz) w.length
  have hd : DifferentiableOn ℂ (fun σ => ∑' i, wirtWord w (g i σ) z) (Metric.ball σ₀ (r / 2)) := by
    refine differentiableOn_tsum_of_summable_norm (hu.mul_left C)
      (fun i => (h2 i w z hz).mono (Metric.ball_subset_closedBall.trans hsub)) Metric.isOpen_ball ?_
    intro i σ hσ
    have := hC (g i σ) (h1 i σ (hsub (Metric.ball_subset_closedBall hσ))) 0 z hz
    rw [norm_iteratedFDeriv_zero, Nat.zero_add] at this
    exact this.trans (mul_le_mul_of_nonneg_left (hb i σ (Metric.ball_subset_closedBall hσ) z rfl) hC0)
  exact (hd.differentiableAt (Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self (by linarith)))).differentiableWithinAt
end GlobalTheory.HeckeTwo
