-- Prove2me | solution 1 for GlobalTheory.sqOpen_of_two_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:51.404829+00:00
-- url     : https://prove2.me/submissions/cc06413f-b9b4-4b0f-a049-4cc87d0104c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SquaringOpenAtOneOfCompleteTwoNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (K : Type) [NormedField K] [CompleteSpace K], (2 : K) ≠ 0 → SqOpen K := by
  intro K _ _ h2 V hV
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  set c := ‖(2:K)⁻¹‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  set ρ := min (ε / 2) (1 / (4 * c + 1)) with hρ
  have hρ0 : 0 < ρ := lt_min (by linarith) (by positivity)
  have hρε : ρ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρc : 2 * ρ * c ≤ 1 / 2 := by
    have h1 : ρ ≤ 1 / (4 * c + 1) := min_le_right _ _
    have h4 : 0 < 4 * c + 1 := by positivity
    have h5 : ρ * (4 * c + 1) ≤ 1 := by rwa [le_div_iff₀ h4] at h1
    nlinarith
  set δ := ρ / (2 * c + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hcδ : c * δ ≤ ρ / 2 := by
    have h : 0 < 2 * c + 1 := by positivity
    have h' : δ * (2 * c + 1) = ρ := div_mul_cancel₀ _ (ne_of_gt h)
    nlinarith
  refine ⟨Metric.closedBall 1 δ, Metric.closedBall_mem_nhds _ hδ0, ?_⟩
  intro r hr
  have hr' : ‖r - 1‖ ≤ δ := by simpa [dist_eq_norm] using hr
  set f : K → K := fun μ => μ - (μ ^ 2 - r) * (2:K)⁻¹ with hfdef
  have h22 : (2:K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  have hdiff : ∀ μ₁ μ₂ : K, f μ₁ - f μ₂ = (μ₁ - μ₂) * ((1 - μ₁) + (1 - μ₂)) * (2:K)⁻¹ := by
    intro μ₁ μ₂
    simp only [hfdef]
    linear_combination (-(μ₁ - μ₂)) * h22
  have hf1 : f 1 - 1 = (r - 1) * (2:K)⁻¹ := by
    simp only [hfdef]; ring
  set s := Metric.closedBall (1:K) ρ with hs
  have hlip : ∀ μ₁ ∈ s, ∀ μ₂ ∈ s, ‖f μ₁ - f μ₂‖ ≤ (1 / 2) * ‖μ₁ - μ₂‖ := by
    intro μ₁ h1 μ₂ h2'
    rw [hdiff, norm_mul, norm_mul]
    have a1 : ‖1 - μ₁‖ ≤ ρ := by
      rw [norm_sub_rev]; simpa [hs, dist_eq_norm] using h1
    have a2 : ‖1 - μ₂‖ ≤ ρ := by
      rw [norm_sub_rev]; simpa [hs, dist_eq_norm] using h2'
    have a3 : ‖(1 - μ₁) + (1 - μ₂)‖ ≤ 2 * ρ := (norm_add_le _ _).trans (by linarith)
    have a4 : 0 ≤ ‖μ₁ - μ₂‖ := norm_nonneg _
    have a5 : 0 ≤ ‖(1 - μ₁) + (1 - μ₂)‖ := norm_nonneg _
    calc ‖μ₁ - μ₂‖ * ‖(1 - μ₁) + (1 - μ₂)‖ * c ≤ ‖μ₁ - μ₂‖ * (2 * ρ) * c := by gcongr
      _ = ‖μ₁ - μ₂‖ * (2 * ρ * c) := by ring
      _ ≤ ‖μ₁ - μ₂‖ * (1 / 2) := by gcongr
      _ = (1 / 2) * ‖μ₁ - μ₂‖ := by ring
  have h1s : (1:K) ∈ s := Metric.mem_closedBall_self hρ0.le
  have hmaps : Set.MapsTo f s s := by
    intro μ hμ
    have hl := hlip μ hμ 1 h1s
    have hμ' : ‖μ - 1‖ ≤ ρ := by simpa [hs, dist_eq_norm] using hμ
    have hf1' : ‖f 1 - 1‖ ≤ c * δ := by
      rw [hf1, norm_mul, mul_comm]; gcongr
    have key : ‖f μ - 1‖ ≤ ρ := by
      calc ‖f μ - 1‖ = ‖(f μ - f 1) + (f 1 - 1)‖ := by congr 1; ring
        _ ≤ ‖f μ - f 1‖ + ‖f 1 - 1‖ := norm_add_le _ _
        _ ≤ (1 / 2) * ρ + c * δ := by gcongr; exact hl.trans (by gcongr)
        _ ≤ ρ := by linarith
    simpa [hs, dist_eq_norm] using key
  have hcomplete : IsComplete s := Metric.isClosed_closedBall.isComplete
  have hcon : ContractingWith (1 / 2 : NNReal) (hmaps.restrict f s s) := by
    constructor
    · rw [← NNReal.coe_lt_coe]; push_cast; norm_num
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [Set.MapsTo.val_restrict_apply, Subtype.dist_eq, dist_eq_norm]
      push_cast
      exact hlip _ x.2 _ y.2
  obtain ⟨μ, hμs, hfix, -⟩ :=
    hcon.exists_fixedPoint' hcomplete hmaps h1s (edist_ne_top _ _)
  refine ⟨μ, hball (Metric.closedBall_subset_ball hρε hμs), ?_⟩
  have hfix' : f μ = μ := hfix
  have hz : (μ ^ 2 - r) * (2:K)⁻¹ = 0 := by
    simp only [hfdef] at hfix'
    linear_combination -hfix'
  rcases mul_eq_zero.1 hz with h | h
  · linear_combination h
  · exact absurd h (inv_ne_zero h2)
end GlobalTheory
