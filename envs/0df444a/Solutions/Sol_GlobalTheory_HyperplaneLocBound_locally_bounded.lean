-- Prove2me | solution 1 for GlobalTheory.HyperplaneLocBound.locally_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:09:45.67272+00:00
-- url     : https://prove2.me/submissions/99ab7afd-63a7-4597-92e7-729b6d15d1e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocallyBoundedOffCoordinateHyperplanes
import Theorems.Thm_GlobalTheory_HyperplaneLocBound_isOpen_offHyperplanes
import Theorems.Thm_GlobalTheory_HyperplaneLocBound_norm_le_of_circle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Filter Topology Set
open GlobalTheory GlobalTheory.HyperplaneLocBound
namespace GlobalTheory.HyperplaneLocBound
theorem _root_.solution : (∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t) → ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∀ z₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ Metric.ball (0 : Fin n → ℂ) ρ → (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Φ z‖ ≤ M := by
  intro hext n a ρ Φ m hρ hΦ hgr z₀ hz₀
  have hUo := isOpen_offHyperplanes n a ρ
  have hδ : 0 < ρ - ‖z₀‖ := by rw [mem_ball, dist_zero_right] at hz₀; linarith
  obtain ⟨r, hr0, hrδ, hrk⟩ : ∃ r : ℝ, 0 < r ∧ 2 * r < ρ - ‖z₀‖ ∧ ∀ k, z₀ k ≠ 0 → r < ‖z₀ k‖ := by
    have h1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
    have h2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), 2 * r < ρ - ‖z₀‖ := by
      apply nhdsWithin_le_nhds
      have : Tendsto (fun r : ℝ => 2 * r) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_const_mul (2 : ℝ)).tendsto 0
      exact this.eventually (gt_mem_nhds hδ)
    have h3 : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ k, z₀ k ≠ 0 → r < ‖z₀ k‖ := by
      rw [eventually_all]; intro k
      by_cases hk : z₀ k = 0
      · exact Eventually.of_forall fun _ h => absurd hk h
      · exact (show ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ‖z₀ k‖ from
          nhdsWithin_le_nhds (gt_mem_nhds (norm_pos_iff.2 hk))).mono fun r hr _ => hr
    exact (h1.and (h2.and h3)).exists
  have hsub : ball z₀ (2 * r) ⊆ ball 0 ρ := ball_subset_ball' (by rw [dist_zero_right]; linarith)
  set K := closedBall z₀ r ∩ {ζ : Fin n → ℂ | ∀ k : Fin n, (k : ℕ) < a → z₀ k = 0 → ‖ζ k‖ = r}
    with hK
  have hKc : IsCompact K := (isCompact_closedBall z₀ r).inter_right (by
    simp only [setOf_forall]
    exact isClosed_iInter fun k => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_eq (continuous_norm.comp (continuous_apply k)) continuous_const)
  have hKU : K ⊆ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} := by
    rintro ζ ⟨hζ, hζc⟩
    refine ⟨hsub (closedBall_subset_ball (by linarith) hζ), fun k hk => ?_⟩
    by_cases h0 : z₀ k = 0
    · intro h; have := hζc k hk h0; rw [h, norm_zero] at this; linarith
    · intro h
      have h1 := dist_le_pi_dist ζ z₀ k
      rw [h, dist_comm, dist_zero_right] at h1
      have := hrk k h0
      linarith [mem_closedBall.1 hζ]
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hΦ.continuousOn.mono hKU)
  have hind : ∀ S : Finset (Fin n), ∀ z : Fin n → ℂ, (∀ j, z j ≠ 0) → z ∈ closedBall z₀ r →
      (∀ k : Fin n, (k : ℕ) < a → z₀ k = 0 → k ∉ S → ‖z k‖ = r) → ‖Φ z‖ ≤ M := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro z _ hz hc
      exact hM z ⟨hz, fun k hk h0 => hc k hk h0 (by simp)⟩
    · intro k S hkS ih z hgen hz hc
      by_cases hk : (k : ℕ) < a ∧ z₀ k = 0
      · refine norm_le_of_circle hext hΦ hgr hr0 hsub hz hgen hk.2 fun t ht => ?_
        apply ih
        · intro j
          by_cases hj : j = k
          · subst hj; simp only [Function.update_self]; rintro rfl; simp at ht; linarith
          · rw [Function.update_of_ne hj]; exact hgen j
        · rw [mem_closedBall, dist_pi_le_iff hr0.le]
          intro j
          by_cases hj : j = k
          · subst hj; simp [hk.2, ht]
          · rw [Function.update_of_ne hj]
            exact (dist_le_pi_dist z z₀ j).trans (mem_closedBall.1 hz)
        · intro j hj h0 hjS
          by_cases hjk : j = k
          · subst hjk; simpa using ht
          · rw [Function.update_of_ne hjk]; exact hc j hj h0 (by simp [hjk, hjS])
      · apply ih z hgen hz
        intro j hj h0 hjS
        by_cases hjk : j = k
        · subst hjk; exact absurd ⟨hj, h0⟩ hk
        · exact hc j hj h0 (by simp [hjk, hjS])
  refine ⟨ball z₀ r, ball_mem_nhds z₀ hr0, M, fun z hzV hzρ hza => ?_⟩
  have hzU : z ∈ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} :=
    ⟨hzρ, hza⟩
  let w : ℂ → Fin n → ℂ := fun s j => if z j = 0 then s else z j
  have hwc : Continuous w := continuous_pi fun j => by
    by_cases h : z j = 0
    · simp only [w, h, if_true]; exact continuous_id
    · simp only [w, h, if_false]; exact continuous_const
  have hw0 : w 0 = z := funext fun j => by by_cases h : z j = 0 <;> simp [w, h]
  have hΦz : ContinuousAt Φ z := (hΦ.differentiableAt (hUo.mem_nhds hzU)).continuousAt
  have hT : Tendsto (fun s => Φ (w s)) (𝓝[≠] (0 : ℂ)) (𝓝 (Φ z)) := by
    have hc : ContinuousAt (Φ ∘ w) 0 :=
      ContinuousAt.comp (x := 0) (by rw [hw0]; exact hΦz) hwc.continuousAt
    have h := hc.tendsto
    rw [Function.comp_apply, hw0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ s in 𝓝[≠] (0 : ℂ), ‖Φ (w s)‖ ≤ M := by
    have h1 : ∀ᶠ s in 𝓝 (0 : ℂ), w s ∈ ball z₀ r :=
      hwc.continuousAt.preimage_mem_nhds (by rw [hw0]; exact isOpen_ball.mem_nhds hzV)
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with s hs hs0
    apply hind Finset.univ (w s)
    · intro j
      simp only [w]
      split_ifs with h
      · exact hs0
      · exact h
    · exact ball_subset_closedBall hs
    · intro k _ _ hk; exact absurd (Finset.mem_univ k) hk
  exact le_of_tendsto hT.norm hev
end GlobalTheory.HyperplaneLocBound
