-- Prove2me | solution 1 for GlobalTheory.HyperplaneLocBound.norm_le_of_circle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:53:51.679186+00:00
-- url     : https://prove2.me/submissions/91b82718-8b86-403d-8838-cbd1a80aa0e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocallyBoundedOffCoordinateHyperplanes
import Theorems.Thm_GlobalTheory_HyperplaneLocBound_isOpen_offHyperplanes
import Theorems.Thm_GlobalTheory_HyperplaneLocBound_prod_update_eq

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
theorem _root_.solution {n a : ℕ} {ρ r : ℝ} {Φ : (Fin n → ℂ) → ℂ} {m : Fin n → ℕ}
    (hext : ∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t)
    (hΦ : DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0})
    (hgr : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) →
      ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1)
    {z₀ z : Fin n → ℂ} (hr : 0 < r) (hsub : ball z₀ (2 * r) ⊆ ball 0 ρ)
    (hz : z ∈ closedBall z₀ r) (hgen : ∀ j, z j ≠ 0) {k : Fin n} (hk0 : z₀ k = 0)
    {B : ℝ} (hB : ∀ t : ℂ, ‖t‖ = r → ‖Φ (Function.update z k t)‖ ≤ B) : ‖Φ z‖ ≤ B := by
  set H : ℂ → ℂ := fun t => Φ (Function.update z k t) with hH
  have hmem : ∀ t ∈ ball (0 : ℂ) (2 * r), Function.update z k t ∈ ball z₀ (2 * r) := by
    intro t ht
    rw [mem_ball, dist_pi_lt_iff (by linarith)]
    intro j
    by_cases hj : j = k
    · subst hj; simpa [hk0] using ht
    · rw [Function.update_of_ne hj]
      exact lt_of_le_of_lt ((dist_le_pi_dist z z₀ j).trans (mem_closedBall.1 hz)) (by linarith)
  have hU : ∀ t ∈ ball (0 : ℂ) (2 * r), t ≠ 0 → Function.update z k t ∈
      {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} := by
    intro t ht ht0
    refine ⟨hsub (hmem t ht), fun j _ => ?_⟩
    by_cases hj : j = k
    · subst hj; simpa using ht0
    · rw [Function.update_of_ne hj]; exact hgen j
  have hHd : DifferentiableOn ℂ H (ball (0 : ℂ) (2 * r) \ {0}) := by
    intro t ht
    have hd := (hΦ _ (hU t ht.1 ht.2)).differentiableAt
      ((isOpen_offHyperplanes n a ρ).mem_nhds (hU t ht.1 ht.2))
    exact (hd.comp t (hasFDerivAt_update z t).differentiableAt).differentiableWithinAt
  set P := ∏ j ∈ Finset.univ.erase k, ‖z j‖ ^ m j with hPdef
  have hP : 0 < P := Finset.prod_pos fun j _ => pow_pos (norm_pos_iff.2 (hgen j)) _
  have hHg : ∀ t ∈ ball (0 : ℂ) (2 * r), t ≠ 0 →
      ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ m k ≤ 1 / P := by
    intro t ht ht0
    have h1 := hgr _ (hU t ht ht0).1 (hU t ht ht0).2
    rw [prod_update_eq, ← mul_assoc] at h1
    exact (le_div_iff₀ hP).2 h1
  obtain ⟨G, hGd, hGH⟩ := hext H (2 * r) (1 / P) (m k) (by linarith) hHd hHg
  have hcl : closedBall (0 : ℂ) r ⊆ ball 0 (2 * r) := closedBall_subset_ball (by linarith)
  have hzk : z k ∈ closedBall (0 : ℂ) r := by
    rw [mem_closedBall]
    have := dist_le_pi_dist z z₀ k
    rw [hk0] at this
    exact this.trans (mem_closedBall.1 hz)
  have key := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    (hGd.diffContOnCl_ball hcl) (C := B) ?_ (by rw [closure_ball 0 hr.ne']; exact hzk)
  · rw [hGH _ (hcl hzk) (hgen k)] at key
    simpa [H] using key
  · intro t ht
    rw [frontier_ball 0 hr.ne', mem_sphere, dist_zero_right] at ht
    have ht0 : t ≠ 0 := by rintro rfl; simp at ht; linarith
    have htb : t ∈ ball (0 : ℂ) (2 * r) := by rw [mem_ball, dist_zero_right]; linarith
    rw [hGH t htb ht0]
    exact hB t ht
end GlobalTheory.HyperplaneLocBound
