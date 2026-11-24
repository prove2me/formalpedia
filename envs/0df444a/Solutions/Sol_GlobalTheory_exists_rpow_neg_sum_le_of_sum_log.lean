-- Prove2me | solution 1 for GlobalTheory.exists_rpow_neg_sum_le_of_sum_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:38:50.601892+00:00
-- url     : https://prove2.me/submissions/3bbb9c73-e854-47d4-a118-3553342c1629

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsRpowNegSumLeOfSumLog
import Theorems.Thm_GlobalTheory_rpow_neg_le_one_sub_log_add_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (N : ℕ) (ω η : ℝ), 1 ≤ ω → 0 < η → ∃ δ c : ℝ, 0 < δ ∧ 0 ≤ c ∧ c < 1 ∧ ∀ (σ : Type) (S : Finset σ) (t : σ → ℝ), S.card = N → (∀ s ∈ S, ω⁻¹ ≤ t s ∧ t s ≤ ω) → η ≤ ∑ s ∈ S, Real.log (t s) → ∑ s ∈ S, t s ^ (-δ) ≤ N * c) := by
  intro N ω η hω hη
  have hL : 0 ≤ Real.log ω := Real.log_nonneg hω
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  obtain ⟨δ, hδ, hδL, hδη⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * Real.log ω ≤ 1 ∧
      δ * (N * Real.log ω ^ 2) ≤ η / 2 := by
    refine ⟨min (1 / (Real.log ω + 1)) (η / 2 / (N * Real.log ω ^ 2 + 1)),
      lt_min (by positivity) (by positivity), ?_, ?_⟩
    · have h := min_le_left (1 / (Real.log ω + 1)) (η / 2 / (N * Real.log ω ^ 2 + 1))
      have hp : 0 < min (1 / (Real.log ω + 1)) (η / 2 / (N * Real.log ω ^ 2 + 1)) :=
        lt_min (by positivity) (by positivity)
      rw [le_div_iff₀ (by positivity)] at h
      nlinarith
    · have h := min_le_right (1 / (Real.log ω + 1)) (η / 2 / (N * Real.log ω ^ 2 + 1))
      have hp : 0 < min (1 / (Real.log ω + 1)) (η / 2 / (N * Real.log ω ^ 2 + 1)) :=
        lt_min (by positivity) (by positivity)
      rw [le_div_iff₀ (by positivity)] at h
      nlinarith
  have he : 0 < δ * η / (2 * (N + 1)) := by positivity
  refine ⟨δ, max 0 (1 - δ * η / (2 * (N + 1))), hδ, le_max_left _ _,
    max_lt one_pos (by linarith), ?_⟩
  intro σ S t hS ht hsum
  have h1 : ∑ s ∈ S, t s ^ (-δ) ≤
      ∑ s ∈ S, (1 - δ * Real.log (t s) + (δ * Real.log ω) ^ 2) :=
    Finset.sum_le_sum fun s hs =>
      rpow_neg_le_one_sub_log_add_sq hω hδ hδL (ht s hs).1 (ht s hs).2
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h1
  simp only [Finset.sum_const, hS, nsmul_eq_mul, mul_one] at h1
  have h2 : δ * η ≤ δ * ∑ s ∈ S, Real.log (t s) := mul_le_mul_of_nonneg_left hsum hδ.le
  have h3 : δ * (δ * (N * Real.log ω ^ 2)) ≤ δ * (η / 2) := mul_le_mul_of_nonneg_left hδη hδ.le
  have h4 : (N : ℝ) * (1 - δ * η / (2 * (N + 1))) ≤ N * max 0 (1 - δ * η / (2 * (N + 1))) :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hN
  have h5 : (N + 1 : ℝ) * (δ * η / (2 * (N + 1))) = δ * η / 2 := by field_simp
  nlinarith
end GlobalTheory
