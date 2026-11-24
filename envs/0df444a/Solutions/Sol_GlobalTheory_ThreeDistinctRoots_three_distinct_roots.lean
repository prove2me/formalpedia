-- Prove2me | solution 1 for GlobalTheory.ThreeDistinctRoots.three_distinct_roots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:32:57.979501+00:00
-- url     : https://prove2.me/submissions/20028eb6-4b52-498a-847f-6163814fbd89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ThreeDistinctRoots

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ThreeDistinctRoots
open Polynomial
namespace GlobalTheory.ThreeDistinctRoots
theorem _root_.solution :
    ∀ {K : Type} [inst : Field K] [IsAlgClosed K] (g₂ g₃ : K), (2 : K) ≠ (0 : K) →
      g₂ ^ (3 : ℕ) - (27 : K) * g₃ ^ (2 : ℕ) ≠ (0 : K) →
      ∃ (x : K) (y : K) (z : K), x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
        (4 : K) * x ^ (3 : ℕ) - g₂ * x - g₃ = (0 : K) ∧
        (4 : K) * y ^ (3 : ℕ) - g₂ * y - g₃ = (0 : K) ∧
        (4 : K) * z ^ (3 : ℕ) - g₂ * z - g₃ = (0 : K) := by
  intro K _ _ g₂ g₃ h2 hΔ
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2

  obtain ⟨x, hx⟩ : ∃ x : K, (4 : K) * x ^ 3 - g₂ * x - g₃ = 0 := by
    have hdeg : (C (4 : K) * X ^ 3 - C g₂ * X - C g₃).degree ≠ 0 := by
      have : (C (4 : K) * X ^ 3 - C g₂ * X - C g₃).degree = 3 := by
        compute_degree!
      rw [this]; decide
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdeg
    refine ⟨x, ?_⟩
    simpa using hx

  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (g₂ - 3 * x ^ 2)
  obtain ⟨y, hy⟩ : ∃ y : K, 2 * y = s - x := ⟨(s - x) / 2, by field_simp⟩
  have hq : 4 * y ^ 2 + 4 * x * y + 4 * x ^ 2 - g₂ = 0 := by
    linear_combination (2 * y + x + s) * hy - hs
  have hg₂ : g₂ = 4 * (x ^ 2 + x * y + y ^ 2) := by linear_combination -hq
  have hg₃ : g₃ = -4 * x * y * (x + y) := by
    linear_combination -hx + x * hq
  refine ⟨x, y, -x - y, ?_⟩
  have key : g₂ ^ 3 - 27 * g₃ ^ 2 = 16 * ((x - y) * (y - (-x - y)) * ((-x - y) - x)) ^ 2 := by
    rw [hg₂, hg₃]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; apply hΔ; rw [key, sub_eq_zero.mpr h]; ring
  · intro h; apply hΔ
    rw [key, show (-x - y) - x = -(x - (-x - y)) by ring, sub_eq_zero.mpr h]; ring
  · intro h; apply hΔ
    rw [key, sub_eq_zero.mpr h]; ring
  · exact hx
  · rw [hg₂, hg₃]; ring
  · rw [hg₂, hg₃]; ring
end GlobalTheory.ThreeDistinctRoots
