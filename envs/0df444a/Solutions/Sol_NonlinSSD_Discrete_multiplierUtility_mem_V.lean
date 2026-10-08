-- Prove2me | solution 1 for NonlinSSD.Discrete.multiplierUtility_mem_V
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:34:57.594734+00:00
-- url     : https://prove2.me/submissions/07619217-6bd3-41ef-9fd6-3b29013dfc54

import Mathlib
import Definitions.Def_NonlinSSD_Discrete_Problem

open Finset

open NonlinSSD.Discrete in
theorem solution {n : ℕ} (y μ : Fin n → ℝ) (hμ : ∀ k, 0 ≤ μ k) :
    NonlinSSD.Discrete.InV y (NonlinSSD.Discrete.multiplierUtility y μ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨convex_univ, ?_⟩
    intro x _ z _ a b ha hb hab
    simp only [multiplierUtility, smul_eq_mul]
    have key : ∀ k, μ k * max (y k - (a * x + b * z)) 0 ≤
        a * (μ k * max (y k - x) 0) + b * (μ k * max (y k - z) 0) := by
      intro k
      have h1 : max (y k - (a * x + b * z)) 0 ≤ a * max (y k - x) 0 + b * max (y k - z) 0 := by
        apply max_le
        · have e : y k - (a * x + b * z) = a * (y k - x) + b * (y k - z) := by
            have : y k = (a + b) * y k := by rw [hab, one_mul]
            linear_combination this
          rw [e]
          exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
            (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
        · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
      calc μ k * max (y k - (a * x + b * z)) 0
          ≤ μ k * (a * max (y k - x) 0 + b * max (y k - z) 0) :=
            mul_le_mul_of_nonneg_left h1 (hμ k)
        _ = a * (μ k * max (y k - x) 0) + b * (μ k * max (y k - z) 0) := by ring
    have hs := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) => key k)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
    linarith
  · intro a b hab
    simp only [multiplierUtility]
    apply neg_le_neg
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) (hμ k)
  · intro s t _ hk
    refine ⟨∑ k, (if y k ≤ s then 0 else μ k), -∑ k, (if y k ≤ s then 0 else μ k * y k), ?_⟩
    intro x hx
    simp only [multiplierUtility]
    rw [Finset.sum_mul, ← sub_eq_add_neg, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : y k ≤ s
    · simp only [h, if_true]
      rw [max_eq_right (by linarith [hx.1])]
      ring
    · simp only [h, if_false]
      have ht : t ≤ y k := by
        by_contra hc
        exact hk k ⟨not_le.mp h, not_le.mp hc⟩
      rw [max_eq_left (by linarith [hx.2])]
      ring
  · intro t ht
    simp only [multiplierUtility, neg_eq_zero]
    apply Finset.sum_eq_zero
    intro k _
    rw [max_eq_right (by linarith [ht k])]
    ring
