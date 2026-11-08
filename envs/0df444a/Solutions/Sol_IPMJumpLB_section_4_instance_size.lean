-- Prove2me | solution 1 for IPMJumpLB.section_4_instance_size
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:28:25.202373+00:00
-- url     : https://prove2.me/submissions/c91a8e1c-970a-409e-a807-f6f08474010e

import Mathlib
import Definitions.Def_IPMJumpLB_FlowInstance
import Definitions.Def_IPMJumpLB_VertexU
import Definitions.Def_IPMJumpLB_ArcU
import Definitions.Def_IPMJumpLB_nHat
import Definitions.Def_IPMJumpLB_mHat

open IPMJumpLB in
theorem solution (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) (hk : 3 ≤ k)
    (b : ℕ) (hb : b = ⌈6 / α⌉₊) (η : ℝ) (hη : η = α * (nHat b k : ℝ)) :
    Fintype.card (VertexU b k) = nHat b k ∧ Fintype.card (ArcU b k) = mHat b k ∧
      6 * (k : ℝ) ^ 2 ≤ η ∧ 2 * (2 * (k : ℝ) ^ 2 + k) ≤ 6 * (k : ℝ) ^ 2 := by
  have hb6 : 6 / α ≤ (b : ℝ) := by rw [hb]; exact Nat.le_ceil _
  have h6 : (6 : ℝ) < 6 / α := by
    rw [lt_div_iff₀ hα0]; linarith
  have hb7 : 7 ≤ b := by
    have : (6 : ℝ) < b := lt_of_lt_of_le h6 hb6
    have : 6 < b := by exact_mod_cast this
    omega
  have hαb : 6 ≤ α * (b : ℝ) := by
    have := mul_le_mul_of_nonneg_left hb6 hα0.le
    rwa [mul_div_cancel₀ _ hα0.ne'] at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_congr (VertexU.equivSum b k)]
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod]
    unfold nHat
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 2 := ⟨b - 2, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  · rw [Fintype.card_congr (ArcU.equivSum b k)]
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod]
    unfold mHat
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 2 := ⟨b - 2, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have e : 2 * (c + 2) - 2 = 2 * c + 2 := by omega
    simp only [Nat.add_sub_cancel, e]
    ring
  · rw [hη]
    unfold nHat
    push_cast
    have hk2 : (0 : ℝ) ≤ (k : ℝ) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hαb hk2]
  · have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
