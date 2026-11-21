-- Prove2me | solution 1 for MasulloAudit.kernel_perturbation_prevents_lift_decay
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-21T04:35:27.127226+00:00
-- url     : https://prove2.me/submissions/2ad34c61-d448-4653-880a-5525a867a416

import Theorems.Thm_MasulloRH_lifted_rank_one_schatten_norms

open MasulloGRH MasulloRH InnerProductSpace

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K F : Submodule ℂ H) (A : H →L[ℂ] H) (v η : ℕ → H) (k : H)
    (hk : k ∈ K ⊓ F) (hak : A k ≠ 0)
    (c C ε : ℝ) (hC : 0 < C) (hε : ‖k‖ < ε)
    (hv : ∀ i, v i ∈ F ∧ c ≤ ‖v i‖ ∧ ‖v i‖ ≤ C)
    (hbi : ∀ i, inner ℂ (η i) (v i) = 1) :
    0 < ‖A k‖ / C ∧ ∃ w : ℕ → H, ∀ i, w i ∈ F ∧ w i - v i ∈ K ∧
      c-ε < ‖w i‖ ∧ ‖w i‖ < C+ε ∧
      ‖A k‖ / C ≤ traceNorm (rankOne ℂ (A (w i)) (η i)) := by
  classical
  have hchoice (i : ℕ) : ∃ w ∈ F, w-v i ∈ K ∧ ‖w-v i‖ = ‖k‖ ∧ ‖A k‖ ≤ ‖A w‖ := by
    have htri : 2 * ‖A k‖ ≤ ‖A (v i + k)‖ + ‖A (v i - k)‖ := by
      have h := norm_sub_le (A (v i+k)) (A (v i-k))
      rw [map_add, map_sub, show A (v i)+A k-(A (v i)-A k) = A k + A k by abel,
        ← two_smul ℝ (A k), norm_smul] at h
      simpa using h
    by_cases h : ‖A k‖ ≤ ‖A (v i + k)‖
    · exact ⟨v i+k, F.add_mem (hv i).1 hk.2, by simpa using hk.1, by simp, h⟩
    · refine ⟨v i-k, F.sub_mem (hv i).1 hk.2, ?_, ?_, by linarith⟩
      · simpa [sub_sub_cancel_left] using K.neg_mem hk.1
      · simp
  choose w hw hK he ha using hchoice
  refine ⟨div_pos (norm_pos_iff.mpr hak) hC, w, fun i => ⟨hw i, hK i, ?_, ?_, ?_⟩⟩
  · have h := norm_sub_norm_le (v i) (w i)
    rw [norm_sub_rev, he] at h
    linarith [(hv i).2.1]
  · have h := norm_sub_norm_le (w i) (v i)
    rw [he] at h
    linarith [(hv i).2.2]
  · rw [(lifted_rank_one_schatten_norms _ _).1, div_le_iff₀ hC]
    have h : 1 ≤ ‖η i‖ * C := calc
      1 = ‖inner ℂ (η i) (v i)‖ := by rw [hbi]; simp
      _ ≤ ‖η i‖ * ‖v i‖ := norm_inner_le_norm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hv i).2.2 (norm_nonneg _)
    calc
      ‖A k‖ ≤ ‖A (w i)‖ := ha i
      _ ≤ ‖A (w i)‖ * (‖η i‖ * C) := le_mul_of_one_le_right (norm_nonneg _) h
      _ = _ := (mul_assoc _ _ _).symm
