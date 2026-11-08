-- Prove2me | solution 1 for NontruthfulPA.gsp_image_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:07:51.626667+00:00
-- url     : https://prove2.me/submissions/dfae4ee4-9791-4a0d-b369-c909d6a3d97b

import Mathlib
import Definitions.Def_NontruthfulPA_Model
import Definitions.Def_NontruthfulPA_GSPImage

open Finset

open NontruthfulPA in
theorem solution {k n : ℕ} (hkn : k ≤ n) {α : ℕ → ℝ} (hα : IsPosVec k α) {b : Fin n → ℝ}
    (hb0 : ∀ i, 0 ≤ b i) (hb : Antitone b) :
    ∀ i : Fin n, 1 ≤ (i : ℕ) → (i : ℕ) ≤ k → gspImage k α b i ≤ b i := by
  intro i hi1 hik
  have hi0 : (i : ℕ) ≠ 0 := by omega
  have hαpos : 0 < α ((i : ℕ) - 1) := hα.1 _ (by omega)
  simp only [gspImage, hi0, if_false]
  rw [if_pos ⟨hi1, hik, hαpos⟩, div_le_iff₀ hαpos]
  unfold payV
  have hw : ∀ j ∈ Finset.Ico ((i : ℕ) - 1) k, 0 ≤ α j - α (j + 1) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    rcases Nat.lt_or_ge (j + 1) k with h | h
    · have := hα.2.1 j (j + 1) (by omega) h
      linarith
    · have h1 := hα.2.2 (j + 1) h
      have h2 := hα.1 j hj.2
      linarith
  have hc : ∀ j ∈ Finset.Ico ((i : ℕ) - 1) k, padBids b (j + 1) ≤ b i := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    unfold padBids
    split_ifs with h
    · apply hb
      rw [Fin.le_iff_val_le_val]
      show (i : ℕ) ≤ j + 1
      omega
    · exact hb0 i
  have ht : ∑ j ∈ Finset.Ico ((i : ℕ) - 1) k, (α j - α (j + 1)) = α ((i : ℕ) - 1) - α k := by
    have h := Finset.sum_Ico_sub (f := α) (show (i : ℕ) - 1 ≤ k by omega)
    rw [show (∑ j ∈ Finset.Ico ((i : ℕ) - 1) k, (α j - α (j + 1))) =
        -∑ j ∈ Finset.Ico ((i : ℕ) - 1) k, (α (j + 1) - α j) by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring), h]
    ring
  calc ∑ j ∈ Finset.Ico ((i : ℕ) - 1) k, (α j - α (j + 1)) * padBids b (j + 1)
      ≤ ∑ j ∈ Finset.Ico ((i : ℕ) - 1) k, (α j - α (j + 1)) * b i :=
        Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hc j hj) (hw j hj))
    _ = (∑ j ∈ Finset.Ico ((i : ℕ) - 1) k, (α j - α (j + 1))) * b i := by rw [Finset.sum_mul]
    _ = (α ((i : ℕ) - 1) - α k) * b i := by rw [ht]
    _ = b i * α ((i : ℕ) - 1) := by rw [hα.2.2 k le_rfl]; ring
