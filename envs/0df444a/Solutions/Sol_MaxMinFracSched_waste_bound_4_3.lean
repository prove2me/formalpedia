-- Prove2me | solution 1 for MaxMinFracSched.waste_bound_4_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T09:17:00.01838+00:00
-- url     : https://prove2.me/submissions/edaeb42c-3abb-4f44-8d43-d20636191896

import Mathlib

namespace Aux_MMFS_wb

theorem key (w : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ Finset.Icc 1 k, (∑ j ∈ Finset.Icc 1 i, w j) * w i =
      ((∑ i ∈ Finset.Icc 1 k, w i) ^ 2 + ∑ i ∈ Finset.Icc 1 k, w i ^ 2) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [Finset.sum_Icc_succ_top (show 1 ≤ k + 1 by omega), ih]
    ring

end Aux_MMFS_wb

theorem solution (k : ℕ) (hk : 1 ≤ k) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hW : 0 < ∑ i ∈ Finset.Icc 1 k, w i) :
    (∑ i ∈ Finset.Icc 1 k, (1 - (∑ j ∈ Finset.Icc 1 i, w j) / ∑ m ∈ Finset.Icc 1 k, w m) *
        (w i / ∑ m ∈ Finset.Icc 1 k, w m)) =
      (1 / 2) * (1 - (∑ i ∈ Finset.Icc 1 k, w i ^ 2) / (∑ m ∈ Finset.Icc 1 k, w m) ^ 2) ∧
    (1 / 2) * (1 - (∑ i ∈ Finset.Icc 1 k, w i ^ 2) / (∑ m ∈ Finset.Icc 1 k, w m) ^ 2) ≤
      1 / 2 - 1 / (2 * (k : ℝ)) := by
  obtain ⟨W, hWdef⟩ : ∃ W, W = ∑ m ∈ Finset.Icc 1 k, w m := ⟨_, rfl⟩
  rw [← hWdef] at hW ⊢
  have hW0 : W ≠ 0 := hW.ne'
  constructor
  · have hterm : ∀ i ∈ Finset.Icc 1 k,
        (1 - (∑ j ∈ Finset.Icc 1 i, w j) / W) * (w i / W) =
          (W * w i - (∑ j ∈ Finset.Icc 1 i, w j) * w i) / W ^ 2 := by
      intro i _
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Aux_MMFS_wb.key, ← hWdef]
    field_simp
    ring
  · have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.Icc 1 k) (f := w)
    rw [← hWdef, Nat.card_Icc, Nat.add_sub_cancel] at hcs
    have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have h1 : 1 / (k : ℝ) ≤ (∑ i ∈ Finset.Icc 1 k, w i ^ 2) / W ^ 2 := by
      rw [div_le_div_iff₀ hkR (by positivity)]
      linarith
    have h2 : 1 / (2 * (k : ℝ)) = 1 / 2 * (1 / (k : ℝ)) := by field_simp
    rw [h2]
    nlinarith
