-- Prove2me | solution 1 for NeedPersuasion.Threshold.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:26:05.223444+00:00
-- url     : https://prove2.me/submissions/7d6d8891-c806-44b6-8f5e-e4bace17f1be

import Mathlib
import Definitions.Def_NeedPersuasion_Threshold_Model

set_option autoImplicit false
open NeedPersuasion.Threshold

theorem solution (M : Model) (hM : M.Standing) (π : ℕ → ℝ) (hπ : π ∈ PiAP M) :
    (∀ k q : ℕ, q < k → M.lamH ^ (k - q) * π q ≤ π k ∧ π k ≤ M.lam ^ (k - q) * π q) ∧
      (0 < M.lamH → ∀ k : ℕ, 0 < π k ∧ π k < 1) := by
  obtain ⟨hL, hH, hlam, -⟩ := hM
  obtain ⟨hnn, hsum, hrec, -, -⟩ := hπ
  have hlam0 : 0 ≤ M.lam := by unfold Model.lam; linarith
  have key : ∀ q d : ℕ, M.lamH ^ d * π q ≤ π (q + d) ∧ π (q + d) ≤ M.lam ^ d * π q := by
    intro q d
    induction d with
    | zero => simp
    | succ d ih =>
      obtain ⟨h1, h2⟩ := ih
      obtain ⟨r1, r2⟩ := hrec (q + d)
      constructor
      · calc M.lamH ^ (d + 1) * π q = M.lamH * (M.lamH ^ d * π q) := by ring
          _ ≤ M.lamH * π (q + d) := mul_le_mul_of_nonneg_left h1 hH
          _ ≤ π (q + (d + 1)) := by rw [← add_assoc]; exact r1
      · calc π (q + (d + 1)) = π (q + d + 1) := by rw [add_assoc]
          _ ≤ M.lam * π (q + d) := r2
          _ ≤ M.lam * (M.lam ^ d * π q) := mul_le_mul_of_nonneg_left h2 hlam0
          _ = M.lam ^ (d + 1) * π q := by ring
  refine ⟨?_, ?_⟩
  · intro k q hqk
    have := key q (k - q)
    rwa [Nat.add_sub_cancel' hqk.le] at this
  · intro hHpos k
    have h0 : 0 < π 0 := by
      by_contra hcon
      have hz : π 0 = 0 := le_antisymm (not_lt.1 hcon) (hnn 0)
      have hall : ∀ n, π n = 0 := by
        intro n
        have := (key 0 n).2
        simp only [zero_add, hz, mul_zero] at this
        exact le_antisymm this (hnn n)
      have : HasSum π 0 := by
        have : π = fun _ => 0 := funext hall
        rw [this]; exact hasSum_zero
      have := hsum.unique this
      norm_num at this
    have hpos : ∀ n, 0 < π n := by
      intro n
      have := (key 0 n).1
      simp only [zero_add] at this
      have : 0 < M.lamH ^ n * π 0 := mul_pos (pow_pos hHpos n) h0
      linarith [(key 0 n).1, show (0:ℕ) + n = n from by simp]
    refine ⟨hpos k, ?_⟩
    have hle : ∑ i ∈ ({k, k + 1} : Finset ℕ), π i ≤ 1 :=
      sum_le_hasSum _ (fun i _ => hnn i) hsum
    rw [Finset.sum_pair (by omega)] at hle
    linarith [hpos (k + 1)]
