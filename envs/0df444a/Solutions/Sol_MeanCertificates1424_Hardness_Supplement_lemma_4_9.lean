-- Prove2me | solution 1 for MeanCertificates1424.Hardness.Supplement.lemma_4_9
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:53:53.629198+00:00
-- url     : https://prove2.me/submissions/846b17c7-1b10-4628-b988-20eee958baa0

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_General

open MeanCertificates1424.Hardness MeanCertificates1424.Hardness.Supplement

lemma mc_size_pos : ∀ T : MergeTree, 1 ≤ T.size
  | .leaf => by simp [MergeTree.size]
  | .node l r => by
      have := mc_size_pos l
      simp only [MergeTree.size]; omega

lemma mc_cost_zero : ∀ T : MergeTree, T.cost 0 + 1 = T.size
  | .leaf => by simp [MergeTree.cost, MergeTree.size]
  | .node l r => by
      have hl := mc_cost_zero l
      have hr := mc_cost_zero r
      simp only [MergeTree.cost, MergeTree.size]
      simp
      omega

def mcF (κ n : ℕ) : ℤ :=
  if n ≤ κ then 2 * (n : ℤ) ^ 2 - 2 * n else 6 * (κ : ℤ) * n - 4 * (κ : ℤ) ^ 2

lemma mc_merge (κ A C : ℕ) (hκ : 1 ≤ κ) (hA : 1 ≤ A) (hC : 1 ≤ C) :
    mcF κ A + mcF κ C + ((min κ A : ℕ) + 1 : ℤ) * ((min κ C : ℕ) + 1 : ℤ) ≤ mcF κ (A + C) := by
  have hκ' : (1 : ℤ) ≤ κ := by exact_mod_cast hκ
  have hA' : (1 : ℤ) ≤ A := by exact_mod_cast hA
  have hC' : (1 : ℤ) ≤ C := by exact_mod_cast hC
  unfold mcF
  by_cases h1 : A ≤ κ <;> by_cases h2 : C ≤ κ
  · have e1 : min κ A = A := min_eq_right h1
    have e2 : min κ C = C := min_eq_right h2
    rw [e1, e2, if_pos h1, if_pos h2]
    have h1' : (A : ℤ) ≤ κ := by exact_mod_cast h1
    have h2' : (C : ℤ) ≤ κ := by exact_mod_cast h2
    by_cases h3 : A + C ≤ κ
    · rw [if_pos h3]; push_cast; nlinarith [mul_nonneg (sub_nonneg.2 hA') (sub_nonneg.2 hC')]
    · rw [if_neg h3]
      have h3' : (κ : ℤ) < A + C := by exact_mod_cast (not_le.1 h3)
      push_cast
      nlinarith [mul_nonneg (sub_nonneg.2 hA') (sub_nonneg.2 hC'),
        mul_nonneg (sub_nonneg.2 h3'.le) (show (0 : ℤ) ≤ 2 * κ - (A + C) by linarith)]
  · have e1 : min κ A = A := min_eq_right h1
    have e2 : min κ C = κ := min_eq_left (le_of_lt (not_le.1 h2))
    have h3 : ¬ (A + C ≤ κ) := by omega
    rw [e1, e2, if_pos h1, if_neg h2, if_neg h3]
    have h1' : (A : ℤ) ≤ κ := by exact_mod_cast h1
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.2 hA') (sub_nonneg.2 hκ'), mul_nonneg (sub_nonneg.2 h1') (sub_nonneg.2 hA')]
  · have e1 : min κ A = κ := min_eq_left (le_of_lt (not_le.1 h1))
    have e2 : min κ C = C := min_eq_right h2
    have h3 : ¬ (A + C ≤ κ) := by omega
    rw [e1, e2, if_neg h1, if_pos h2, if_neg h3]
    have h2' : (C : ℤ) ≤ κ := by exact_mod_cast h2
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.2 hC') (sub_nonneg.2 hκ'), mul_nonneg (sub_nonneg.2 h2') (sub_nonneg.2 hC')]
  · have e1 : min κ A = κ := min_eq_left (le_of_lt (not_le.1 h1))
    have e2 : min κ C = κ := min_eq_left (le_of_lt (not_le.1 h2))
    have h3 : ¬ (A + C ≤ κ) := by omega
    rw [e1, e2, if_neg h1, if_neg h2, if_neg h3]
    push_cast
    nlinarith

lemma mc_cost_le (κ : ℕ) (hκ : 1 ≤ κ) : ∀ T : MergeTree, (T.cost κ : ℤ) ≤ mcF κ T.size
  | .leaf => by simp [MergeTree.cost, MergeTree.size, mcF, hκ]
  | .node l r => by
      have hl := mc_cost_le κ hκ l
      have hr := mc_cost_le κ hκ r
      have hm := mc_merge κ l.size r.size hκ (mc_size_pos l) (mc_size_pos r)
      simp only [MergeTree.cost, MergeTree.size]
      push_cast at hm ⊢
      linarith

lemma mcF_le (κ n : ℕ) (hκ : 1 ≤ κ) (hn : 1 ≤ n) : mcF κ n ≤ 8 * κ * n := by
  unfold mcF
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hκ' : (1 : ℤ) ≤ κ := by exact_mod_cast hκ
  split_ifs with h
  · have h' : (n : ℤ) ≤ κ := by exact_mod_cast h
    nlinarith
  · nlinarith

theorem solution (κ : ℕ) (T : MergeTree) :
    (κ = 0 → T.cost κ = T.size - 1) ∧ (1 ≤ κ → T.cost κ ≤ 8 * κ * T.size) := by
  constructor
  · intro h; subst h; have := mc_cost_zero T; omega
  · intro hκ
    have h1 := mc_cost_le κ hκ T
    have h2 := mcF_le κ T.size hκ (mc_size_pos T)
    have : (T.cost κ : ℤ) ≤ ((8 * κ * T.size : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
