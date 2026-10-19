-- Prove2me | solution 1 for InertialAVD.Algo.lemma_A_9
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:41:00.84187+00:00
-- url     : https://prove2.me/submissions/5a63c708-d9dd-4f44-93fd-66a8b70cd58f

import Mathlib

set_option autoImplicit false

open Filter Topology

theorem solution (a β : ℕ → ℝ) (c : ℝ)
    (ha : ∀ k, 0 ≤ a k) (hβ : ∀ j, 0 ≤ β j) (hβs : Summable β) (hc : 0 ≤ c)
    (h : ∀ k : ℕ, a k ^ 2 ≤ c ^ 2 + ∑ j ∈ Finset.Icc 1 k, β j * a j) :
    ∀ k : ℕ, a k ≤ c + ∑' j : ℕ, β (j + 1) := by
  intro k
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (Finset.range (k + 1)) a
    ⟨0, by simp⟩
  have hmk : a k ≤ a m := hmax k (by simp)
  have hs1 : Summable (fun j => β (j + 1)) := (summable_nat_add_iff 1).mpr hβs
  have hB : ∑ j ∈ Finset.Icc 1 m, β j ≤ ∑' j : ℕ, β (j + 1) := by
    have : ∑ j ∈ Finset.Icc 1 m, β j = ∑ j ∈ Finset.range m, β (j + 1) := by
      clear hmax hm hmk
      induction m with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
    rw [this]
    exact hs1.sum_le_tsum _ (fun j _ => hβ (j + 1))
  have hle : ∑ j ∈ Finset.Icc 1 m, β j * a j ≤ (∑ j ∈ Finset.Icc 1 m, β j) * a m := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun j hj => ?_)
    have hjm : j ≤ m := (Finset.mem_Icc.mp hj).2
    have hjk : j ∈ Finset.range (k + 1) := by
      have := Finset.mem_range.mp hm
      simp only [Finset.mem_range]; omega
    exact mul_le_mul_of_nonneg_left (hmax j hjk) (hβ j)
  have hBn : 0 ≤ ∑ j ∈ Finset.Icc 1 m, β j := Finset.sum_nonneg (fun j _ => hβ j)
  have h1 := h m
  have hm0 := ha m
  have key : a m ≤ c + ∑ j ∈ Finset.Icc 1 m, β j := by
    by_contra hcon
    push_neg at hcon
    set B := ∑ j ∈ Finset.Icc 1 m, β j
    nlinarith
  linarith
