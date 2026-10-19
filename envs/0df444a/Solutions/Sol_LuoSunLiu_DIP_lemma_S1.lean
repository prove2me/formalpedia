-- Prove2me | solution 1 for LuoSunLiu.DIP.lemma_S1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T20:26:26.510981+00:00
-- url     : https://prove2.me/submissions/8716ff08-8fe8-4091-829b-9abe9000d560

import Mathlib
set_option autoImplicit false

theorem solution (S1 : Finset ℕ) (S2 : Set ℕ) (hS : (S1 : Set ℕ) ⊆ S2) (hne : S1.Nonempty)
    (a b : ℕ → ℝ) (δ : ℝ) (ha : ∀ i ∈ S2, ∀ j ∈ S2, |a i - a j| ≤ δ)
    (hb : ∀ i ∈ S1, 0 < b i) :
    ∀ j ∈ S2, |(∑ i ∈ S1, b i * a i) / (∑ i ∈ S1, b i) - a j| ≤ δ := by
  intro j hj
  have hpos : 0 < ∑ i ∈ S1, b i := Finset.sum_pos hb hne
  have key : (∑ i ∈ S1, b i * a i) / (∑ i ∈ S1, b i) - a j
      = (∑ i ∈ S1, b i * (a i - a j)) / (∑ i ∈ S1, b i) := by
    field_simp
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [key, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  calc |∑ i ∈ S1, b i * (a i - a j)| ≤ ∑ i ∈ S1, |b i * (a i - a j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S1, b i * δ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_of_pos (hb i hi)]
        exact mul_le_mul_of_nonneg_left (ha i (hS hi) j hj) (hb i hi).le
    _ = δ * ∑ i ∈ S1, b i := by rw [← Finset.sum_mul, mul_comm]
