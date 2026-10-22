-- Prove2me | solution 1 for IRLSM.RIP.shelling_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:32:21.787289+00:00
-- url     : https://prove2.me/submissions/71d82f0c-96fe-4fd9-accb-e628782764a9

import Mathlib
set_option autoImplicit false

theorem solution (s : ℕ → ℝ) (hs : Antitone s) (h0 : ∀ i, 0 ≤ s i) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (j : ℕ) :
    Real.sqrt (∑ i ∈ Finset.Ico ((j + 1) * ℓ) ((j + 2) * ℓ), s i ^ 2) ≤
      (1 / Real.sqrt ℓ) * ∑ i ∈ Finset.Ico (j * ℓ) ((j + 1) * ℓ), s i := by
  set A : ℝ := ∑ i ∈ Finset.Ico (j * ℓ) ((j + 1) * ℓ), s i with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun i _ => h0 i)
  have hcard1 : (Finset.Ico (j * ℓ) ((j + 1) * ℓ)).card = ℓ := by
    simp only [Nat.card_Ico]
    have : (j + 1) * ℓ = j * ℓ + ℓ := by ring
    omega
  have hcard2 : (Finset.Ico ((j + 1) * ℓ) ((j + 2) * ℓ)).card = ℓ := by
    simp only [Nat.card_Ico]
    have : (j + 2) * ℓ = (j + 1) * ℓ + ℓ := by ring
    omega
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  -- each entry of the second block is at most the average of the first block
  have hbound : ∀ i ∈ Finset.Ico ((j + 1) * ℓ) ((j + 2) * ℓ), s i ≤ A / ℓ := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hle : ∀ k ∈ Finset.Ico (j * ℓ) ((j + 1) * ℓ), s i ≤ s k := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      exact hs (by omega)
    have := Finset.card_nsmul_le_sum (Finset.Ico (j * ℓ) ((j + 1) * ℓ)) s (s i) hle
    rw [hcard1, nsmul_eq_mul] at this
    rw [le_div_iff₀ hℓr]
    linarith
  have hsum : ∑ i ∈ Finset.Ico ((j + 1) * ℓ) ((j + 2) * ℓ), s i ^ 2 ≤ ℓ * (A / ℓ) ^ 2 := by
    calc ∑ i ∈ Finset.Ico ((j + 1) * ℓ) ((j + 2) * ℓ), s i ^ 2
        ≤ ∑ i ∈ Finset.Ico ((j + 1) * ℓ) ((j + 2) * ℓ), (A / ℓ) ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          exact pow_le_pow_left₀ (h0 i) (hbound i hi) 2
      _ = ℓ * (A / ℓ) ^ 2 := by
          rw [Finset.sum_const, hcard2, nsmul_eq_mul]
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  calc ∑ i ∈ Finset.Ico ((j + 1) * ℓ) ((j + 2) * ℓ), s i ^ 2 ≤ ℓ * (A / ℓ) ^ 2 := hsum
    _ = (1 / Real.sqrt ℓ * A) ^ 2 := by
        have h2 : (1 / Real.sqrt ℓ) ^ 2 = 1 / ℓ := by
          rw [div_pow, one_pow, Real.sq_sqrt hℓr.le]
        rw [mul_pow, h2]
        field_simp
