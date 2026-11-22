-- Prove2me | solution 1 for MasulloRH.sparse_subpower_square_prime_energy
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-21T09:17:11.39861+00:00
-- url     : https://prove2.me/submissions/981d67b6-c2b4-403c-aa2e-436d9c5ff00f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_finite_square_prime_energy_cap

open Finset ArithmeticFunction MeasureTheory Set
set_option autoImplicit false

private theorem seven_mul_succ_le_two_pow (j : ℕ) (hj : 7 ≤ j) :
    7 * (j + 1) ≤ 2 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
      rw [pow_succ]
      omega

private theorem eighty_one_le_sparse_scale (j : ℕ) (hj : 7 ≤ j) :
    (81 : ℝ) ≤ (((2 : ℕ) ^ (2 ^ j) : ℕ) : ℝ) ^ (1 / ((j : ℝ) + 1)) := by
  have hden : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hgrowth : (7 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) / ((j : ℝ) + 1) := by
    apply (le_div_iff₀ hden).2
    exact_mod_cast seven_mul_succ_le_two_pow j hj
  have hpow : (((2 : ℕ) ^ (2 ^ j) : ℕ) : ℝ) = (2 : ℝ) ^ (2 ^ j) := by norm_cast
  rw [hpow, ← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    (81 : ℝ) ≤ (2 : ℝ) ^ (7 : ℝ) := by norm_num
    _ ≤ (2 : ℝ) ^ (((2 ^ j : ℕ) : ℝ) / ((j : ℝ) + 1)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hgrowth
    _ = (2 : ℝ) ^ (((2 ^ j : ℕ) : ℝ) * (1 / ((j : ℝ) + 1))) := by
      simp only [div_eq_mul_inv, one_mul]

theorem solution :
    let G (x : ℝ) := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)
    let E (N : ℕ) := ∑ n ∈ range N, let k := (n:ℝ)+4; (G (k^2))^2/(k^3*(1+Real.log k)^2)
    ∃ J : ℕ,∀ j ≥ J, let D := (2:ℕ)^(2^j)
      E D ≤ (D:ℝ)^(1/((j:ℝ)+1)) := by
  dsimp
  refine ⟨7, ?_⟩
  intro j hj
  exact (MasulloRH.finite_square_prime_energy_cap ((2 : ℕ) ^ (2 ^ j))).trans
    (eighty_one_le_sparse_scale j hj)
