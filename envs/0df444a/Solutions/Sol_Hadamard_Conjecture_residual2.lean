-- Prove2me | solution 1 for Hadamard_Conjecture_residual2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ronr
-- created : 2026-09-06T00:29:55.825996+00:00
-- url     : https://prove2.me/submissions/fad94bae-b1be-4f20-a4a7-3d8f32a3cd73
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Hadamard_Conjecture_paley_primepower_case
import Theorems.Thm_Hadamard_Conjecture_residual3

open Matrix

theorem solution (k : ℕ)
    (hk1 : ¬ ∃ m : ℕ, k = 2 ^ m)
    (hk2 : ¬ ∃ q t : ℕ, Nat.Prime q ∧ q % 4 = 3 ∧ 4 * k = (q + 1) * 2 ^ t)
    (hk3 : ¬ ∃ q t : ℕ, Nat.Prime q ∧ q % 4 = 1 ∧ 4 * k = (2 * (q + 1)) * 2 ^ t) :
    ∃ M : Matrix (Fin (4 * k)) (Fin (4 * k)) ℝ,
      (∀ i j, M i j ∈ ({1, -1} : Finset ℝ)) ∧
      |M.det| = ((4 * k : ℕ) : ℝ) ^ (((4 * k : ℕ) : ℝ) / 2) := by
  by_cases hpp : ∃ p n t : ℕ, Nat.Prime p ∧ 0 < n ∧
      ((p ^ n % 4 = 3 ∧ 4 * k = (p ^ n + 1) * 2 ^ t) ∨
       (p ^ n % 4 = 1 ∧ 4 * k = (2 * (p ^ n + 1)) * 2 ^ t))
  · exact Hadamard_Conjecture_paley_primepower_case k hpp
  · exact Hadamard_Conjecture_residual3 k hk1 hpp
