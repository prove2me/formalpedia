-- Prove2me | solution 1 for Hadamard_Conjecture_nonpoweroftwo
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ronr
-- created : 2026-09-05T22:15:31.389939+00:00
-- url     : https://prove2.me/submissions/283ca722-dfec-4ed3-a747-bbb8b7c61d36
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Hadamard_Conjecture_paley_sylvester_case
import Theorems.Thm_Hadamard_Conjecture_residual

open Matrix

theorem solution (k : ℕ) (hk : ¬ ∃ m : ℕ, k = 2 ^ m) :
    ∃ M : Matrix (Fin (4 * k)) (Fin (4 * k)) ℝ,
      (∀ i j, M i j ∈ ({1, -1} : Finset ℝ)) ∧
      |M.det| = ((4 * k : ℕ) : ℝ) ^ (((4 * k : ℕ) : ℝ) / 2) := by
  by_cases hcombo : ∃ q t : ℕ, Nat.Prime q ∧ q % 4 = 3 ∧ 4 * k = (q + 1) * 2 ^ t
  · exact Hadamard_Conjecture_paley_sylvester_case k hcombo
  · exact Hadamard_Conjecture_residual k hk hcombo
