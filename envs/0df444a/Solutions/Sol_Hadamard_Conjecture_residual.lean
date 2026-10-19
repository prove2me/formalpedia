-- Prove2me | solution 1 for Hadamard_Conjecture_residual
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ronr
-- created : 2026-09-06T00:04:46.07654+00:00
-- url     : https://prove2.me/submissions/f350fef2-d137-46e2-a259-acf240c0df27
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Hadamard_Conjecture_paley2_sylvester_case
import Theorems.Thm_Hadamard_Conjecture_residual2

open Matrix

theorem solution (k : ℕ)
    (hk1 : ¬ ∃ m : ℕ, k = 2 ^ m)
    (hk2 : ¬ ∃ q t : ℕ, Nat.Prime q ∧ q % 4 = 3 ∧ 4 * k = (q + 1) * 2 ^ t) :
    ∃ M : Matrix (Fin (4 * k)) (Fin (4 * k)) ℝ,
      (∀ i j, M i j ∈ ({1, -1} : Finset ℝ)) ∧
      |M.det| = ((4 * k : ℕ) : ℝ) ^ (((4 * k : ℕ) : ℝ) / 2) := by
  by_cases hcombo2 : ∃ q t : ℕ, Nat.Prime q ∧ q % 4 = 1 ∧ 4 * k = (2 * (q + 1)) * 2 ^ t
  · exact Hadamard_Conjecture_paley2_sylvester_case k hcombo2
  · exact Hadamard_Conjecture_residual2 k hk1 hk2 hcombo2
