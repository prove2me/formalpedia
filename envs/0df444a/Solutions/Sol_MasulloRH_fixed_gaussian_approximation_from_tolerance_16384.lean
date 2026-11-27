-- Prove2me | solution 1 for MasulloRH.fixed_gaussian_approximation_from_tolerance_16384
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T22:29:46.045824+00:00
-- url     : https://prove2.me/submissions/e73e6ce2-c8a8-4737-a533-2b04f8d87191
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_fixed_gaussian_tail_iff_factorial_gram_tests
import Theorems.Thm_MasulloRH_factorial_gram_negative_direction_from_tolerance_16666
import Theorems.Thm_MasulloRH_thirty_seven_shift_gram_passes_first_16666_tests

open MasulloRH.FixedGaussianTest MasulloRH.GaussianApproximation

theorem solution :
    ∀ j : ℕ, 16384 ≤ j → ∃ k : ℕ, j+1 ≤ k ∧ ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
      energy (fullCenter k) (fullWidth k) (residual 0
        (fun i => ((a i).1:ℂ)+((a i).2:ℂ)*Complex.I) (fun i => (y i:ℝ))) < 1/((j:ℝ)+1) := by
  apply MasulloRH.fixed_gaussian_tail_iff_factorial_gram_tests.2
  intro j _
  by_cases h : j < 16666
  · exact ⟨3,MasulloRH.thirty_seven_shift_gram_passes_first_16666_tests j h⟩
  · exact MasulloRH.factorial_gram_negative_direction_from_tolerance_16666 j (Nat.le_of_not_gt h)
