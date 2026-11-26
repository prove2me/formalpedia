-- Prove2me | solution 1 for MasulloRH.fixed_gaussian_approximation_beyond_first_fifteen
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T21:51:28.573226+00:00
-- url     : https://prove2.me/submissions/b274a6bc-3bd7-49fd-b217-0c96dd66940c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_nine_rational_theta_shifts_on_every_gaussian_window
import Theorems.Thm_MasulloRH_fixed_gaussian_approximation_from_tolerance_16384

open MasulloRH.NineShift MasulloRH.FixedGaussianTest MasulloRH.GaussianApproximation

theorem solution :
    ∀ j : ℕ, 16 ≤ j → ∃ k : ℕ, j+1≤k ∧ ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
      energy (fullCenter k) (fullWidth k) (residual 0
        (fun i => ((a i).1:ℂ)+((a i).2:ℂ)*Complex.I) (fun i => (y i:ℝ))) < 1/((j:ℝ)+1) := by 
  intro j _
  by_cases h : 16384 ≤ j
  · exact MasulloRH.fixed_gaussian_approximation_from_tolerance_16384 j h
  · have hh := MasulloRH.nine_rational_theta_shifts_on_every_gaussian_window.2 (j+1)
    refine ⟨j+1,le_rfl,9,fun i => (coeff i,0),shift,?_⟩
    simp only [Rat.cast_zero,zero_mul,add_zero]
    apply hh.trans_le
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast (show j+1≤16384 by omega)
