-- Prove2me | solution 1 for MasulloRH.cofinal_theta_gram_negative_direction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T19:27:37.255903+00:00
-- url     : https://prove2.me/submissions/a37f304c-54cb-41fe-9a48-91742ed37df9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_riemannHypothesis_iff_expanding_fixed_gaussian_windows
import Theorems.Thm_MasulloRH_fixed_gaussian_cofinal_tests_iff_each_window
import Theorems.Thm_MasulloRH_fixed_gaussian_approximation_on_remaining_windows
import Theorems.Thm_MasulloRH_theta_gram_negative_direction_at_every_scale_of_RH
import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Basis

open MasulloRH.GaussianApproximation MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false

theorem solution :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ (m : ℕ) (y : Fin m → ℚ),
    let δ : ℝ := 1 / (16 * ((n : ℝ) + 1))
    let u : Fin (m + 1) → ℝ → ℂ := Fin.cons (pulse n) (fun i x => theta (x - (y i : ℝ)))
    let G : Matrix (Fin (m+1)) (Fin (m+1)) ℂ := fun i j =>
      ∫ x : ℝ, (Real.exp (2*(3/4)*x + 2*(1/4-δ)*|x|) : ℂ) * conj (u i x) * u j x
    let K : Matrix (Fin (m+1)) (Fin (m+1)) ℝ := fun i j => (G i j).re
    ¬ (K - Matrix.single 0 0 (δ / 2)).PosSemidef := by
  intro N
  have hRH := MasulloRH.riemannHypothesis_iff_expanding_fixed_gaussian_windows.2
      (MasulloRH.fixed_gaussian_cofinal_tests_iff_each_window.2
        MasulloRH.fixed_gaussian_approximation_on_remaining_windows)
  exact ⟨N,le_rfl,MasulloRH.theta_gram_negative_direction_at_every_scale_of_RH hRH N⟩
