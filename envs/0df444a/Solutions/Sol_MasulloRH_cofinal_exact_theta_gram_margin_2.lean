-- Prove2me | solution 2 for MasulloRH.cofinal_exact_theta_gram_margin
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T08:54:08.528635+00:00
-- url     : https://prove2.me/submissions/a60b235d-b9ca-422b-8eb1-7465d91fed68
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_theta_gram_margin_iff_not_posSemidef
import Theorems.Thm_MasulloRH_cofinal_theta_gram_negative_direction
import Definitions.Def_MasulloRH_GaussianThetaApproximation

open MasulloRH.GaussianApproximation MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false

theorem solution :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
        let δ : ℝ := 1 / (16 * ((n : ℝ) + 1))
        let u : Fin (m + 1) → ℝ → ℂ := Fin.cons (pulse n)
          (fun i x => theta (x - (y i : ℝ)))
        let d : Fin (m + 1) → ℂ := Fin.cons 1
          (fun i => -(((a i).1 : ℂ) + ((a i).2 : ℂ) * Complex.I))
        (∑ i, ∑ j, conj (d i) * d j *
          (∫ x : ℝ,
            (Real.exp (2 * (3 / 4) * x + 2 * (1 / 4 - δ) * |x|) : ℂ) *
              conj (u i x) * u j x)).re < δ / 2 := by
  intro N
  obtain ⟨n, hn, m, y, hneg⟩ := MasulloRH.cofinal_theta_gram_negative_direction N
  obtain ⟨a, ha⟩ := (MasulloRH.theta_gram_margin_iff_not_posSemidef n m y).mpr hneg
  exact ⟨n, hn, m, a, y, ha⟩
