-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.weighted_truncation_preserves_filtered_substitution
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T20:40:34.062398+00:00
-- url     : https://prove2.me/submissions/cc193ee7-f763-4ca4-aa6f-dec87d777e2a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_triangular_series_shear_reflects_vanishing
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_polynomial_series_coordinate_change_factorization

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem solution
    {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (c : Fin m → ℂ) (G : Fin m → PowerSeries ℂ) (T : Fin m → ℕ)
    (hT : ∀ i : Fin m, q i.succ ≤ (T i : ℝ) * q 0)
    (B : ℝ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hcoeff : ∀ a : Fin (m + 1) → ℕ,
      (∑ j, q j * (a j : ℝ)) < B →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (MvPolynomial.aeval
          (Fin.cases (1 + MvPowerSeries.X 0)
            (fun i => MvPowerSeries.C (c i) + MvPowerSeries.X i.succ +
              liftLogSeries m (G i))) P) = 0) :
    ∀ a : Fin (m + 1) → ℕ,
      (∑ j, q j * (a j : ℝ)) < B →
      MvPolynomial.coeff (InterpolationMatrix.exponentVector a)
        (MvPolynomial.aeval
          (Fin.cases (1 + MvPolynomial.X 0)
            (fun i => MvPolynomial.C (c i) + MvPolynomial.X i.succ +
              Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0)
                (PowerSeries.trunc (T i) (G i)))) P) = 0 := by
  let H : Fin m → Polynomial ℂ := fun i => PowerSeries.trunc (T i) (G i)
  let D : Fin m → PowerSeries ℂ := fun i => G i - (H i : PowerSeries ℂ)
  let Q : MvPolynomial (Fin (m + 1)) ℂ :=
    MvPolynomial.aeval
      (Fin.cases (1 + MvPolynomial.X 0)
        (fun i => MvPolynomial.C (c i) + MvPolynomial.X i.succ +
          Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) (H i))) P
  have hD : ∀ i : Fin m, ∀ n : ℕ,
      (n : ℝ) * q 0 < q i.succ → PowerSeries.coeff n (D i) = 0 := by
    intro i n hn
    have hnT : n < T i := by
      by_contra hnT
      have hTn : (T i : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Nat.le_of_not_gt hnT)
      have hbound : q i.succ ≤ (n : ℝ) * q 0 :=
        (hT i).trans (mul_le_mul_of_nonneg_right hTn (hq 0).le)
      exact (not_lt_of_ge hbound) hn
    change PowerSeries.coeff n
      (G i - (PowerSeries.trunc (T i) (G i) : PowerSeries ℂ)) = 0
    rw [map_sub, PowerSeries.coeff_coe_trunc_of_lt hnT, sub_self]
  have hfactor :
      MvPolynomial.aeval
        (Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i))) Q =
      MvPolynomial.aeval
        (Fin.cases (1 + MvPowerSeries.X 0)
          (fun i => MvPowerSeries.C (c i) + MvPowerSeries.X i.succ +
            liftLogSeries m (G i))) P := by
    exact OAI.PiExponent.LogarithmicJetIdeals.polynomial_series_coordinate_change_factorization
      c G H P
  have hshear : ∀ a : Fin (m + 1) → ℕ,
      (∑ j, q j * (a j : ℝ)) < B →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (MvPolynomial.aeval
          (Fin.cases (MvPowerSeries.X 0)
            (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i))) Q) = 0 := by
    intro a ha
    rw [hfactor]
    exact hcoeff a ha
  exact OAI.PiExponent.LogarithmicJetIdeals.weighted_triangular_series_shear_reflects_vanishing
    q hq D hD B Q hshear
