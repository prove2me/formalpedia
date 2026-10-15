-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.weighted_triangular_series_shear_reflects_vanishing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T22:41:22.622505+00:00
-- url     : https://prove2.me/submissions/5e9c2ba7-86a3-4187-8d12-c527bd4f3bb1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_shear_inverse_preserves_filtered_vanishing
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_shear_roundtrip_coeff

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem solution
    {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (D : Fin m → PowerSeries ℂ)
    (hD : ∀ i : Fin m, ∀ n : ℕ,
      (n : ℝ) * q 0 < q i.succ → PowerSeries.coeff n (D i) = 0)
    (B : ℝ) (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (hcoeff : ∀ a : Fin (m + 1) → ℕ,
      (∑ j, q j * (a j : ℝ)) < B →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (MvPolynomial.aeval
          (Fin.cases (MvPowerSeries.X 0)
            (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i))) Q) = 0) :
    ∀ a : Fin (m + 1) → ℕ,
      (∑ j, q j * (a j : ℝ)) < B →
      MvPolynomial.coeff (InterpolationMatrix.exponentVector a) Q = 0 := by
  intro a ha
  have hinv :=
    OAI.PiExponent.LogarithmicJetIdeals.weighted_shear_inverse_preserves_filtered_vanishing
      q hq D hD B
      (MvPolynomial.aeval
        (Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i))) Q)
      (fun a ha => hcoeff a ha) a ha
  have hround :=
    OAI.PiExponent.LogarithmicJetIdeals.weighted_shear_roundtrip_coeff
      q hq D hD Q a
  rw [← hround]
  exact hinv