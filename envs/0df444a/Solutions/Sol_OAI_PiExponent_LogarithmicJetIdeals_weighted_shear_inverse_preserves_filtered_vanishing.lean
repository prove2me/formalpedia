-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.weighted_shear_inverse_preserves_filtered_vanishing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T19:23:43.712435+00:00
-- url     : https://prove2.me/submissions/1d5383cc-234d-4556-959a-e2b050296ab4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_subst_preserves_filtered_vanishing
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_shear_coordinate_coefficients

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

set_option maxHeartbeats 2000000 in
theorem solution
    {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (D : Fin m → PowerSeries ℂ)
    (hD : ∀ i : Fin m, ∀ n : ℕ,
      (n : ℝ) * q 0 < q i.succ → PowerSeries.coeff n (D i) = 0)
    (B : ℝ) (F : MvPowerSeries (Fin (m + 1)) ℂ)
    (hF : ∀ a : Fin (m + 1) → ℕ,
      (∑ j, q j * (a j : ℝ)) < B →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) F = 0) :
    ∀ a : Fin (m + 1) → ℕ,
      (∑ j, q j * (a j : ℝ)) < B →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (MvPowerSeries.subst
          (σ := Fin (m + 1)) (τ := Fin (m + 1)) (R := ℂ) (S := ℂ)
          (Fin.cases
            (motive := fun _ : Fin (m + 1) => MvPowerSeries (Fin (m + 1)) ℂ)
            (MvPowerSeries.X (R := ℂ) (0 : Fin (m + 1)))
            (fun i : Fin m =>
              MvPowerSeries.X (R := ℂ) i.succ - liftLogSeries m (D i))) F) = 0 := by
  -- Fix the motive before elaborating either branch of the substitution.
  let sigma : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ :=
    Fin.cases
      (motive := fun _ : Fin (m + 1) => MvPowerSeries (Fin (m + 1)) ℂ)
      (MvPowerSeries.X (R := ℂ) (0 : Fin (m + 1)))
      (fun i : Fin m =>
        MvPowerSeries.X (R := ℂ) i.succ - liftLogSeries m (D i))
  have hsigma : ∀ i : Fin (m + 1), ∀ b : Fin (m + 1) →₀ ℕ,
      MvPowerSeries.coeff b (sigma i) ≠ 0 →
        q i ≤ ∑ j, q j * (b j : ℝ) :=
    OAI.PiExponent.LogarithmicJetIdeals.weighted_shear_coordinate_coefficients
      (m := m) q hq D hD
  exact OAI.PiExponent.LogarithmicJetIdeals.weighted_subst_preserves_filtered_vanishing
    (m := m) q hq sigma hsigma B F hF
