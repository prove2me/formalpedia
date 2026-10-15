-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.weighted_shear_roundtrip_coeff
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T23:15:42.645203+00:00
-- url     : https://prove2.me/submissions/7a08d593-e8a5-4da2-b490-7104dba208cd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_subst_inverse_shear
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_identity_aeval

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (D : Fin m → PowerSeries ℂ)
    (hD : ∀ i : Fin m, ∀ n : ℕ,
      (n : ℝ) * q 0 < q i.succ → PowerSeries.coeff n (D i) = 0)
    (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (a : Fin (m + 1) → ℕ) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (MvPowerSeries.subst
        (Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ - liftLogSeries m (D i)))
        (MvPolynomial.aeval
          (Fin.cases (MvPowerSeries.X 0)
            (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i))) Q)) =
    MvPolynomial.coeff (InterpolationMatrix.exponentVector a) Q := by
  rw [OAI.PiExponent.LogarithmicJetIdeals.subst_inverse_shear D Q]
  exact OAI.PiExponent.LogarithmicJetIdeals.coeff_identity_aeval Q a