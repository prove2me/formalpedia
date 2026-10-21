-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.weighted_shear_roundtrip_series
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T05:58:32.333157+00:00
-- url     : https://prove2.me/submissions/5575b719-9a40-4d37-ae3e-81766109c89a

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_subst_aeval_comp
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_shear_coordinate_roundtrip

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (D : Fin m → PowerSeries ℂ)
    (hD : ∀ i : Fin m, ∀ n : ℕ,
      (n : ℝ) * q 0 < q i.succ → PowerSeries.coeff n (D i) = 0)
    (Q : MvPolynomial (Fin (m + 1)) ℂ) :
    MvPowerSeries.subst
      (Fin.cases (MvPowerSeries.X 0)
        (fun i => MvPowerSeries.X i.succ - liftLogSeries m (D i)))
      (MvPolynomial.aeval
        (Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i))) Q) =
    MvPolynomial.aeval MvPowerSeries.X Q := by
  rcases OAI.PiExponent.LogarithmicJetIdeals.weighted_shear_coordinate_roundtrip
      q hq D hD with ⟨ha, hb, hcoord⟩
  rw [OAI.PiExponent.LogarithmicJetIdeals.subst_aeval_comp
        (a := Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i)))
        (b := Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ - liftLogSeries m (D i)))
        ha hb Q, hcoord]