-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.subst_formalJet_log_tail_eq_truncatedCoordinate_aeval
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:29:10.644503+00:00
-- url     : https://prove2.me/submissions/a90683d2-f9cc-4ae7-8403-b40738a918e2

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinates
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.Tactic.Abel
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_hasSubst_logTailCoordinates
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_subst_liftLogSeries_fixed

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (P : MvPolynomial (Fin (m + 1)) ℂ) :
    MvPowerSeries.subst
        (Fin.cases (MvPowerSeries.X 0)
          (fun i : Fin m => MvPowerSeries.X i.succ + liftLogSeries m
            ((InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) -
              PowerSeries.log ℂ)))
        (formalJet c P) =
      MvPolynomial.aeval
        (Fin.cases (1 + MvPowerSeries.X 0)
          (fun i : Fin m => MvPowerSeries.C (c i) + MvPowerSeries.X i.succ +
            liftLogSeries m (InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ))) P := by
  let a : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ :=
    Fin.cases (MvPowerSeries.X 0)
      (fun i : Fin m => MvPowerSeries.X i.succ + liftLogSeries m
        ((InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) -
          PowerSeries.log ℂ))
  have ha : MvPowerSeries.HasSubst a :=
    OAI.PiExponent.LogarithmicJetIdeals.hasSubst_logTailCoordinates T
  have hfixed (f : PowerSeries ℂ) :
      MvPowerSeries.subst a (liftLogSeries m f) = liftLogSeries m f :=
    OAI.PiExponent.LogarithmicJetIdeals.subst_liftLogSeries_fixed a ha rfl f
  change MvPowerSeries.subst a (formalJet c P) = _
  rw [formalJet, ← MvPowerSeries.substAlgHom_apply ha,
    MvPolynomial.comp_aeval_apply]
  apply congrArg (fun b : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ =>
    MvPolynomial.aeval b P)
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [Fin.cases_zero, map_add, map_one, MvPowerSeries.substAlgHom_X]
    rfl
  · simp only [Fin.cases_succ, map_add]
    simp only [MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_C,
      MvPowerSeries.subst_X ha, hfixed]
    change MvPowerSeries.C (c i) +
      (MvPowerSeries.X i.succ + liftLogSeries m
        ((InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) -
          PowerSeries.log ℂ)) + liftLogSeries m (PowerSeries.log ℂ) = _
    rw [map_sub]
    abel
