-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_sheared_substitution_formula
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T16:20:25.51299+00:00
-- url     : https://prove2.me/submissions/d53dda7b-bb05-4c17-8067-1f4605d5ad61

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : Nat}
    (center : Fin m -> Complex)
    (Q : MvPolynomial (Fin (m + 1)) Complex) :
    OAI.PiExponent.AdmissibleFormalInterpolation.formalJet center (MvPolynomial.aeval
      (Fin.cases (MvPolynomial.X 0 - MvPolynomial.C 1)
        (fun i => MvPolynomial.X i.succ - MvPolynomial.C (center i) -
          (MvPolynomial.X 0 - MvPolynomial.C 1))) Q) =
      MvPolynomial.aeval
        (Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ +
            OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries m (PowerSeries.log ℂ)
              - MvPowerSeries.X 0)) Q := by
  have hmain : (OAI.PiExponent.AdmissibleFormalInterpolation.formalJet center).comp
      (MvPolynomial.aeval
        (Fin.cases (MvPolynomial.X 0 - MvPolynomial.C 1)
          (fun i => MvPolynomial.X i.succ - MvPolynomial.C (center i) -
            (MvPolynomial.X 0 - MvPolynomial.C 1)))) =
      MvPolynomial.aeval
        (Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ +
            OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries m (PowerSeries.log ℂ)
              - MvPowerSeries.X 0)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    refine Fin.cases ?_ ?_ i
    · rw [Fin.cases_zero, map_sub, map_one]
      have hX : OAI.PiExponent.AdmissibleFormalInterpolation.formalJet center
          (MvPolynomial.X (0 : Fin (m + 1))) =
          (1 : MvPowerSeries (Fin (m + 1)) Complex) + MvPowerSeries.X 0 := by
        simp [OAI.PiExponent.AdmissibleFormalInterpolation.formalJet]
      have h1 : (OAI.PiExponent.AdmissibleFormalInterpolation.formalJet center)
          (1 : MvPolynomial (Fin (m + 1)) Complex) = 1 := map_one _
      rw [hX, h1]
      simp
    · intro j
      rw [Fin.cases_succ, Fin.cases_succ, map_sub, map_sub, map_sub]
      have hX : OAI.PiExponent.AdmissibleFormalInterpolation.formalJet center
          (MvPolynomial.X (Fin.succ j)) =
          MvPowerSeries.C (center j) + MvPowerSeries.X j.succ +
            OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries m (PowerSeries.log ℂ) := by
        simp [OAI.PiExponent.AdmissibleFormalInterpolation.formalJet]
      have hC : OAI.PiExponent.AdmissibleFormalInterpolation.formalJet center
          (MvPolynomial.C (center j)) = MvPowerSeries.C (center j) := by
        rw [MvPolynomial.C_eq_algebraMap]
        have h := MvPolynomial.aeval_C (Fin.cases (1 + MvPowerSeries.X (0 : Fin (m + 1)))
          (fun i => MvPowerSeries.C (center i) + MvPowerSeries.X i.succ
            + OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries m (PowerSeries.log ℂ)))
          (center j)
        rw [MvPowerSeries.c_eq_algebraMap] at h
        exact h
      rw [hX, hC]
      have hX0 : OAI.PiExponent.AdmissibleFormalInterpolation.formalJet center
          (MvPolynomial.X (0 : Fin (m + 1))) =
          (1 : MvPowerSeries (Fin (m + 1)) Complex) + MvPowerSeries.X 0 := by
        simp [OAI.PiExponent.AdmissibleFormalInterpolation.formalJet]
      have h1 : OAI.PiExponent.AdmissibleFormalInterpolation.formalJet center
          (1 : MvPolynomial (Fin (m + 1)) Complex) = 1 := map_one _
      have hcone : (MvPolynomial.C (1 : Complex) : MvPolynomial (Fin (m + 1)) Complex) = 1 := by
        simp
      rw [hcone, hX0, h1]
      ring_nf
  exact AlgHom.congr_fun hmain Q
