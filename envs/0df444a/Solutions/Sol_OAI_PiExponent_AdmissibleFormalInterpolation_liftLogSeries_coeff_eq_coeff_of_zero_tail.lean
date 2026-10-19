-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_coeff_eq_coeff_of_zero_tail
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T07:27:59.405149+00:00
-- url     : https://prove2.me/submissions/77fa29f1-f108-4bb1-bbeb-d4fa4d766db8

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution (m : ℕ) (D : PowerSeries ℂ) (α : Fin (m + 1) →₀ ℕ)
    (htail : ∀ j : Fin m, α j.succ = 0) :
    MvPowerSeries.coeff α (OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries m D) =
      PowerSeries.coeff (α 0) D := by
  have hα : α = Finsupp.cons (α 0) (0 : Fin m →₀ ℕ) := by
    ext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j
      simp [htail j]
  rw [hα]
  rw [← MvPowerSeries.coeff_coeff_finSuccEquiv
    (p := liftLogSeries m D) (k := α 0) (x := (0 : Fin m →₀ ℕ))]
  simp [liftLogSeries]