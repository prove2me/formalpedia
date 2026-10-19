-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_coeff_eq_zero_of_nonzero_tail
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T07:45:10.275417+00:00
-- url     : https://prove2.me/submissions/992300e9-a7e7-47ae-906d-28971ce6cc56

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    (m : ℕ) (D : PowerSeries ℂ) (α : Fin (m + 1) →₀ ℕ)
    (htail : ∃ j : Fin m, α j.succ ≠ 0) :
    MvPowerSeries.coeff α (OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries m D) = 0 := by
  classical
  obtain ⟨j, hj⟩ := htail
  have htail_ne : Finsupp.tail α ≠ 0 := by
    intro h
    apply hj
    simpa [Finsupp.tail_apply] using congrArg (fun f : Fin m →₀ ℕ => f j) h
  rw [← Finsupp.cons_tail α]
  rw [← MvPowerSeries.coeff_coeff_finSuccEquiv
    (p := liftLogSeries m D) (k := α 0) (x := Finsupp.tail α)]
  change MvPowerSeries.coeff (Finsupp.tail α)
    (PowerSeries.coeff (α 0)
      ((MvPowerSeries.finSuccEquiv ℂ m)
        ((MvPowerSeries.finSuccEquiv ℂ m).symm
          (PowerSeries.map (MvPowerSeries.C : ℂ →+* MvPowerSeries (Fin m) ℂ) D)))) = 0
  rw [AlgEquiv.apply_symm_apply, PowerSeries.coeff_map]
  exact MvPowerSeries.coeff_C_of_ne_zero (R := ℂ) (σ := Fin m)
    htail_ne (PowerSeries.coeff (α 0) D)
