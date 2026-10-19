-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.liftPowerSeries_coeff_formula
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T18:04:54.988197+00:00
-- url     : https://prove2.me/submissions/761c03bd-13a5-40b2-80aa-22d95b1d5f7b

import Definitions.Def_OAI_PiExponent_FormalJetShear

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (f : PowerSeries ℂ)
    (d : Fin (m + 1) →₀ ℕ) :
    MvPowerSeries.coeff d
      (((MvPowerSeries.finSuccEquiv ℂ m).symm.toRingHom.comp
        (PowerSeries.map MvPowerSeries.C)) f) =
      if ∀ j : Fin m, d j.succ = 0 then PowerSeries.coeff (d 0) f else 0 := by
  let x : Fin m →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun j => d j.succ)
  have hd : d = Finsupp.cons (d 0) x := by
    ext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j
      simp [x]
  have hx : (x = 0) ↔ ∀ j : Fin m, d j.succ = 0 := by
    rw [Finsupp.ext_iff]
    simp [x]
  rw [hd, ← MvPowerSeries.coeff_coeff_finSuccEquiv]
  simp [RingHom.comp_apply, x, hx, MvPowerSeries.coeff_C]