-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.coeff_shear_top_zero_specialize
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T10:09:06.193466+00:00
-- url     : https://prove2.me/submissions/6a579faf-bd10-41d7-9331-f56667f6916a

import Definitions.Def_OAI_PiExponent_FormalJetShear

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (f : Fin m → PowerSeries ℂ)
    (a d : Fin (m + 1) →₀ ℕ)
    (htop : ∀ i : Fin m, d i.succ = a i.succ)
    (hzero : d 0 = 0) :
    MvPowerSeries.coeff d
        (∏ i : Fin m,
          (MvPowerSeries.X i.succ + liftLogSeries m (f i)) ^ (a i.succ)) =
      MvPowerSeries.coeff d
        (∏ i : Fin m,
          (MvPowerSeries.X i.succ + MvPowerSeries.C ((f i).constantCoeff)) ^
            (a i.succ)) := by
  classical
  let E := MvPowerSeries.finSuccEquiv ℂ m
  let P : MvPowerSeries (Fin (m + 1)) ℂ :=
    ∏ i : Fin m,
      (MvPowerSeries.X i.succ + liftLogSeries m (f i)) ^ (a i.succ)
  let Q : MvPowerSeries (Fin (m + 1)) ℂ :=
    ∏ i : Fin m,
      (MvPowerSeries.X i.succ + MvPowerSeries.C ((f i).constantCoeff)) ^
        (a i.succ)
  have hd : d = Finsupp.cons 0 a.tail := by
    ext j
    cases j using Fin.cases with
    | zero => simp [hzero]
    | succ i => simpa only [Finsupp.cons_succ, Finsupp.tail_apply] using htop i
  have hmap (i : Fin m) :
      PowerSeries.constantCoeff
          (PowerSeries.map (MvPowerSeries.C : ℂ →+* MvPowerSeries (Fin m) ℂ) (f i)) =
        MvPowerSeries.C ((f i).constantCoeff) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [PowerSeries.coeff_map]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hconst :
      PowerSeries.constantCoeff (E P) = PowerSeries.constantCoeff (E Q) := by
    simp [P, Q, E, liftLogSeries, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hmap]
  change MvPowerSeries.coeff d P = MvPowerSeries.coeff d Q
  rw [hd,
    ← MvPowerSeries.coeff_coeff_finSuccEquiv (p := P) (k := 0) (x := a.tail),
    ← MvPowerSeries.coeff_coeff_finSuccEquiv (p := Q) (k := 0) (x := a.tail),
    PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hconst]