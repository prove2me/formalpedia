-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.liftLogSeries_coeff_formula
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T18:23:57.405866+00:00
-- url     : https://prove2.me/submissions/b1a7e7b2-89e1-4319-b492-f5da5d5e5ad1

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : Nat} (d : Fin (m + 1) -> Nat) (f : PowerSeries ℂ) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
      (liftLogSeries m f) =
      if (∀ i : Fin (m + 1), i ≠ 0 → d i = 0) then
        PowerSeries.coeff (d 0) f else 0 := by
  classical
  let x : Fin m →₀ Nat := Finsupp.equivFunOnFinite.symm (fun i : Fin m => d i.succ)
  have hindex : Finsupp.equivFunOnFinite.symm d = Finsupp.cons (d 0) x := by
    ext i
    cases i using Fin.cases with
    | zero => simp [x]
    | succ j => simp [x]
  have hzero : (∀ i : Fin (m + 1), i ≠ 0 → d i = 0) ↔ x = 0 := by
    constructor
    · intro h
      ext j
      simp [x, h j.succ (by simp)]
    · intro hx i hi
      cases i using Fin.cases with
      | zero => exact (hi rfl).elim
      | succ j =>
        have hj : d j.succ = 0 := by
          simpa [x] using congrArg (fun y : Fin m →₀ Nat => y j) hx
        exact hj
  rw [hindex]
  rw [← MvPowerSeries.coeff_coeff_finSuccEquiv
    (p := liftLogSeries m f) (k := d 0) (x := x)]
  change MvPowerSeries.coeff x
    (PowerSeries.coeff (d 0) ((MvPowerSeries.finSuccEquiv ℂ m) (liftLogSeries m f))) = _
  unfold liftLogSeries
  change MvPowerSeries.coeff x
    (PowerSeries.coeff (d 0) ((MvPowerSeries.finSuccEquiv ℂ m)
      ((MvPowerSeries.finSuccEquiv ℂ m).symm ((PowerSeries.map MvPowerSeries.C) f)))) = _
  rw [AlgEquiv.apply_symm_apply, PowerSeries.coeff_map]
  simp only [MvPowerSeries.coeff_C]
  by_cases hx : x = 0
  · rw [if_pos hx, if_pos (hzero.mpr hx)]
  · have hd : ¬ (∀ i : Fin (m + 1), i ≠ 0 → d i = 0) := by
      intro hd
      exact hx (hzero.mp hd)
    rw [if_neg hx, if_neg hd]
