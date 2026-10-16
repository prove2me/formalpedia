-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.liftLogSeries_coeff_truncation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T05:33:50.391293+00:00
-- url     : https://prove2.me/submissions/5a055d9c-f336-4239-95f8-4e938d0f38b7

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    (m : ℕ) (f : PowerSeries ℂ) (T : ℕ)
    (d : Fin (m + 1) → ℕ) (hd : d 0 < T) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (liftLogSeries m f) =
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
        (∑ n ∈ Finset.range T,
          MvPowerSeries.C (PowerSeries.coeff n f) *
            (MvPowerSeries.X (0 : Fin (m + 1))) ^ n) := by
  classical
  let e : Fin (m + 1) →₀ ℕ := Finsupp.equivFunOnFinite.symm d
  have he0 : e 0 = d 0 := rfl
  have hcoeff (p : MvPowerSeries (Fin (m + 1)) ℂ) :
      MvPowerSeries.coeff e p =
        MvPowerSeries.coeff (Finsupp.tail e)
          (PowerSeries.coeff (e 0) (MvPowerSeries.finSuccEquiv ℂ m p)) := by
    rw [MvPowerSeries.coeff_coeff_finSuccEquiv, Finsupp.cons_tail]
  have hlift :
      MvPowerSeries.finSuccEquiv ℂ m (liftLogSeries m f) =
        PowerSeries.map MvPowerSeries.C f := by
    change (MvPowerSeries.finSuccEquiv ℂ m)
      ((MvPowerSeries.finSuccEquiv ℂ m).symm
        (PowerSeries.map MvPowerSeries.C f)) = _
    exact (MvPowerSeries.finSuccEquiv ℂ m).apply_symm_apply _
  have hfinite :
      PowerSeries.coeff (e 0)
        (MvPowerSeries.finSuccEquiv ℂ m
          (∑ n ∈ Finset.range T,
            MvPowerSeries.C (PowerSeries.coeff n f) *
              (MvPowerSeries.X (0 : Fin (m + 1))) ^ n)) =
        MvPowerSeries.C (PowerSeries.coeff (e 0) f) := by
    simp only [map_sum, map_mul, map_pow, MvPowerSeries.finSuccEquiv_C,
      MvPowerSeries.finSuccEquiv_X_zero, PowerSeries.coeff_C_mul_X_pow]
    simp only [Finset.sum_ite_eq, Finset.mem_range, he0, if_pos hd]
  calc
    MvPowerSeries.coeff e (liftLogSeries m f) =
        MvPowerSeries.coeff (Finsupp.tail e)
          (PowerSeries.coeff (e 0)
            (MvPowerSeries.finSuccEquiv ℂ m (liftLogSeries m f))) := hcoeff _
    _ = MvPowerSeries.coeff (Finsupp.tail e)
          (MvPowerSeries.C (PowerSeries.coeff (e 0) f)) := by
      rw [hlift, PowerSeries.coeff_map]
    _ = MvPowerSeries.coeff e
          (∑ n ∈ Finset.range T,
            MvPowerSeries.C (PowerSeries.coeff n f) *
              (MvPowerSeries.X (0 : Fin (m + 1))) ^ n) := by
      rw [hcoeff, hfinite]