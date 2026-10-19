-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.liftLogSeries_firstJet_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:14:34.722744+00:00
-- url     : https://prove2.me/submissions/279522f5-d9e2-426b-b4ab-a635d4186247

import Mathlib
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PowerSeries.Log

open OAI.PiExponent.AdmissibleFormalInterpolation
theorem pie_coeff_lift {m : ℕ} (D : PowerSeries ℂ) (b : Fin (m + 1) →₀ ℕ) :
    MvPowerSeries.coeff b (liftLogSeries m D) =
      if b.tail = 0 then PowerSeries.coeff (b 0) D else 0 := by
  conv_lhs => rw [← Finsupp.cons_tail b]
  rw [← MvPowerSeries.coeff_coeff_finSuccEquiv]
  simp only [liftLogSeries, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe,
    Function.comp_apply, RingEquiv.coe_toRingHom]
  rw [show (MvPowerSeries.finSuccEquiv ℂ m)
      ((MvPowerSeries.finSuccEquiv ℂ m).symm.toRingEquiv (PowerSeries.map MvPowerSeries.C D))
      = PowerSeries.map MvPowerSeries.C D from
    (MvPowerSeries.finSuccEquiv ℂ m).apply_symm_apply _]
  rw [PowerSeries.coeff_map, MvPowerSeries.coeff_C]

theorem solution
    {m : Nat} :
    MvPowerSeries.coeff 0 (liftLogSeries m (PowerSeries.log Complex)) = 0 ∧
    (∀ j : Fin (m + 1),
      MvPowerSeries.coeff (Finsupp.single j 1)
        (liftLogSeries m (PowerSeries.log Complex)) = (if j = 0 then 1 else 0)) := by
  refine ⟨?_, fun j => ?_⟩
  · rw [pie_coeff_lift]; simp
  · rw [pie_coeff_lift]
    by_cases hj : j = 0
    · subst hj
      have : (Finsupp.single (0 : Fin (m+1)) 1 : Fin (m+1) →₀ ℕ).tail = 0 := by
        ext k; simp [Finsupp.tail, Fin.tail, Finsupp.single_apply, (Fin.succ_ne_zero k).symm]
      simp [this]
    · obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.mpr hj
      have : (Finsupp.single k.succ 1 : Fin (m+1) →₀ ℕ).tail ≠ 0 := by
        intro h
        have := DFunLike.congr_fun h k
        simp [Finsupp.tail, Fin.tail] at this
      simp [this, hj]
