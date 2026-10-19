-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.local_jet_generator_logTail_coeff_support_succ
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:14:59.108992+00:00
-- url     : https://prove2.me/submissions/57b9ba53-50fb-4553-8552-09fa6ec00c48

import Mathlib
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators
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
    {m : ℕ} (T : Fin m → ℕ) (b : Fin (m + 1) → ℕ) (i : Fin m) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (AdmissibleFormalInterpolation.liftLogSeries m
        (PowerSeries.log ℂ -
          (InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ))) ≠ 0 →
      (∀ j : Fin m, b j.succ = 0) ∧ T i ≤ b 0 := by
  intro h
  rw [pie_coeff_lift] at h
  split_ifs at h with ht
  · refine ⟨fun j => ?_, ?_⟩
    · have := DFunLike.congr_fun ht j
      simpa [InterpolationMatrix.exponentVector, Finsupp.tail, Fin.tail] using this
    · by_contra hlt
      push Not at hlt
      apply h
      simp [InterpolationMatrix.exponentVector, InterpolationMatrix.truncatedLog,
        Polynomial.coeff_coe, PowerSeries.coeff_trunc, hlt]
  · exact absurd rfl h
