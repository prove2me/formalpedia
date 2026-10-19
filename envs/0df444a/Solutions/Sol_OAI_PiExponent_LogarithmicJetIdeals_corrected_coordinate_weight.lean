-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.corrected_coordinate_weight
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:15:35.77203+00:00
-- url     : https://prove2.me/submissions/87afb10f-96a2-4d9d-bb89-73738f2f3258

import Mathlib
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators
theorem pie_coeff_lift {m : ℕ} (D : PowerSeries ℂ) (b : Fin (m + 1) →₀ ℕ) :
    MvPowerSeries.coeff b (AdmissibleFormalInterpolation.liftLogSeries m D) =
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
    {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (D : Fin m → PowerSeries ℂ)
    (hD : ∀ i : Fin m, ∀ n : ℕ,
      (n : ℝ) * q 0 < q i.succ → PowerSeries.coeff n (D i) = 0)
    (i : Fin m) (b : Fin (m + 1) →₀ ℕ) :
    MvPowerSeries.coeff b
      (MvPowerSeries.X i.succ - liftLogSeries m (D i)) ≠ 0 →
      q i.succ ≤ ∑ j, q j * (b j : ℝ) := by
  intro h
  rw [map_sub, pie_coeff_lift, MvPowerSeries.coeff_X] at h
  by_cases hb : b = Finsupp.single i.succ 1
  · subst hb
    rw [Finset.sum_eq_single i.succ]
    · simp
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  · rw [if_neg hb, zero_sub, neg_ne_zero] at h
    split_ifs at h with ht
    have hle : ¬ ((b 0 : ℕ) : ℝ) * q 0 < q i.succ := fun hlt => h (hD i _ hlt)
    push Not at hle
    rw [Fin.sum_univ_succ]
    have : ∀ j : Fin m, b j.succ = 0 := fun j => by
      have := DFunLike.congr_fun ht j
      simpa [Finsupp.tail, Fin.tail] using this
    simp only [this, Nat.cast_zero, mul_zero, Finset.sum_const_zero, add_zero]
    linarith
    exact absurd rfl h
