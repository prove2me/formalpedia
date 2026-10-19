-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_support_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:15:12.092847+00:00
-- url     : https://prove2.me/submissions/78e5f2a9-a8a0-44cb-a47e-743074d4f2ab

import Mathlib
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.MvPowerSeries.Substitution

open scoped BigOperators
open OAI.PiExponent
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
    {m : ℕ} (q : Fin (m + 1) → ℝ) (T : Fin m → ℕ)
    (R : Fin m → PowerSeries ℂ)
    (hq : ∀ i, 0 < q i)
    (hT : ∀ i : Fin m, q i.succ ≤ (T i : ℝ) * q 0)
    (hR : ∀ (i : Fin m) (k : ℕ), k < T i → PowerSeries.coeff k (R i) = 0)
    (i : Fin m) (a : Fin (m + 1) → ℕ) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (liftLogSeries m (R i)) ≠ 0 →
    q i.succ ≤ ∑ j, q j * (a j : ℝ) := by
  intro h
  rw [pie_coeff_lift] at h
  split_ifs at h with ht
  · have htail : ∀ j : Fin m, a j.succ = 0 := fun j => by
      have := DFunLike.congr_fun ht j
      simpa [InterpolationMatrix.exponentVector, Finsupp.tail, Fin.tail] using this
    have hT0 : T i ≤ a 0 := by
      by_contra hlt
      push Not at hlt
      exact h (by simpa [InterpolationMatrix.exponentVector] using hR i (a 0) hlt)
    rw [Fin.sum_univ_succ]
    simp only [htail, Nat.cast_zero, mul_zero, Finset.sum_const_zero, add_zero]
    have h1 := hT i
    have h2 : (T i : ℝ) ≤ a 0 := by exact_mod_cast hT0
    nlinarith [hq 0]
  · exact absurd rfl h
