-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.monomial_shear_factor_power_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T10:32:29.375394+00:00
-- url     : https://prove2.me/submissions/db5b2f71-c24f-4b4a-8713-de68541bfd3e

import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_monomial_shear_factor_power_support_of_factor_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators

theorem solution
    {m : ℕ} (i : Fin m) (n : ℕ)
    (g : Fin m → MvPowerSeries (Fin (m + 1)) ℂ)
    (hg : ∀ k : Fin m, ∀ d : Fin (m + 1) →₀ ℕ, ∀ j : Fin m,
      d j.succ ≠ 0 → MvPowerSeries.coeff d (g k) = 0)
    (d : Fin (m + 1) →₀ ℕ) :
    (MvPowerSeries.coeff d ((MvPowerSeries.X i.succ + g i) ^ n) ≠ 0 →
      d i.succ ≤ n) ∧
    (∀ j : Fin m, j ≠ i → d j.succ ≠ 0 →
      MvPowerSeries.coeff d ((MvPowerSeries.X i.succ + g i) ^ n) = 0) := by
  classical
  have hfactor : ∀ e : Fin (m + 1) →₀ ℕ,
      MvPowerSeries.coeff e (MvPowerSeries.X i.succ + g i) ≠ 0 →
        e i.succ ≤ 1 ∧ ∀ j : Fin m, j ≠ i → e j.succ = 0 := by
    intro e he
    have hadd : MvPowerSeries.coeff e (MvPowerSeries.X i.succ + g i) =
        MvPowerSeries.coeff e (MvPowerSeries.X i.succ) + MvPowerSeries.coeff e (g i) :=
      map_add (MvPowerSeries.coeff e) _ _
    by_cases hi : e i.succ = 0
    · have hneq : e ≠ Finsupp.single i.succ 1 := by
        intro heq
        simp [heq] at hi
      have hX : MvPowerSeries.coeff e (MvPowerSeries.X i.succ) = 0 := by
        simp [MvPowerSeries.coeff_X, hneq]
      have hother : ∀ j : Fin m, j ≠ i → e j.succ = 0 := by
        intro j hji
        by_contra hj
        have hgzero := hg i e j hj
        have hzero : MvPowerSeries.coeff e (MvPowerSeries.X i.succ + g i) = 0 := by
          calc
            MvPowerSeries.coeff e (MvPowerSeries.X i.succ + g i) =
                MvPowerSeries.coeff e (MvPowerSeries.X i.succ) +
                  MvPowerSeries.coeff e (g i) := hadd
            _ = 0 := by simp [MvPowerSeries.coeff_X, hneq, hgzero]
        exact he hzero
      exact ⟨by omega, hother⟩
    · have hgzero := hg i e i hi
      have hx : MvPowerSeries.coeff e (MvPowerSeries.X i.succ + g i) =
          MvPowerSeries.coeff e (MvPowerSeries.X i.succ) := by
        rw [hadd, hgzero, add_zero]
      have hcoeff : MvPowerSeries.coeff e
          (MvPowerSeries.X i.succ : MvPowerSeries (Fin (m + 1)) ℂ) ≠ 0 := by
        intro hzero
        exact he (hx.trans hzero)
      have heq : e = Finsupp.single i.succ 1 := by
        by_contra hne
        have hzero : MvPowerSeries.coeff e
            (MvPowerSeries.X i.succ : MvPowerSeries (Fin (m + 1)) ℂ) = 0 := by
          simp [MvPowerSeries.coeff_X, hne]
        exact hcoeff hzero
      subst e
      constructor
      · simp
      · intro j hji
        have hsucc : j.succ ≠ i.succ := by
          intro h
          exact hji ((Fin.succ_injective m) h)
        simp [hsucc]
  exact OAI.PiExponent.AdmissibleFormalInterpolation.monomial_shear_factor_power_support_of_factor_support
    i n (MvPowerSeries.X i.succ + g i) hfactor d