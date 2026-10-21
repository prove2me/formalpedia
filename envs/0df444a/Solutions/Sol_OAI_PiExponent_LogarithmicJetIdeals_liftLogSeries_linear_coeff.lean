-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.liftLogSeries_linear_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T18:00:49.062674+00:00
-- url     : https://prove2.me/submissions/650bf474-f4f2-41fe-a9b0-29067e17bcdf

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_liftLogSeries_coeff_formula
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_log_linear_coefficients
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_X_zero_coeff_formula

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : Nat} (d : Fin (m + 1) -> Nat)
    (hd : (∑ k : Fin (m + 1), d k) <= 1) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
      (liftLogSeries m (PowerSeries.log ℂ)) =
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
      (MvPowerSeries.X 0) := by
  classical
  have hd0 : d 0 ≤ 1 := by
    calc
      d 0 ≤ ∑ k : Fin (m + 1), d k := by
        exact Finset.single_le_sum (s := Finset.univ) (f := d)
          (fun k hk => Nat.zero_le _) (Finset.mem_univ 0)
      _ ≤ 1 := hd
  have hleft :=
    OAI.PiExponent.LogarithmicJetIdeals.liftLogSeries_coeff_formula
      d (PowerSeries.log ℂ)
  have hlog :=
    OAI.PiExponent.LogarithmicJetIdeals.log_linear_coefficients
      (d 0) hd0
  -- The published variable formula has natural-number coefficients.
  have hrightNat :
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
        (MvPowerSeries.X 0 : MvPowerSeries (Fin (m + 1)) ℕ) =
      if (d 0 = 1 ∧ ∀ i : Fin (m + 1), i ≠ 0 → d i = 0) then 1 else 0 :=
    OAI.PiExponent.LogarithmicJetIdeals.X_zero_coeff_formula d
  have hright :
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
        (MvPowerSeries.X 0 : MvPowerSeries (Fin (m + 1)) ℂ) =
      if (d 0 = 1 ∧ ∀ i : Fin (m + 1), i ≠ 0 → d i = 0) then 1 else 0 := by
    calc
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
          (MvPowerSeries.X 0 : MvPowerSeries (Fin (m + 1)) ℂ) =
          (Nat.castRingHom ℂ)
            (MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
              (MvPowerSeries.X 0 : MvPowerSeries (Fin (m + 1)) ℕ)) := by
        rw [← MvPowerSeries.coeff_map, MvPowerSeries.map_X]
      _ = _ := by
        rw [hrightNat]
        split_ifs <;> simp
  rw [hleft, hright]
  by_cases htail : ∀ i : Fin (m + 1), i ≠ 0 → d i = 0
  · rw [if_pos htail, hlog]
    rcases (show d 0 = 0 ∨ d 0 = 1 by omega) with hzero | hone
    · have hnot : ¬ (d 0 = 1 ∧ ∀ i : Fin (m + 1), i ≠ 0 → d i = 0) := by
        rintro ⟨hone, hrest⟩
        omega
      rw [if_pos hzero, if_neg hnot]
    · rw [if_neg (show d 0 ≠ 0 by omega), if_pos ⟨hone, htail⟩]
  · have hnot : ¬ (d 0 = 1 ∧ ∀ i : Fin (m + 1), i ≠ 0 → d i = 0) := by
      rintro ⟨hone, hrest⟩
      exact htail hrest
    rw [if_neg htail, if_neg hnot]
