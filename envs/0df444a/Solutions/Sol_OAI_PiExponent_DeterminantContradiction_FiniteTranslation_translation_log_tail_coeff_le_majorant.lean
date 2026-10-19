-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_log_tail_coeff_le_majorant
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T18:14:26.927847+00:00
-- url     : https://prove2.me/submissions/683981ff-9471-428d-acd4-dcbe0be272f5

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution (N n : ℕ) :
    ‖PowerSeries.coeff n
      ((PowerSeries.trunc N (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ)‖ ≤
    ‖PowerSeries.coeff n
      (PowerSeries.mk (fun j : ℕ => if j = 0 then 0 else (j : ℂ)⁻¹))‖ := by
  by_cases h0 : n = 0
  · subst n
    simp [PowerSeries.coeff_trunc, PowerSeries.coeff_log, PowerSeries.coeff_mk]
  · have hn : 0 < n := Nat.pos_of_ne_zero h0
    by_cases hcut : n < N
    · have htail : PowerSeries.coeff n
          ((PowerSeries.trunc N (PowerSeries.log ℂ) : PowerSeries ℂ) -
            PowerSeries.log ℂ) = 0 := by
        simp [PowerSeries.coeff_trunc, hcut]
      rw [htail]
      simpa using (norm_nonneg (PowerSeries.coeff n
        (PowerSeries.mk (fun j : ℕ => if j = 0 then 0 else (j : ℂ)⁻¹))))
    · have htail : PowerSeries.coeff n
          ((PowerSeries.trunc N (PowerSeries.log ℂ) : PowerSeries ℂ) -
            PowerSeries.log ℂ) = - PowerSeries.coeff n (PowerSeries.log ℂ) := by
        simp [PowerSeries.coeff_trunc, hcut]
      rw [htail]
      simp [PowerSeries.coeff_log, PowerSeries.coeff_mk, h0,
        Complex.norm_div, Complex.norm_pow, Complex.norm_natCast, hn]