-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_power_coeff_le_one
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-18T18:01:23.1068+00:00
-- url     : https://prove2.me/submissions/731d3714-d083-4fb5-aee7-c038beebd1f8

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Mathlib.Tactic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution : ¬ (∀ (q k : ℕ),
    ‖PowerSeries.coeff k
      ((PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (n : ℂ)⁻¹)) ^ q)‖ ≤ 1) := by
  intro h
  have h35 := h 3 5
  have hcoeff : PowerSeries.coeff 5
      ((PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (n : ℂ)⁻¹)) ^ 3)
      = (7 / 4 : ℂ) := by
    norm_num [PowerSeries.coeff_mul, PowerSeries.coeff_mk,
      Finset.antidiagonal, pow_succ]
  rw [hcoeff] at h35
  norm_num at h35