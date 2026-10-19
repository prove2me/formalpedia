-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_power_coeff_le_composition_card
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T18:20:21.538151+00:00
-- url     : https://prove2.me/submissions/bc8c33e3-70dc-47ed-8ca3-9c2add0dc22b

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Definitions.Def_OAI_PiExponent_logMajorantCompositions
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_log_majorant_power_coeff_eq_composition_sum
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_log_majorant_composition_reciprocal_sum_bound

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution (q k : ℕ) :
    ‖PowerSeries.coeff k
      ((PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (n : ℂ)⁻¹)) ^ q)‖ ≤
      ((logMajorantCompositions q k).card : ℝ) := by
  rw [log_majorant_power_coeff_eq_composition_sum]
  exact log_majorant_composition_reciprocal_sum_bound q k