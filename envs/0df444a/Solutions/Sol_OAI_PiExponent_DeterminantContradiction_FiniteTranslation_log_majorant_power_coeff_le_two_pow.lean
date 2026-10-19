-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_power_coeff_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T18:15:30.559226+00:00
-- url     : https://prove2.me/submissions/d15534eb-c2eb-4a74-8cac-6387b8f8019f

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Definitions.Def_OAI_PiExponent_logMajorantCompositions
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_log_majorant_power_coeff_le_composition_card
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_positive_composition_card_le_two_pow

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution (q k : ℕ) :
    ‖PowerSeries.coeff k
      ((PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (n : ℂ)⁻¹)) ^ q)‖ ≤
      (2 : ℝ) ^ k := by
  calc
    ‖PowerSeries.coeff k
        ((PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (n : ℂ)⁻¹)) ^ q)‖ ≤
        ((logMajorantCompositions q k).card : ℝ) :=
      OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_power_coeff_le_composition_card q k
    _ ≤ (2 : ℝ) ^ k := by
      exact_mod_cast
        OAI.PiExponent.DeterminantContradiction.FiniteTranslation.positive_composition_card_le_two_pow q k