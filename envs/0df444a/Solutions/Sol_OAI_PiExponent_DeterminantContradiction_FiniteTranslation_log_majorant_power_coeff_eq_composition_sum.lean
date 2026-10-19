-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_power_coeff_eq_composition_sum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T18:29:29.280607+00:00
-- url     : https://prove2.me/submissions/e819d659-852d-4d25-be1a-a39135269de0

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Definitions.Def_OAI_PiExponent_logMajorantCompositions
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_logMajorant_power_coeff_eq_composition_sum_generic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution (q k : ℕ) :
    PowerSeries.coeff k
      ((PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (n : ℂ)⁻¹)) ^ q) =
      ∑ a ∈ logMajorantCompositions q k, ∏ i : Fin q, ((a i : ℂ)⁻¹) := by
  have hgeneric :=
    OAI.PiExponent.DeterminantContradiction.FiniteTranslation.logMajorant_power_coeff_eq_composition_sum_generic
      q k (fun n : ℕ => if n = 0 then 0 else (n : ℂ)⁻¹) rfl
  calc
    PowerSeries.coeff k
        ((PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (n : ℂ)⁻¹)) ^ q) =
        ∑ a ∈ logMajorantCompositions q k,
          ∏ i : Fin q, (if a i = 0 then 0 else (a i : ℂ)⁻¹) := by
      simpa [PowerSeries.coeff_mk] using hgeneric
    _ = ∑ a ∈ logMajorantCompositions q k, ∏ i : Fin q, ((a i : ℂ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.prod_congr rfl
      intro i hi
      have hpos : 0 < a i := (Finset.mem_filter.mp ha).2.1 i
      simp [Nat.ne_of_gt hpos]