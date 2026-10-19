-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_coeff_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T18:00:20.173314+00:00
-- url     : https://prove2.me/submissions/a199bf44-c4c0-4bce-aee6-258bc071b7c1

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution (n : ℕ) :
    ∃ x : ℝ, 0 ≤ x ∧
      PowerSeries.coeff n
        (PowerSeries.mk (fun j : ℕ => if j = 0 then 0 else (j : ℂ)⁻¹)) = (x : ℂ) := by
  refine ⟨(n : ℝ)⁻¹, inv_nonneg.mpr (Nat.cast_nonneg n), ?_⟩
  by_cases hn : n = 0
  · simp [PowerSeries.coeff_mk, hn]
  · simp [PowerSeries.coeff_mk, hn, map_inv₀]