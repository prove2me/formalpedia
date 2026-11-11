-- Prove2me | solution 1 for OAI.SiegelZeros.WeightedTorusJets.dirichletRealZeroBound_proof
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:02:44.466852+00:00
-- url     : https://prove2.me/submissions/273c46e3-40ea-4c51-b8d3-0e934ed5ca31

import Mathlib
import Theorems.Thm_OAI_DirichletCharacter_LFunction_ne_zero_of_seven_eighths_lt_re

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β : ℝ,
          (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) →
            c ≤ (1 - β) * Real.log (q : ℝ) := by
  refine ⟨Real.log 3 / 8, by positivity, ?_⟩
  intro q _ hq χ _ hχ _ β ⟨hβ0, hβ1, hz⟩
  have hβ : β ≤ 7 / 8 := by
    by_contra h
    replace h := not_le.mp h
    refine OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re χ (s := (β : ℂ))
      (by simpa using h) (fun h' => hχ h'.1) hz
  have hl : Real.log 3 ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hq)
  have hl0 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  nlinarith
