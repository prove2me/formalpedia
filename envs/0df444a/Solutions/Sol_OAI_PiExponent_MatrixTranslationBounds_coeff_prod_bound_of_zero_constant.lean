-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.coeff_prod_bound_of_zero_constant
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:12:11.811993+00:00
-- url     : https://prove2.me/submissions/cb421b7c-2ecd-40ac-a47b-92307e703076

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Log
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_coeff_prod_bound_choose
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_choose_real_le_two_pow

open scoped BigOperators

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → PowerSeries ℂ) (k : ℕ)
    (h0 : ∀ i, PowerSeries.coeff 0 (g i) = 0)
    (h1 : ∀ i n, ‖PowerSeries.coeff n (g i)‖ ≤ (1 : ℝ)) :
    ‖PowerSeries.coeff k (∏ i, g i)‖ ≤ (2 : ℝ) ^ k := by
  exact le_trans
    (OAI.PiExponent.MatrixTranslationBounds.coeff_prod_bound_choose g k h0 h1)
    (OAI.PiExponent.MatrixTranslationBounds.choose_real_le_two_pow k (Fintype.card ι))