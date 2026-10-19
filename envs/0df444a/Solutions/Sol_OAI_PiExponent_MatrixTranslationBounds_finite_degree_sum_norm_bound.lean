-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.finite_degree_sum_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T18:50:20.561284+00:00
-- url     : https://prove2.me/submissions/dc9cea37-449e-451e-947b-1d02d7e8a99b

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Log

import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_masked_sum_le_valid_card
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_positive_degree_assignments_card

open scoped BigOperators

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → PowerSeries ℂ) (k : ℕ)
    (h1 : ∀ i n, ‖PowerSeries.coeff n (g i)‖ ≤ (1 : ℝ)) :
    (∑ f : ι → Fin (k + 1),
      ‖if (∀ i, 0 < (f i).val) ∧ (∑ i, (f i).val) = k then
          ∏ i, PowerSeries.coeff (f i).val (g i)
        else (0 : ℂ)‖) ≤ (Nat.choose k (Fintype.card ι) : ℝ) := by
  classical
  let P : (ι → Fin (k + 1)) → Prop := fun f =>
    (∀ i, 0 < (f i).val) ∧ (∑ i, (f i).val) = k
  have hsum := OAI.PiExponent.MatrixTranslationBounds.masked_sum_le_valid_card g k h1
  have hcard := OAI.PiExponent.MatrixTranslationBounds.positive_degree_assignments_card
    (ι := ι) k
  calc
    (∑ f : ι → Fin (k + 1),
        ‖if (∀ i, 0 < (f i).val) ∧ (∑ i, (f i).val) = k then
            ∏ i, PowerSeries.coeff (f i).val (g i)
          else (0 : ℂ)‖)
        ≤ (Fintype.card {f : ι → Fin (k + 1) // P f} : ℝ) := by
          simpa [P] using hsum
    _ ≤ (Nat.choose k (Fintype.card ι) : ℝ) := by
          exact_mod_cast hcard