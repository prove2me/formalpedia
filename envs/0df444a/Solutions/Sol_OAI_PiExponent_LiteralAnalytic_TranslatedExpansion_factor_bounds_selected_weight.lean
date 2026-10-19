-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds_selected_weight
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T13:08:43.240202+00:00
-- url     : https://prove2.me/submissions/4a337847-eac9-4266-850a-ca42d00ff372

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionWeights
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_selected_weight_ge_row_weight_of_choiceScalar_ne_zero
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_actual_weight_sum_eq_row_count_height_mean

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (f : ChoiceFamily d H)
    (hs : (∏ r : Row d H, choiceScalar d r (f r)) ≠ 0) :
    (actualRowCount d H : ℝ) * H * actualMean d H ≤
      ∑ r : Row d H, translatedIndexWeight d (f r).1 := by
  classical
  have hfactor : ∀ r : Row d H, choiceScalar d r (f r) ≠ 0 := by
    have hp := (Finset.prod_ne_zero_iff.mp hs)
    intro r
    exact hp r (Finset.mem_univ r)
  calc
    (actualRowCount d H : ℝ) * H * actualMean d H =
        ∑ r : Row d H,
          ∑ i : Fin d.m,
            MatrixArithmetic.logWeights (finiteDenominators d) i *
              (r.2.1 i.succ : ℝ) :=
      OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.actual_weight_sum_eq_row_count_height_mean
        d hH
    _ ≤ ∑ r : Row d H, translatedIndexWeight d (f r).1 :=
      Finset.sum_le_sum fun r _ =>
        OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.selected_weight_ge_row_weight_of_choiceScalar_ne_zero
          d hH f r (hfactor r)