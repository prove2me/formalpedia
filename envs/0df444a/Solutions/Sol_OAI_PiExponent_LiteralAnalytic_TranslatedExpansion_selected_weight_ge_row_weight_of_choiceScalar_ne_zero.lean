-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.selected_weight_ge_row_weight_of_choiceScalar_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T21:32:38.617056+00:00
-- url     : https://prove2.me/submissions/9eb7ef2e-1b7f-45d7-86bc-3f2fe6c4547a

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionWeights
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_row_coordinate_le_index_of_choiceScalar_ne_zero

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (f : ChoiceFamily d H) (r : Row d H)
    (hr : choiceScalar d r (f r) ≠ 0) :
    (∑ i : Fin d.m, MatrixArithmetic.logWeights (finiteDenominators d) i *
        (r.2.1 i.succ : ℝ)) ≤
      translatedIndexWeight d (f r).1 := by
  classical
  have hcoord :=
    OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.row_coordinate_le_index_of_choiceScalar_ne_zero
      d f r hr
  unfold translatedIndexWeight
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left
  · exact_mod_cast hcoord i
  · change 0 ≤ (Nat.ceil (Real.log (finiteDenominators d i)) : ℝ)
    exact_mod_cast (Nat.zero_le (Nat.ceil (Real.log (finiteDenominators d i))))