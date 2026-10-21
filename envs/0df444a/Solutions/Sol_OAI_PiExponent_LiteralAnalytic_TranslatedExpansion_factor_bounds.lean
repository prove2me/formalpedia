-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T09:45:15.804663+00:00
-- url     : https://prove2.me/submissions/ff7c44cc-648e-4608-bc8c-9f415da788ab

import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_factor_bounds_index_geometry
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_factor_bounds_selected_weight
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_factor_bounds_scalar_product
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_factor_bounds_collision_determinant
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionWeights

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : ChoiceFamily d H)
    (hs : (∏ r : Row d H, choiceScalar d r (f r)) ≠ 0) :
    0 < (lowIndexCount d H : ℝ) ∧
    (∀ a : indices d H, 0 ≤ translatedIndexWeight d a) ∧
    (((Finset.univ : Finset (indices d H)).filter
      (fun a => translatedIndexWeight d a ≤ (d.base.A : ℝ) * H)).card : ℝ) ≤
        (lowIndexCount d H : ℝ) ∧
    (actualRowCount d H : ℝ) * H * actualMean d H ≤
      ∑ r : Row d H, translatedIndexWeight d (f r).1 ∧
    ‖∏ r : Row d H, choiceScalar d r (f r)‖ ≤
      Real.exp (-nu * ((∑ r : Row d H, translatedIndexWeight d (f r).1) -
        (actualRowCount d H : ℝ) * H * actualMean d H) +
        (actualRowCount d H : ℝ) * H * d.translationError) ∧
    ‖(choiceMatrix d selection f).det‖ ≤
      Real.exp (-collisionConstant *
        (∑ a : indices d H,
          (((Finset.univ : Finset (Row d H)).filter
            (fun r => (f r).1 = a)).card : ℝ) ^ 2) +
        (actualRowCount d H : ℝ) * H *
          (d.holomorphicError + Collision.collisionRemainder (actualRowCount d H) H)) := by
  obtain ⟨hcount, hweight, hcapacity⟩ :=
    OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds_index_geometry d hH
  have hselected :=
    OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds_selected_weight d hH f hs
  have hscalar :=
    OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds_scalar_product d hnu hH f
  have hdet :=
    OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds_collision_determinant
      d hH selection f
  exact ⟨hcount, hweight, hcapacity, hselected, hscalar, hdet⟩