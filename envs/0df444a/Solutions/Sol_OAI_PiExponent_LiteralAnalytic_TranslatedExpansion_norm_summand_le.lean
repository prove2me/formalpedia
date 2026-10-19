-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.norm_summand_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T09:29:04.395618+00:00
-- url     : https://prove2.me/submissions/8291884c-71db-4a49-96ae-36e8f98aafb9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionWeights
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_factor_bounds
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_generic_product_bound

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    ‖summand d selection f‖ ≤ Real.exp (((actualRowCount d H : ℝ) * H) *
      (d.analyticError + Collision.collisionRemainder (actualRowCount d H) H +
        max (-collisionRate d H)
          (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)))) := by
  classical
  by_cases hs : (∏ r : Row d H, choiceScalar d r (f r)) = 0
  · rw [summand, hs, zero_mul, norm_zero]
    exact Real.exp_nonneg _
  rcases factor_bounds d hnu hH selection f hs with
    ⟨hN, hweight, hcapacity, hmean, hscalar, hdet⟩
  have hb := generic_product_bound
    (fun r : Row d H => (f r).1)
    (translatedIndexWeight d)
    (∏ r : Row d H, choiceScalar d r (f r))
    (choiceMatrix d selection f).det
    hH d.base.A_pos.le d.base.eta_pos.le hnu collisionConstant_pos.le hN
    hweight hmean hcapacity hscalar hdet
  simpa only [summand, AdmissibleParameters.analyticError, collisionRate,
    actualRowCount, neg_mul, neg_div] using hb
