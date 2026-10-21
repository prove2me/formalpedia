-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds_collision_determinant
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T10:02:16.75209+00:00
-- url     : https://prove2.me/submissions/c301031e-c287-4cc9-929d-dc3a84678d7a

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_factor_bounds_collision_row_order
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_factor_bounds_collision_estimate_of_order_budget

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    ‖(choiceMatrix d selection f).det‖ ≤
      Real.exp (-collisionConstant *
        (∑ a : indices d H,
          (((Finset.univ : Finset (Row d H)).filter
            (fun r => (f r).1 = a)).card : ℝ) ^ 2) +
        (actualRowCount d H : ℝ) * H *
          (d.holomorphicError + Collision.collisionRemainder (actualRowCount d H) H)) := by
  have horders : ((∑ r : Row d H,
      (r.2.1 0 - ((f r).2.2 : ℕ)) : ℕ) : ℝ) ≤
      (Fintype.card (Row d H) : ℝ) * H / (d.v0 : ℝ) := by
    rw [Nat.cast_sum]
    calc
      _ ≤ ∑ r : Row d H, H / (d.v0 : ℝ) := by
        apply Finset.sum_le_sum
        intro r _
        exact le_trans (by exact_mod_cast Nat.sub_le (r.2.1 0) ((f r).2.2 : ℕ))
          (OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds_collision_row_order d hH r)
      _ = _ := by simp; ring_nf
  exact OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds_collision_estimate_of_order_budget
    d hH selection f (by simpa [actualRowCount] using horders)
