-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds_collision_estimate_of_order_budget
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T07:34:54.121854+00:00
-- url     : https://prove2.me/submissions/13326162-248b-4256-89ef-57fb4487901d

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_period_coefficient_collision_bound

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : ChoiceFamily d H)
    (horders : ((∑ r : Row d H,
      (r.2.1 0 - ((f r).2.2 : ℕ)) : ℕ) : ℝ) ≤
        (Fintype.card (Row d H) : ℝ) * H / (d.v0 : ℝ)) :
    ‖(choiceMatrix d selection f).det‖ ≤
      Real.exp (-collisionConstant *
        (∑ a : indices d H,
          (((Finset.univ : Finset (Row d H)).filter
            (fun r => (f r).1 = a)).card : ℝ) ^ 2) +
        (actualRowCount d H : ℝ) * H *
          (d.holomorphicError + Collision.collisionRemainder (actualRowCount d H) H)) := by
  classical
  have hw (i : Fin d.m) :
      d.wstar ≤ MatrixArithmetic.logWeights (finiteDenominators d) i := by
    change d.wstar ≤ (⌈Real.log (d.q i.val)⌉₊ : ℝ)
    rw [← d.x_log i.val]
    exact d.wstar_lower i
  have hcol (c : Row d H) :
      (d.w0 : ℝ) * ((selection c).1 0 : ℝ) +
        ∑ i : Fin d.m,
          MatrixArithmetic.logWeights (finiteDenominators d) i *
            ((selection c).1 i.succ : ℝ) ≤ H := by
    have hc : (∑ i : Fin (d.m + 1),
        InterpolationMatrix.columnWeights (d.w0 : ℝ)
          (MatrixArithmetic.logWeights (finiteDenominators d)) i *
            ((selection c).1 i : ℝ)) ≤ H := by
      exact (Finset.mem_filter.mp (selection c).2).2
    simpa [InterpolationMatrix.columnWeights, Fin.sum_univ_succ] using hc
  have hb := period_coefficient_collision_bound
    (fun r : Row d H => (f r).1) (fun A : indices d H => A.1)
    (fun r : Row d H => r.1.val)
    (fun r : Row d H => r.2.1 0 - ((f r).2.2 : ℕ))
    (fun c : Row d H => (selection c).1 0)
    (fun c : Row d H => fun i : Fin d.m => (selection c).1 i.succ)
    (MatrixArithmetic.logWeights (finiteDenominators d))
    (lt_of_lt_of_le Nat.zero_lt_one d.K_pos) hH d.w0_pos d.v0_pos d.wstar_pos
    hw (fun r => r.1.isLt) hcol horders
  change ‖(choiceMatrix d selection f).det‖ ≤ _ at hb
  simpa only [actualRowCount, collisionConstant,
    AdmissibleParameters.holomorphicError] using hb
