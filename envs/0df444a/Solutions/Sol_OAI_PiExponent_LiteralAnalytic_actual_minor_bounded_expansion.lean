-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.actual_minor_bounded_expansion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T02:58:30.190058+00:00
-- url     : https://prove2.me/submissions/2dd48866-0985-4dd2-8320-4b800354c43f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_row_choice_card_le
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_minor_eq_sum
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_norm_summand_le

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem solution {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (selection : Row d H → Column d H) :
    ∃ (N : ℕ) (terms : Fin N → ℂ),
      (actualMinor d H selection).det = ∑ i, terms i ∧
      (N : ℝ) ≤ Real.exp ((actualRowCount d H : ℝ) *
        Real.log (translationTermCount d.m d.v0 H : ℝ)) ∧
      ∀ i, ‖terms i‖ ≤ Real.exp (((actualRowCount d H : ℝ) * H) *
        (d.analyticError + Collision.collisionRemainder (actualRowCount d H) H +
          max (-collisionRate d H)
            (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)))) := by
  classical
  let e := (Fintype.equivFin (ChoiceFamily d H)).symm
  refine ⟨Fintype.card (ChoiceFamily d H), (fun i => summand d selection (e i)), ?_, ?_, ?_⟩
  · exact (minor_eq_sum d hH selection).trans (e.sum_comp (summand d selection)).symm
  · have hcard : Fintype.card (ChoiceFamily d H) ≤
        (translationTermCount d.m d.v0 H) ^ actualRowCount d H := by
      change Fintype.card (∀ r : Row d H, RowChoice d H r) ≤ _
      rw [Fintype.card_pi]
      calc
        (∏ r : Row d H, Fintype.card (RowChoice d H r)) ≤
            ∏ _r : Row d H, translationTermCount d.m d.v0 H :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
            (fun r _ => row_choice_card_le d hH r)
        _ = (translationTermCount d.m d.v0 H) ^ actualRowCount d H := by
          simp [actualRowCount]
    have hpos : (0 : ℝ) < (translationTermCount d.m d.v0 H : ℝ) := by
      unfold translationTermCount
      positivity
    calc
      (Fintype.card (ChoiceFamily d H) : ℝ) ≤
          ((translationTermCount d.m d.v0 H : ℕ) : ℝ) ^ actualRowCount d H := by
        exact_mod_cast hcard
      _ = Real.exp ((actualRowCount d H : ℝ) *
          Real.log (translationTermCount d.m d.v0 H : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log hpos]
  · intro i
    exact norm_summand_le d hnu hH selection (e i)
