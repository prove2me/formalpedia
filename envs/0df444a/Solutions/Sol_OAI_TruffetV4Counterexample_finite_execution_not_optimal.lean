-- Prove2me | solution 1 for OAI.TruffetV4Counterexample.finite_execution_not_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T17:20:07.713422+00:00
-- url     : https://prove2.me/submissions/74706899-845f-4685-8888-b092489e123a

-- Generated from openai/math@1581d4c lean/OAI/Optimization/Tropical/TruffetCounterexample.lean:L126-L143
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.TruffetV4Counterexample.finite_execution_not_optimal.
-- The statement is the platform stub (Theorems.Thm_OAI_TruffetV4Counterexample_finite_execution_not_optimal) verbatim; the proof is the source proof;
-- inline helpers are the source spans of the proof-only lemmas it needs.
import Mathlib
import Definitions.Def_TruffetCounterexample

-- ---- inline helpers from OAI.Optimization.Tropical.TruffetCounterexample ----
namespace OAI

/-! A forced pair of tropical substitutions with a strictly better feasible point. -/

noncomputable section
namespace TruffetV4Counterexample

private lemma fin3_two_ne_one : (2 : Fin 3) ≠ 1 := by decide

private lemma fin3_two_ne_zero : (2 : Fin 3) ≠ 0 := by decide

private lemma coeff_one_add_neg_one : (1 : Coeff) + ((-1 : ℝ) : Coeff) = 0 := by
  change (((1 : ℝ) + (-1) : ℝ) : Coeff) = (0 : Coeff)
  norm_num

theorem Row.ext {a b : Row} (hl : a.lhs = b.lhs) (hr : a.rhs = b.rhs) : a = b := by
  cases a
  cases b
  cases hl
  cases hr
  rfl

theorem State.ext {a b : State} (hr : a.rows = b.rows) (hc : a.cost = b.cost)
    (hv : a.remaining = b.remaining) : a = b := by
  cases a
  cases b
  cases hr
  cases hc
  cases hv
  rfl

lemma initial_crossRowRestriction : crossRowRestriction initial := by
  intro i r hir α
  fin_cases i <;> fin_cases r
  · exact (hir rfl).elim
  · refine ⟨![0, 0, 3-α], ?_⟩
    norm_num [fin3_two_ne_one, fin3_two_ne_zero, coeff_one_add_neg_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      ← WithBot.coe_one, ← WithBot.coe_add, eval, initial]
    have hreal : (0 : ℝ) < α + max 1 (-2 + (3-α)) := by
      linarith [le_max_right (1 : ℝ) (-2 + (3-α))]
    exact WithBot.coe_lt_coe.mpr hreal
  · refine ⟨![0, 0, 1-α], ?_⟩
    norm_num [fin3_two_ne_one, fin3_two_ne_zero, coeff_one_add_neg_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      ← WithBot.coe_one, ← WithBot.coe_add, eval, initial]
  · exact (hir rfl).elim

lemma advance_first : advance initial 0 1 = middle := by
  classical
  apply State.ext
  · funext i
    apply Row.ext <;> funext k <;> fin_cases i <;> fin_cases k <;>
      norm_num [fin3_two_ne_one, fin3_two_ne_zero, coeff_one_add_neg_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      ← WithBot.coe_one, ← WithBot.coe_add, advance, initial, middle, cleanup, substitute, lowerForm, column,
        nullForm, Fin.forall_fin_succ]
  · funext k
    fin_cases k <;> norm_num [fin3_two_ne_one, fin3_two_ne_zero, coeff_one_add_neg_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      ← WithBot.coe_one, ← WithBot.coe_add, advance, initial, middle, substitute, lowerForm, column]
  · funext j
    apply propext
    fin_cases j <;> simp [advance, initial, middle]

lemma advance_second : advance middle 1 0 = finalState := by
  classical
  apply State.ext
  · funext i
    apply Row.ext <;> funext k <;> fin_cases i <;> fin_cases k <;>
      norm_num [fin3_two_ne_one, fin3_two_ne_zero, coeff_one_add_neg_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      ← WithBot.coe_one, ← WithBot.coe_add, advance, middle, finalState, cleanup, substitute, lowerForm, column,
        nullForm, Fin.forall_fin_succ]
  · funext k
    fin_cases k <;> norm_num [fin3_two_ne_one, fin3_two_ne_zero, coeff_one_add_neg_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      ← WithBot.coe_one, ← WithBot.coe_add, advance, middle, finalState, substitute, lowerForm, column]
  · funext j
    apply propext
    fin_cases j <;> simp [advance, middle, finalState]

lemma first_forced : ForcedSingletonStep initial middle 0 1 := by
  classical
  unfold ForcedSingletonStep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, advance_first.symm⟩
  all_goals
    norm_num [fin3_two_ne_one, fin3_two_ne_zero, coeff_one_add_neg_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      ← WithBot.coe_one, ← WithBot.coe_add, wellFormed, bounded, stop, switch, failure, eligible, dominating, lower, upper,
      initial, middle, finalState, nullForm, substitute, lowerForm, column, Fin.forall_fin_succ, Fin.exists_fin_succ]

lemma second_forced : ForcedSingletonStep middle finalState 1 0 := by
  classical
  unfold ForcedSingletonStep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, advance_second.symm⟩
  all_goals
    norm_num [fin3_two_ne_one, fin3_two_ne_zero, coeff_one_add_neg_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      ← WithBot.coe_one, ← WithBot.coe_add, wellFormed, bounded, stop, switch, failure, eligible, dominating, lower, upper,
      middle, finalState, nullForm, substitute, lowerForm, column, Fin.forall_fin_succ,
      Fin.exists_fin_succ]

lemma final_terminal : (¬ ∃ j, finalState.remaining j) ∧ stop finalState := by
  simp [finalState, stop, nullForm]

lemma output_backsubstitution :
    (output 1 : Coeff) = eval (lowerForm initial 0 1) output ∧
    (output 0 : Coeff) = eval (lowerForm middle 1 0) output ∧ output 2 = 0 := by
  norm_num [fin3_two_ne_one, fin3_two_ne_zero, coeff_one_add_neg_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      ← WithBot.coe_one, ← WithBot.coe_add, output, eval, lowerForm, initial, middle, column]

lemma output_cost_and_feasible : feasible initial output ∧
    eval initial.cost output = (1 : Coeff) ∧
    eval finalState.cost output = (1 : Coeff) := by
  norm_num [fin3_two_ne_one, fin3_two_ne_zero, coeff_one_add_neg_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      ← WithBot.coe_one, ← WithBot.coe_add, feasible, initial, finalState, output, eval, Fin.forall_fin_succ]

lemma better_feasible_and_cost : feasible initial better ∧
    eval initial.cost better = (0 : Coeff) ∧ better 2 = 0 := by
  norm_num [fin3_two_ne_one, fin3_two_ne_zero, coeff_one_add_neg_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      ← WithBot.coe_one, ← WithBot.coe_add, feasible, initial, better, eval, Fin.forall_fin_succ]

end TruffetV4Counterexample
end

end OAI

-- ---- hoisted mission target ----
open OAI OAI.TruffetV4Counterexample

theorem solution :
    crossRowRestriction initial ∧
    ForcedSingletonStep initial middle 0 1 ∧
    ForcedSingletonStep middle finalState 1 0 ∧
    (¬ ∃ j, finalState.remaining j) ∧ stop finalState ∧
    feasible initial output ∧ feasible initial better ∧
    output 2 = 0 ∧ better 2 = 0 ∧
    (output 1 : Coeff) = eval (lowerForm initial 0 1) output ∧
    (output 0 : Coeff) = eval (lowerForm middle 1 0) output ∧
    eval initial.cost output = eval finalState.cost output ∧
    eval initial.cost better < eval finalState.cost output := by
  refine ⟨initial_crossRowRestriction, first_forced, second_forced,
    final_terminal.1, final_terminal.2, output_cost_and_feasible.1,
    better_feasible_and_cost.1, rfl, rfl, output_backsubstitution.1,
    output_backsubstitution.2.1, ?_, ?_⟩
  · rw [output_cost_and_feasible.2.1, output_cost_and_feasible.2.2]
  · rw [better_feasible_and_cost.2.1, output_cost_and_feasible.2.2]
    norm_num
