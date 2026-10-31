-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.chosen_scalar_input_cap_of_scope_resources
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:00:54.735402+00:00
-- url     : https://prove2.me/submissions/4ed93b21-596d-4592-a0c0-a510fd9d61dd

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S178
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CostAssembly_ParameterValues_serialized_values_of_fourth_power
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_chosen_query_scalars_cutoff_of_scope_resources

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryParameterBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Uniform input-polynomial numeric caps for every actually produced query.
These bounds quantify over every physical padding, while physical word-length
bounds are supplied separately by the concrete producers. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace


open SqrtLog SqrtLog.Asymptotic SqrtLog.ProducedQueryResources in
/-- One fixed polynomial bounds every serialized numeric bank value of every
large query with the actual disjoint occurrence choice. Padding lengths remain
arbitrary; this is a bound on values, not on the padded words. -/
theorem chosen_serialized_values_cutoff_of_scope_resources (k : ℕ) (hk : 2 ≤ k) :
    ∃ C degree cutoff : ℕ, ∀ n ≥ cutoff,
      let B := 4 * DisjointReuse.SparseBudget.chooseM k 1
        (sparsifySchedule n) (by omega) ^ (k - 1)
      ∀ q : LeafQueryFrontend.Query, q.Valid → ambient q = n →
        0 < q.clauses.length → q.clauses.length ≤ n * B →
        q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n q.clauses.length + 2 →
        HighIncidenceProgram.Prepare.mass q.scopeRows ≤
          (3 * n * SparseCode.degreeBound q.clauses.length B +
            (HashSelect.loopCap n q.clauses.length + 1) *
              SparseCode.distanceDenom q.clauses.length B + 1) * k →
        (∀ row ∈ q.scopeRows, row.length ≤
          (SparseCode.degreeBound q.clauses.length B + SparseCode.distanceDenom q.clauses.length B + 1) * k) →
        ∀ (padding : Fin 8 → ℕ) (j : Fin 64),
          (LeafParametersProgram.Circuit.result LeafParametersProgram.Serialization.code
            (LeafParametersProgram.Execute.guardedModel (q.input k) padding)).val j ≤
              C * (n + 1) ^ degree := by
  obtain ⟨C, degree, hvalues⟩ :=
    CostAssembly.ParameterValues.serialized_values_of_fourth_power
  obtain ⟨cutoff, hcutoff⟩ := chosen_query_scalars_cutoff_of_scope_resources k hk
  refine ⟨C, degree, cutoff, ?_⟩
  intro n hn B q hvalid hambient hnonempty hclauses hlen hmass harity padding j
  have hsmall := ((hcutoff n hn).2.2 q hvalid hambient hnonempty hclauses hlen hmass harity).2
  exact hvalues (q.input k) padding n hsmall.magnitude j

open SqrtLog SqrtLog.Asymptotic SqrtLog.ProducedQueryResources in
/-- Numeric source dimensions and all produced bank entries share a fixed
polynomial in the original input length. The actual native scan identifies
incidences, so the full raw row count is included without using rank. -/
theorem chosen_scalar_input_cap_of_scope_resources_oai (k : ℕ) (hk : 2 ≤ k) :
    ∃ C degree cutoff : ℕ, ∀ n inputLength : ℕ, cutoff ≤ n → n ≤ inputLength →
      let B := 4 * DisjointReuse.SparseBudget.chooseM k 1
        (sparsifySchedule n) (by omega) ^ (k - 1)
      ∀ q : LeafQueryFrontend.Query, q.Valid → ambient q = n →
        0 < q.clauses.length → q.clauses.length ≤ n * B →
        q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n q.clauses.length + 2 →
        HighIncidenceProgram.Prepare.mass q.scopeRows ≤
          (3 * n * SparseCode.degreeBound q.clauses.length B +
            (HashSelect.loopCap n q.clauses.length + 1) *
              SparseCode.distanceDenom q.clauses.length B + 1) * k →
        (∀ row ∈ q.scopeRows, row.length ≤
          (SparseCode.degreeBound q.clauses.length B + SparseCode.distanceDenom q.clauses.length B + 1) * k) →
        let S := C * (inputLength + 1) ^ degree
        1 ≤ S ∧ n ^ 2 ≤ S ∧ (q.input k).incidences ≤ S ∧
        ∀ (padding : Fin 8 → ℕ) (j : Fin 64),
          (LeafParametersProgram.Circuit.result LeafParametersProgram.Serialization.code
            (LeafParametersProgram.Execute.guardedModel (q.input k) padding)).val j ≤ S := by
  obtain ⟨C, degree, cutoff₁, hvalues⟩ := chosen_serialized_values_cutoff_of_scope_resources k hk
  obtain ⟨cutoff₂, hsmall⟩ := chosen_query_scalars_cutoff_of_scope_resources k hk
  refine ⟨C + 1, degree + 2, max cutoff₁ cutoff₂, ?_⟩
  intro n inputLength hn hinput B q hvalid hambient hnonempty hclauses hlen hmass harity S
  have hbase : 1 ≤ inputLength + 1 := by omega
  have hpow : 1 ≤ (inputLength + 1) ^ (degree + 2) := Nat.one_le_pow _ _ hbase
  have hS : 1 ≤ S := hpow.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hnS : n ^ 2 ≤ S := by
    calc
      _ ≤ (inputLength + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ (inputLength + 1) ^ (degree + 2) := Nat.pow_le_pow_right hbase (by omega)
      _ ≤ _ := Nat.le_mul_of_pos_left _ (by omega)
  have hs := ((hsmall n (by omega)).2.2 q hvalid hambient hnonempty hclauses hlen hmass harity).2
  refine ⟨hS, hnS, hs.incidences.trans hnS, ?_⟩
  intro padding j
  apply (hvalues n (by omega) q hvalid hambient hnonempty hclauses hlen hmass harity padding j).trans
  apply Nat.mul_le_mul (by omega)
  exact (Nat.pow_le_pow_left (by omega) degree).trans
    (Nat.pow_le_pow_right hbase (by omega))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.chosen_scalar_input_cap_of_scope_resources_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.chosen_scalar_input_cap_of_scope_resources_oai
