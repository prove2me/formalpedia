-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafPackingFiberBounds.query_factor_fiber_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:52:41.250773+00:00
-- url     : https://prove2.me/submissions/8804002e-0efe-4d68-997c-e14deaf0a6d5

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S168

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNF
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable list operations for CNF formulas

These definitions use explicit finite lists and decidable literal comparisons.
The structural bounds count list elements or comparison invocations; they make
no assumption that an arbitrary `DecidableEq` comparison has unit bit cost.
-/

namespace SubexponentialSAT.ExecCNF

universe u

variable {α : Type u} [DecidableEq α]

theorem dedupLiterals_nodup (C : Clause α) : (dedupLiterals C).Nodup := by
  induction C with
  | nil => simp [dedupLiterals]
  | cons x xs ih =>
    by_cases h : contains x xs = true
    · simpa [dedupLiterals, h] using ih
    · simp only [dedupLiterals, ite_eq_right h, List.nodup_cons]
      exact ⟨fun hm => h ((contains_true x xs).mpr ((mem_dedupLiterals x xs).mp hm)), ih⟩

end SubexponentialSAT.ExecCNF

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecSunflowerSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit finite sunflower search, with counted list scans. -/
namespace SubexponentialSAT.ExecSunflowerSearch

open ExecCNF
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

@[simp] theorem dedupLiterals_length (C : Clause α) :
    (dedupLiterals C).length = (clauseSet C).card := by
  have h := List.toFinset_card_of_nodup (dedupLiterals_nodup C)
  change (clauseSet (dedupLiterals C)).card = _ at h
  rw [clauseSet_dedupLiterals] at h
  exact h.symm

end SubexponentialSAT.ExecSunflowerSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeProducer
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Construct a clause's local chunk scope from its encoded literals

This fixed program maps actual literal records to chunk records, restores the
record order, and invokes the checked stable deduplicator. Its output order is
the last-occurrence order used by the materializer and incidence-plan producer.
-/

namespace SubexponentialSAT.SubexpScopeProducer

open BitProgram StructuredCalls SubexpChunkRecordMap

theorem scope_nodup (ell : List Bool) (codes : List ℕ) : (scope ell codes).Nodup :=
  ExecCNF.dedupLiterals_nodup _

end SubexponentialSAT.SubexpScopeProducer

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Raw hash scopes include every referenced literal, irrespective of its
coefficient. The physical materializer preserves these exact original codes. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram

theorem scope_nodup (terms : List Term) : (scope terms).Nodup :=
  SubexpScopeProducer.scope_nodup _ _

end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsNeutral
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact statistics for the neutral completion of the residual factor family. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open scoped BigOperators
open HighIncidence

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [DecidableEq E] in
theorem neutral_arity_eq (scope : E → Finset V) :
    (Finset.univ.sup fun e => (neutralScope scope e).card) =
      max (Finset.univ.sup fun e => (scope e).card)
        (if (uncovered scope).Nonempty then 1 else 0) := by
  classical
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro e _
    cases e with
    | inl e =>
      exact (Finset.le_sup (f := fun e => (scope e).card) (Finset.mem_univ e)).trans
        (le_max_left _ _)
    | inr v =>
      have hn : (uncovered scope).Nonempty := ⟨v.val, v.property⟩
      simp [neutralScope, hn]
  · apply max_le
    · apply Finset.sup_le
      intro e _
      exact Finset.le_sup (f := fun e => (neutralScope scope e).card)
        (Finset.mem_univ (Sum.inl e))
    · split_ifs with hn
      · obtain ⟨v, hv⟩ := hn
        simpa [neutralScope] using
          (Finset.le_sup (f := fun e => (neutralScope scope e).card)
            (Finset.mem_univ (Sum.inr ⟨v, hv⟩)))
      · exact Nat.zero_le _

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsTotals
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed finite-sum and maximum specifications of the native variable scan. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open scoped BigOperators
open LeafStatisticsProgram

theorem totals_uncovered (scopes : List (List ℕ)) (v : ℕ) (mask : List Bool) (t : Totals) :
    (variableTotals scopes v mask t).uncovered =
      t.uncovered + scanSum (fun i => if degree scopes i = 0 then 1 else 0) v mask := by
  induction mask generalizing v t with
  | nil => simp [variableTotals]
  | cons b bs ih =>
    cases b <;> simp [variableTotals, Totals.add, ih, Nat.add_assoc]

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The runtime scan equals the statistics of the actual residual scope family,
with precisely one neutral singleton for each unused free coordinate. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open scoped BigOperators
open LeafStatisticsProgram HighIncidence

theorem scanSum_eq_free_sum (f : ℕ → ℕ) (mask : List Bool) :
    scanSum f 0 mask = ∑ i : Free mask, f i.val.val := by
  unfold scanSum
  simp only [Nat.zero_add]
  calc
    _ = ∑ i ∈ (Finset.univ.filter fun i : Fin mask.length => i ∉ highMask mask), f i.val := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      simp only [mem_highMask, List.get_eq_getElem]
      by_cases hb : mask[i.val] = true <;> simp [hb]
    _ = _ := Finset.sum_subtype _ (by intro i; simp) _

theorem uncovered_exact (scopes : List (List ℕ)) (mask : List Bool) :
    (variableTotals scopes 0 mask zero).uncovered = (uncovered (residualScope scopes mask)).card := by
  rw [totals_uncovered, scanSum_eq_free_sum]
  simp [zero, uncovered]

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsArity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open scoped BigOperators
open LeafStatisticsProgram HighIncidence

theorem low_iff (mask : List Bool) (i : ℕ) :
    Scope.low mask i = true ↔ ∃ hi : i < mask.length, mask.get ⟨i, hi⟩ = false := by
  by_cases hi : i < mask.length
  · simp [Scope.low, hi]
  · simp [Scope.low, hi]

theorem residual_card (scopes : List (List ℕ)) (mask : List Bool)
    (e : Fin scopes.length) (hn : (scopes.get e).Nodup) :
    (residualScope scopes mask e).card = ((scopes.get e).filter (Scope.low mask)).length := by
  rw [← List.toFinset_card_of_nodup (hn.filter _)]
  apply Finset.card_bij (fun v _ => v.val.val)
  · intro v hv
    apply List.mem_toFinset.mpr
    apply List.mem_filter.mpr
    exact ⟨(residual_mem scopes mask e v).mp hv,
      (low_iff mask v.val.val).mpr ⟨v.val.isLt, free_bit mask v⟩⟩
  · intro v hv w hw h
    apply Subtype.ext
    exact Fin.ext h
  · intro i hi
    obtain ⟨hirow, hilow⟩ := List.mem_filter.mp (List.mem_toFinset.mp hi)
    obtain ⟨hib, hibit⟩ := (low_iff mask i).mp hilow
    simp only [List.get_eq_getElem] at hibit
    let v : Free mask := ⟨⟨i, hib⟩, by simp [hibit]⟩
    exact ⟨v, (residual_mem scopes mask e v).mpr hirow, rfl⟩

theorem arity_le_iff (mask : List Bool) (scopes : List (List ℕ)) (a b : ℕ) :
    Arity.arity mask scopes a ≤ b ↔
      a ≤ b ∧ ∀ row ∈ scopes, (row.filter (Scope.low mask)).length ≤ b := by
  induction scopes generalizing a with
  | nil => simp [Arity.arity]
  | cons row rows ih =>
    change Arity.arity mask rows (max (row.filter (Scope.low mask)).length a) ≤ b ↔ _
    rw [ih]
    simp [ and_assoc, and_comm]

theorem raw_arity_exact (mask : List Bool) (scopes : List (List ℕ))
    (hn : ∀ row ∈ scopes, row.Nodup) :
    Arity.arity mask scopes 0 = Finset.univ.sup (fun e => (residualScope scopes mask e).card) := by
  apply Nat.le_antisymm
  · rw [arity_le_iff]
    refine ⟨Nat.zero_le _, ?_⟩
    intro row hrow
    obtain ⟨e, rfl⟩ := List.get_of_mem hrow
    rw [← residual_card scopes mask e (hn _ (List.get_mem _ _))]
    exact Finset.le_sup (f := fun e => (residualScope scopes mask e).card)
      (Finset.mem_univ e)
  · apply Finset.sup_le
    intro e _
    rw [residual_card scopes mask e (hn _ (List.get_mem _ _))]
    exact ((arity_le_iff mask scopes 0 (Arity.arity mask scopes 0)).mp le_rfl).2
      _ (List.get_mem _ _)

theorem completed_arity_exact (mask : List Bool) (scopes : List (List ℕ))
    (hn : ∀ row ∈ scopes, row.Nodup) :
    max (Arity.arity mask scopes 0)
      (if (variableTotals scopes 0 mask zero).uncovered = 0 then 0 else 1) =
        Finset.univ.sup (fun e => (completedScope scopes mask e).card) := by
  rw [raw_arity_exact mask scopes hn, uncovered_exact, completedScope, neutral_arity_eq]
  congr 1
  by_cases h : (uncovered (residualScope scopes mask)).Nonempty
  · have hc : (uncovered (residualScope scopes mask)).card ≠ 0 :=
      Nat.ne_of_gt (Finset.card_pos.mpr h)
    simp [h, hc]
  · have hc : (uncovered (residualScope scopes mask)).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h)
    simp [h, hc]

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafPackingFiberBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Raw native incidence records have no repeated owner-factor pair. Hence their
index fibers are bounded by the statistics of the actual completed scopes. -/
namespace SubexponentialSAT.SqrtLog.LeafPackingFiberBounds
open PackingIncidenceInput LeafStatisticsSemantics LeafStatisticsProgram

 theorem factor_fiber_le_scope (scopes : List (List ℕ)) (mask : List Bool) (n : ℕ)
    (hm : mask.length ≤ n) (e : Fin (Semantics.factorCount scopes mask)) :
    (Finset.univ.filter fun i : Semantics.Incidences scopes mask =>
      Semantics.factor scopes n mask hm i=e).card ≤ (nativeScope scopes mask e).card := by
  classical
  apply Finset.card_le_card_of_injOn (freeOwner scopes mask)
  · intro i hi
    rw [← (Finset.mem_filter.mp hi).2]
    exact freeOwner_mem scopes mask n hm i
  · intro i hi j hj he
    exact free_pair_injective scopes mask n hm i j he
      ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)

 theorem factor_fiber_le (scopes : List (List ℕ)) (mask : List Bool) (n : ℕ)
    (hm : mask.length ≤ n) (hd : ∀ row ∈ scopes, row.Nodup)
    (e : Fin (Semantics.factorCount scopes mask)) :
    (Finset.univ.filter fun i : Semantics.Incidences scopes mask =>
      Semantics.factor scopes n mask hm i=e).card ≤
      max (Arity.arity mask scopes 0) (if (measured scopes mask).uncovered=0 then 0 else 1) := by
  classical
  apply (factor_fiber_le_scope scopes mask n hm e).trans
  rw [measured,completed_arity_exact mask scopes hd]
  obtain ⟨f,rfl⟩ := (factorCodeEquiv scopes mask).surjective e
  rw [nativeScope_transport]
  exact Finset.le_sup (f := fun f => (completedScope scopes mask f).card) (Finset.mem_univ _)

end SubexponentialSAT.SqrtLog.LeafPackingFiberBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafScopeResourceBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Resource bounds for the exact physical scope stream, including zero
coefficients, repeated raw slots, empty hash rows, and the optional mark. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
open HashScopeProgram

theorem scopes_nodup (t d : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ) (rows : RawTable.Rows clauses.length)
    (mark : Option (Fin clauses.length)) :
    ∀ row ∈ Complete.scopes t d codes rows mark, row.Nodup := by
  intro row hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr
    exact scope_nodup _
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    exact SubexpScopeProducer.scope_nodup _ _

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafPackingFiberBoundsQuery
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! No raw-fiber hypothesis is needed for a produced query: its actual scope
rows are deduplicated, and its parameter fields are the actual native scan. -/
namespace SubexponentialSAT.SqrtLog.LeafPackingFiberBounds
open PackingIncidenceInput LeafStatisticsProgram LeafQueryFrontend

 theorem query_scopes_nodup (q : Query) : ∀ row ∈ q.scopeRows, row.Nodup :=
  LeafScopeResourceBounds.scopes_nodup 1 0 q.codes q.rows q.mark

 theorem query_factor_fiber_le_oai (q : Query) (k : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k))
    (e : Fin (Semantics.factorCount q.scopeRows q.forward)) :
    (Finset.univ.filter fun i : Semantics.Incidences q.scopeRows q.forward =>
      Semantics.factor q.scopeRows (BinaryArithmetic.toNat q.ambient) q.forward
        (LeafProgram.Query.packingProblem q k hg).mask_le i=e).card ≤ (q.input k).arity := by
  let hm : q.forward.length ≤ BinaryArithmetic.toNat q.ambient := by
    simp [LeafQueryFrontend.Query.forward, LeafQueryFrontend.highMask]
  calc
    (Finset.univ.filter fun i : Semantics.Incidences q.scopeRows q.forward =>
        Semantics.factor q.scopeRows (BinaryArithmetic.toNat q.ambient) q.forward
          (LeafProgram.Query.packingProblem q k hg).mask_le i=e).card =
        (Finset.univ.filter fun i : Semantics.Incidences q.scopeRows q.forward =>
          Semantics.factor q.scopeRows (BinaryArithmetic.toNat q.ambient) q.forward hm i=e).card := by
      apply congrArg Finset.card
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    _ ≤ (q.input k).arity := by
      have h := factor_fiber_le q.scopeRows q.forward (BinaryArithmetic.toNat q.ambient)
        hm (query_scopes_nodup q) e
      have harity : (q.input k).arity =
          max (LeafStatisticsProgram.Arity.arity q.forward q.scopeRows 0)
            (if (LeafStatisticsProgram.measured q.scopeRows q.forward).uncovered=0 then 0 else 1) := by
        unfold LeafQueryFrontend.Query.input LeafQueryFrontend.numericInput
          LeafQueryFrontend.completedArity LeafQueryFrontend.totals
          LeafStatisticsProgram.measured LeafStatisticsProgram.Finalize.neutralArity
          LeafStatisticsProgram.zeroTotals LeafStatisticsSemantics.zero
        by_cases hz : (LeafStatisticsProgram.variableTotals q.scopeRows 0 q.forward
          { free := 0, occurrence := 0, incidences := 0, uncovered := 0 }).uncovered=0
        · rw [ite_eq_left hz]
        · rw [ite_eq_right hz]
      rw [harity]
      convert h using 1
      all_goals try with_reducible_and_instances rfl

end SubexponentialSAT.SqrtLog.LeafPackingFiberBounds

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafPackingFiberBounds.query_factor_fiber_le_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafPackingFiberBounds.query_factor_fiber_le_oai
