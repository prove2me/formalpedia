-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.arity_pos_of_free_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T13:15:09.234407+00:00
-- url     : https://prove2.me/submissions/d08d9cb7-2de4-4c79-9709-1830edaa9740

import Mathlib
import Definitions.Def_OAIQ081S092

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceNeutral
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Neutral unary factors cover exactly the otherwise unused coordinates. -/
namespace SubexponentialSAT.SqrtLog.HighIncidence

open scoped BigOperators

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [DecidableEq E] in
theorem neutralScope_covers (scope : E → Finset V) (v : V) :
    ∃ e, v ∈ neutralScope scope e := by
  by_cases h : Incidence.degree scope v = 0
  · exact ⟨.inr ⟨v, by simp [uncovered, h]⟩, by simp [neutralScope]⟩
  · have hn : (Incidence.incident scope v).Nonempty :=
      Finset.card_pos.mp (Nat.pos_of_ne_zero h)
    obtain ⟨e, he⟩ := hn
    exact ⟨.inl e, (Incidence.mem_incident scope v e).mp he⟩

end SubexponentialSAT.SqrtLog.HighIncidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsNeutral
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

theorem totals_free (scopes : List (List ℕ)) (v : ℕ) (mask : List Bool) (t : Totals) :
    (variableTotals scopes v mask t).free = t.free + scanSum (fun _ => 1) v mask := by
  induction mask generalizing v t with
  | nil => simp [variableTotals]
  | cons b bs ih =>
    cases b <;> simp [variableTotals, Totals.add, ih, Nat.add_assoc]

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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

theorem free_exact (scopes : List (List ℕ)) (mask : List Bool) :
    (variableTotals scopes 0 mask zero).free = Fintype.card (Free mask) := by
  rw [totals_free, scanSum_eq_free_sum]
  simp [zero]

theorem uncovered_exact (scopes : List (List ℕ)) (mask : List Bool) :
    (variableTotals scopes 0 mask zero).uncovered = (uncovered (residualScope scopes mask)).card := by
  rw [totals_uncovered, scanSum_eq_free_sum]
  simp [zero, uncovered]

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsArity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramPositivity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Elementary nondegeneracy conditions for the measured native statistics. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
open scoped BigOperators
open LeafStatisticsSemantics

theorem arity_pos_of_free_pos_oai (scopes : List (List ℕ)) (mask : List Bool)
    (hn : ∀ row ∈ scopes, row.Nodup)
    (hfree : 0 < (measured scopes mask).free) :
    0 < max (Arity.arity mask scopes 0)
      (if (measured scopes mask).uncovered = 0 then 0 else 1) := by
  have hc : 0 < Fintype.card (Free mask) := by simpa [measured, free_exact] using hfree
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hc
  obtain ⟨e,he⟩ := HighIncidence.neutralScope_covers (residualScope scopes mask) v
  have hcard : 0 < (completedScope scopes mask e).card :=
    Finset.card_pos.mpr ⟨v,he⟩
  rw [measured, completed_arity_exact mask scopes hn]
  exact lt_of_lt_of_le hcard
    (Finset.le_sup (f := fun e => (completedScope scopes mask e).card) (Finset.mem_univ e))

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.arity_pos_of_free_pos_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.arity_pos_of_free_pos_oai
