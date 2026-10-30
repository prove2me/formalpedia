-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.statistics_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:52:53.822224+00:00
-- url     : https://prove2.me/submissions/2d166207-0f4a-41fd-a26b-0d3f7803c194

import Mathlib
import Definitions.Def_OAIQ081S039
import Definitions.Def_OAIQ081S075

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Incidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite factor incidence bounds

Scopes are finite sets: a coordinate occurs at most once in any single factor,
while distinct factors may have equal scopes.  The results below count actual
incidences, bound the neighbors sharing a factor, and account for packing
Boolean variables into chunks followed by one unary validity factor per chunk.
-/

namespace SubexponentialSAT.Incidence

open scoped BigOperators

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]

omit [DecidableEq E] in
/-- Counting incidences by coordinates or by factors gives the same result. -/
theorem sum_degrees [Fintype V] (scope : E → Finset V) :
    ∑ v, degree scope v = ∑ e, (scope e).card := by
  simp_rw [degree_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp

end SubexponentialSAT.Incidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Integer high-incidence cutoff and disjoint branching on original coordinates. -/
namespace SubexponentialSAT.SqrtLog.HighIncidence

open scoped BigOperators

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem card_remainingScope_le (H : Finset V) (scope : E → Finset V) (e : E) :
    (remainingScope H scope e).card ≤ (scope e).card := by
  rw [remainingScope, Finset.card_subtype]
  exact Finset.card_filter_le _ _

end SubexponentialSAT.SqrtLog.HighIncidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceNeutral
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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
theorem neutral_factor_count (scope : E → Finset V) :
    Fintype.card (uncovered scope) ≤ Fintype.card V := by
  simpa using (Finset.card_le_univ (uncovered scope))

omit [DecidableEq E] in
theorem totalScope_neutralScope_le (scope : E → Finset V) :
    totalScope (neutralScope scope) ≤ totalScope scope + Fintype.card V := by
  rw [totalScope, Fintype.sum_sum_type]
  simp only [neutralScope, Finset.card_singleton, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one]
  exact Nat.add_le_add_left (neutral_factor_count scope) _

end SubexponentialSAT.SqrtLog.HighIncidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical mask is exactly the finite incidence cutoff on original
variables. The theorem counts zero-degree variables in the ambient dimension. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram
open scoped BigOperators


/-- Even nonnormalized supplied records overcount rather than undercount mass.
This suffices for the high-dimension bound with the physically counted S. -/
theorem suppliedScope_card_le (n : ℕ) (scopes : List (List ℕ)) (e : Fin scopes.length) :
    (suppliedScope n scopes e).card ≤ (scopes.get e).length := by
  have hi : (suppliedScope n scopes e).image Fin.val ⊆ (scopes.get e).toFinset := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact List.mem_toFinset.mpr ((Subexp.IncidencePlanSpec.mem_pattern_scope n scopes v e).mp hv)
  calc
    _ = ((suppliedScope n scopes e).image Fin.val).card :=
      (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ (scopes.get e).toFinset.card := Finset.card_le_card hi
    _ ≤ (scopes.get e).length := List.toFinset_card_le _

theorem suppliedScope_mass_le (n : ℕ) (scopes : List (List ℕ)) :
    HighIncidence.totalScope (suppliedScope n scopes) ≤ (scopes.map List.length).sum := by
  calc
    _ ≤ ∑ e : Fin scopes.length, (scopes.get e).length :=
      Finset.sum_le_sum (fun e _ => suppliedScope_card_le n scopes e)
    _ = (scopes.map List.length).sum := by
      rw [← Fin.sum_ofFn]
      change (List.ofFn (List.length ∘ scopes.get)).sum = _
      rw [← List.map_ofFn, List.ofFn_get]

end SubexponentialSAT.SqrtLog.HighIncidenceProgram

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

theorem totals_incidences (scopes : List (List ℕ)) (v : ℕ) (mask : List Bool) (t : Totals) :
    (variableTotals scopes v mask t).incidences =
      t.incidences + scanSum (fun i => max 1 (degree scopes i)) v mask := by
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

theorem incidences_exact (scopes : List (List ℕ)) (mask : List Bool) :
    (variableTotals scopes 0 mask zero).incidences = totalScope (completedScope scopes mask) := by
  rw [totals_incidences, scanSum_eq_free_sum]
  simp only [zero, Nat.zero_add]
  rw [totalScope, ← Incidence.sum_degrees]
  simp only [completed_degree]

theorem uncovered_exact (scopes : List (List ℕ)) (mask : List Bool) :
    (variableTotals scopes 0 mask zero).uncovered = (uncovered (residualScope scopes mask)).card := by
  rw [totals_uncovered, scanSum_eq_free_sum]
  simp [zero, uncovered]

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsArity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open scoped BigOperators
open LeafStatisticsProgram HighIncidence

theorem arity_le_iff (mask : List Bool) (scopes : List (List ℕ)) (a b : ℕ) :
    Arity.arity mask scopes a ≤ b ↔
      a ≤ b ∧ ∀ row ∈ scopes, (row.filter (Scope.low mask)).length ≤ b := by
  induction scopes generalizing a with
  | nil => simp [Arity.arity]
  | cons row rows ih =>
    change Arity.arity mask rows (max (row.filter (Scope.low mask)).length a) ≤ b ↔ _
    rw [ih]
    simp [ and_assoc, and_comm]

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramPositivity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Elementary nondegeneracy conditions for the measured native statistics. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
open scoped BigOperators
open LeafStatisticsSemantics

theorem free_le_ambient (scopes : List (List ℕ)) (mask : List Bool) :
    (measured scopes mask).free ≤ mask.length := by
  rw [measured, free_exact]
  simp

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafScopeResourceBoundsStatistics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Upper bounds for the actual measured statistics. The mask is the forward
reverse of the physical descending high-prefix stream. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
open LeafStatisticsProgram LeafStatisticsSemantics

theorem measured_arity_le (scopes : List (List ℕ)) (mask : List Bool) (A : ℕ)
    (ha : ∀ row ∈ scopes, row.length ≤ A) :
    max (Arity.arity mask scopes 0) (if (measured scopes mask).uncovered = 0 then 0 else 1) ≤ max A 1 := by
  apply max_le
  · apply le_trans _ (le_max_left A 1)
    apply (arity_le_iff mask scopes 0 A).mpr
    exact ⟨Nat.zero_le _, fun row hr => (List.length_filter_le _ _).trans (ha row hr)⟩
  · split_ifs <;> omega

theorem measured_uncovered_le (scopes : List (List ℕ)) (mask : List Bool) :
    (measured scopes mask).uncovered ≤ mask.length := by
  rw [measured, uncovered_exact]
  apply (Finset.card_le_univ _).trans
  simp

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

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

theorem slots_le {α : Type*} (rows : List (List α)) (D : ℕ)
    (h : ∀ row ∈ rows, row.length ≤ D) : slots rows ≤ rows.length * D := by
  induction rows with
  | nil => simp [slots]
  | cons row rows ih =>
    have hr := h row (by simp)
    have hs := ih (fun r hr => h r (by simp [hr]))
    simp only [slots, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul] at *
    omega

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafScopeResourceBoundsUniform
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Every reachable supplied-code selector trial, for every optional mark,
has the same ambient resource envelope. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
open Asymptotic HashSelectProgram LeafStatisticsProgram LeafStatisticsSemantics

/-- Neutral completion adds at most one incidence per ambient coordinate. -/
theorem measured_incidences_le (scopes : List (List ℕ)) (mask : List Bool) :
    (measured scopes mask).incidences ≤ slots scopes + mask.length := by
  have hres : HighIncidence.totalScope (residualScope scopes mask) ≤
      HighIncidence.totalScope (HighIncidenceProgram.suppliedScope mask.length scopes) := by
    apply Finset.sum_le_sum
    intro e _
    exact HighIncidence.card_remainingScope_le _ _ e
  have hcard : Fintype.card (Free mask) ≤ mask.length := by
    simp
  rw [measured, incidences_exact]
  exact (HighIncidence.totalScope_neutralScope_le _).trans
    (Nat.add_le_add (hres.trans (HighIncidenceProgram.suppliedScope_mass_le _ _)) hcard)

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafScopeInputBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Input-size bounds for explicit scopes. These bounds use actual duplicate-free
original-coordinate scope rows, with no value-only replacement for their bytes. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeInputBounds
open LeafStatisticsProgram LeafStatisticsSemantics

theorem finite_scope_length (row : List ℕ) (n : ℕ) (hd : row.Nodup)
    (hi : ∀ v ∈ row, v < n) : row.length ≤ n := by
  classical
  rw [← List.toFinset_card_of_nodup hd]
  calc
    row.toFinset.card ≤ (Finset.range n).card := Finset.card_le_card (by
      intro v hv
      exact Finset.mem_range.mpr (hi v (List.mem_toFinset.mp hv)))
    _ = n := Finset.card_range n

theorem scope_mass (scopes : List (List ℕ)) (n S : ℕ)
    (hn : n ≤ S) (hc : scopes.length ≤ S)
    (hd : ∀ row ∈ scopes, row.Nodup) (hi : ∀ row ∈ scopes, ∀ v ∈ row, v < n) :
    LeafScopeResourceBounds.slots scopes ≤ S^2 := by
  have h := LeafScopeResourceBounds.slots_le scopes n
    (fun row hr => finite_scope_length row n (hd row hr) (hi row hr))
  exact h.trans (by simpa [pow_two] using Nat.mul_le_mul hc hn)

theorem occurrence_le_rows (scopes : List (List ℕ)) (mask : List Bool) :
    (measured scopes mask).occurrence ≤ max 1 scopes.length := by
  apply (totals_occurrence_le_iff scopes 0 mask zero _).mpr
  refine ⟨Nat.zero_le _, ?_⟩
  intro i _
  apply max_le_max_left
  simpa only [Subexp.IncidencePlanSpec.degree, Subexp.IncidencePlanSpec.incidentIndices,
    Nat.zero_add] using SubexpIncidencePlanScan.incidenceFrom_length_le i.val 0 scopes

theorem statistics_bound_oai (scopes : List (List ℕ)) (mask : List Bool) (n S : ℕ)
    (hS : 1 ≤ S) (hn : n ≤ S) (hm : mask.length ≤ S) (hc : scopes.length ≤ S)
    (hd : ∀ row ∈ scopes, row.Nodup) (hi : ∀ row ∈ scopes, ∀ v ∈ row, v < n) :
    StatisticsBound scopes mask S := by
  have hf := (free_le_ambient scopes mask).trans hm
  have hu := (LeafScopeResourceBounds.measured_uncovered_le scopes mask).trans hm
  have ho := (occurrence_le_rows scopes mask).trans (max_le hS hc)
  have ha := (LeafScopeResourceBounds.measured_arity_le scopes mask n
    (fun row hr => finite_scope_length row n (hd row hr) (hi row hr))).trans (max_le hn hS)
  have hs := scope_mass scopes n S hn hc hd hi
  have hM := LeafScopeResourceBounds.measured_incidences_le scopes mask
  have hsquare : S ≤ S^2 := by nlinarith
  refine ⟨hf,ho,?_,hu,ha,?_⟩
  · omega
  · omega

end SubexponentialSAT.SqrtLog.LeafScopeInputBounds

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.statistics_bound_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.statistics_bound_oai
