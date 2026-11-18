-- Prove2me | solution 1 for OAI.EditApproximation.physicalFamilyDependencyTree_valid
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:42:26.469759+00:00
-- url     : https://prove2.me/submissions/001aa6d8-d0e7-4dd4-b461-881102cccb63

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea002
import Definitions.Def_OAIQ361V3Ea003
import Theorems.Thm_OAI_EditApproximation_computed_chargedRandomGlobalQuery_earlier_reads
import Theorems.Thm_OAI_EditApproximation_computed_localRandomDataQuery_table_cost

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_DependencyExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite dependency expansions with two edge sorts. The certificate
checks progress and local branching at every actual node; the global
count follows from these local conditions. -/

namespace EditApproximation

open Finset

namespace DependencyExpansion

section Builder

variable {ι : Type*} (d r m n : ι → ℕ)
  (s : (x : ι) → Fin (m x) → ι) (e : (x : ι) → Fin (n x) → ι)
  (hs : ∀ x i, d (s x i) < d x ∧ r (s x i) ≤ r x)
  (he : ∀ x i, d (e x i) ≤ d x ∧ r (e x i) < r x)

theorem build_depth (root : ι) : (build d r m n s e hs he root).depth = d root := by
  rw [build]
  rfl

theorem build_rank (root : ι) : (build d r m n s e hs he root).rank = r root := by
  rw [build]
  rfl

theorem build_valid (a b : ℕ) (hm : ∀ x, m x ≤ a) (hn : ∀ x, n x ≤ b) (root : ι) :
    Valid a b (build d r m n s e hs he root) := by
  have hall : ∀ fuel x, d x + r x = fuel → Valid a b (build d r m n s e hs he x) := by
    intro fuel
    induction fuel using Nat.strong_induction_on with
    | h fuel ih =>
      intro x hx
      rw [build]
      refine ⟨hm x, hn x, ?_, ?_⟩
      · intro i
        refine ⟨?_, ?_, ?_⟩
        · rw [build_depth]
          exact (hs x i).1
        · rw [build_rank]
          exact (hs x i).2
        · apply ih (d (s x i) + r (s x i)) _ (s x i) rfl
          rw [← hx]
          exact Nat.add_lt_add_of_lt_of_le (hs x i).1 (hs x i).2
      · intro i
        refine ⟨?_, ?_, ?_⟩
        · rw [build_depth]
          exact (he x i).1
        · rw [build_rank]
          exact (he x i).2
        · apply ih (d (e x i) + r (e x i)) _ (e x i) rfl
          rw [← hx]
          exact Nat.add_lt_add_of_le_of_lt (he x i).1 (he x i).2
  exact hall (d root + r root) root rfl

end Builder

end DependencyExpansion
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RankedMemoWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counts of the actual persistent interpreter. Dictionary operations
are charged on every request, including hits; insertion and retained-node
costs are charged only when a value is computed. -/

namespace EditApproximation

namespace FiniteQuery

theorem cost_eq_sum {ι : Type*} (oracle : ι → ℚ) (weight : ι → ℕ)
    (program : FiniteQuery ι) :
    program.cost oracle weight = ((program.keys oracle).map weight).sum := by
  induction program with
  | done _ => rfl
  | read key next ih => exact congrArg (weight key + ·) (ih (oracle key))

end FiniteQuery

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteQueryWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact read costs for the finite query combinators used in warmup
and refinement. In particular, a collected value is computed once and
is reused by the continuation's local arithmetic. -/

namespace EditApproximation.FiniteQuery

theorem cost_bind {ι : Type*} (oracle : ι → ℚ) (weight : ι → ℕ)
    (program : FiniteQuery ι) (next : ℚ → FiniteQuery ι) :
    (bind program next).cost oracle weight = program.cost oracle weight +
      (next (program.value oracle)).cost oracle weight := by
  induction program with
  | done result => simp only [bind, cost, value, Nat.zero_add]
  | read key continuation ih =>
    simp only [bind, cost, value, ih, Nat.add_assoc]

theorem cost_collect {ι κ : Type*} (oracle : ι → ℚ) (weight : ι → ℕ)
    (reader : κ → FiniteQuery ι) (keys : List κ) (next : List ℚ → FiniteQuery ι) :
    (collect reader keys next).cost oracle weight =
      (keys.map fun key => (reader key).cost oracle weight).sum +
      (next (keys.map fun key => (reader key).value oracle)).cost oracle weight := by
  induction keys generalizing next with
  | nil => simp only [collect, List.map_nil, List.sum_nil, Nat.zero_add]
  | cons key keys ih =>
    simp only [collect, cost_bind, ih, List.map_cons, List.sum_cons, Nat.add_assoc]

end EditApproximation.FiniteQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteQueryRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Restriction of adaptive read programs to a proved finite request domain.
The restriction visits the same reads whenever the original execution stays
in that domain. It does not enumerate the domain. -/

namespace EditApproximation.FiniteQuery



 theorem mapKeys_cost {ι κ : Type*} (f : ι → κ) (oracle : κ → ℚ) (weight : κ → ℕ)
    (program : FiniteQuery ι) :
    (mapKeys f program).cost oracle weight = program.cost (oracle ∘ f) (weight ∘ f) := by
  induction program with
  | done result => rfl
  | read key next ih => exact congrArg (fun rest => weight (f key) + rest) (ih (oracle (f key)))

 theorem restrict_cost {ι : Type*} (P : ι → Prop) [DecidablePred P]
    (oracle : ι → ℚ) (weight : ι → ℕ) (program : FiniteQuery ι)
    (hvalid : ∀ key ∈ program.keys oracle, P key) :
    (restrict P program).cost (fun key => oracle key.val) (fun key => weight key.val) =
      program.cost oracle weight := by
  induction program with
  | done result => rfl
  | read key next ih =>
    have hk : P key := hvalid key (by simp only [keys, List.mem_cons, true_or])
    have hnext : ∀ other ∈ (next (oracle key)).keys oracle, P other := by
      intro other hother
      exact hvalid other (List.mem_cons_of_mem key hother)
    simpa only [restrict, dite_eq_left hk, cost] using
      congrArg (fun rest => weight key + rest) (ih (oracle key) hnext)

end EditApproximation.FiniteQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRefinementReadWork
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Split the literal recursive reads by the unified table index. The
current-index reads are physical-child requests; initial data, warmup
mass and old history have strictly smaller indices. -/

namespace EditApproximation

theorem physicalRefinementWarmupRead_cost_current {M J ny : ℕ} (pass copy T S t : ℕ)
    (ht : 0 < t) (node : PhysicalNode M J) (q : TargetInterval ny)
    (otherNode : PhysicalNode M J) (hnode : node.1.val ≤ otherNode.1.val)
    (j : ℕ) (hj : j ≤ T) (r : TargetInterval ny) (oracle) :
    (physicalRefinementWarmupRead pass copy T S t ht node q otherNode hnode j hj r).cost
      oracle (fun request => physicalCurrentReadWeight (T + t) request.val) = 0 := by
  have hne : j ≠ T + t := by omega
  simp only [physicalRefinementWarmupRead, FiniteQuery.cost, physicalCurrentReadWeight,
    PhysicalTableRequest.warmup, ite_eq_right hne, Nat.add_zero]

theorem physicalRefinementMassQuery_cost_current {M J ny : ℕ} (pass copy T S t : ℕ)
    (ht : 0 < t) (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (q : TargetInterval ny) (input : Fin M × TargetInterval ny) (oracle) :
    (physicalRefinementMassQuery pass copy T S t ht node hbelow q input).cost
      oracle (fun request => physicalCurrentReadWeight (T + t) request.val) = 0 := by
  simp only [physicalRefinementMassQuery, FiniteQuery.cost_collect, FiniteQuery.cost,
    physicalRefinementWarmupRead_cost_current, List.map_ofFn, Function.comp_def,
    List.sum_ofFn, Finset.sum_const_zero, Nat.add_zero]

theorem physicalRefinementCurrentQuery_cost_current {M J ny : ℕ} (pass copy T S t : ℕ)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (q : TargetInterval ny)
    (input : Fin M × TargetInterval ny) (oracle) :
    (physicalRefinementCurrentQuery pass copy T S t node hbelow q input).cost
      oracle (fun request => physicalCurrentReadWeight (T + t) request.val) = 1 := by
  simp only [physicalRefinementCurrentQuery, FiniteQuery.cost, physicalCurrentReadWeight,
    PhysicalTableRequest.refinement, ite_true, if_true, Nat.add_zero]

theorem physicalRefinementEarlierQuery_cost_current {M J ny : ℕ} (pass copy T S t : ℕ)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (q : TargetInterval ny)
    (input : Fin M × ℕ × TargetInterval ny) (oracle) :
    (physicalRefinementEarlierQuery pass copy T S t node hbelow q input).cost
      oracle (fun request => physicalCurrentReadWeight (T + t) request.val) = 0 := by
  unfold physicalRefinementEarlierQuery
  split_ifs with hs
  · have hne : T + input.2.1 ≠ T + t := by omega
    simp only [FiniteQuery.cost, physicalCurrentReadWeight, PhysicalTableRequest.refinement,
      hne, ↓reduceIte, Nat.add_zero]
  · rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalQueryProgress
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dependency split for keys actually emitted by the adaptive local
queries. Current-index edges descend in the physical tree; older reads
decrease the table rank and never move to an ancestor. -/

namespace EditApproximation

namespace PhysicalTableRequest

theorem rank_lt_iff_index_lt_of_pass {M J ny : ℕ} (T S : ℕ)
    (parent child : PhysicalTableRequest M J ny) (hpass : child.pass = parent.pass) :
    child.rank T S < parent.rank T S ↔ child.index < parent.index := by
  unfold rank
  rw [hpass]
  omega

theorem rank_not_lt_iff_index_eq_of_pass {M J ny : ℕ} (T S : ℕ)
    (parent child : PhysicalTableRequest M J ny) (hpass : child.pass = parent.pass)
    (hindex : child.index ≤ parent.index) :
    ¬ child.rank T S < parent.rank T S ↔ child.index = parent.index := by
  rw [rank_lt_iff_index_lt_of_pass T S parent child hpass]
  omega

end PhysicalTableRequest

theorem physicalRefinementWarmupRead_keys_pass_copy {M J ny : ℕ}
    (pass copy T S t : ℕ) (ht : 0 < t) (node : PhysicalNode M J) (q : TargetInterval ny)
    (otherNode : PhysicalNode M J) (hnode : node.1.val ≤ otherNode.1.val)
    (j : ℕ) (hj : j ≤ T) (r : TargetInterval ny) (oracle) :
    ∀ key ∈ (physicalRefinementWarmupRead pass copy T S t ht node q otherNode hnode j hj r).keys oracle,
      key.val.pass = pass ∧ key.val.copy = copy ∧ key.val.index ≤ T + t := by
  intro key hk
  simp only [physicalRefinementWarmupRead, FiniteQuery.keys, List.mem_singleton] at hk
  subst key
  exact ⟨rfl, rfl, hj.trans (Nat.le_add_right T t)⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GlobalQueryCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact weighted-cost transport for the full internal refinement body.
In this branch every request is an ordinary table request: parent initial,
child mass, child initial, old history or a current physical child. -/

namespace EditApproximation

namespace FiniteQuery

theorem cost_congr_weights {ι : Type*} (oracle : ι → ℚ) (program : FiniteQuery ι)
    (left right : ι → ℕ) (heq : ∀ key ∈ program.keys oracle, left key = right key) :
    program.cost oracle left = program.cost oracle right := by
  rw [cost_eq_sum, cost_eq_sum]
  congr 1
  exact List.map_congr_left heq

end FiniteQuery

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedIndexCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The charged request index distinguishes previous passes and coarse
leaves. For internal refinement its two index classes are exactly the
current and earlier table-read counters. -/

namespace EditApproximation

theorem chargedSameWeight_table {M J ny passes copies T S : ℕ}
    (parent : {r : PhysicalTableRequest M J ny // r.Bounded passes copies T S}) :
    chargedSameWeight (Sum.inr parent) = chargedTableWeight 0
      (fun child => if ¬ child.rank T S < parent.val.rank T S then 1 else 0) := by
  funext child
  cases child <;> simp only [chargedSameWeight, ChargedPhysicalRequest.index, chargedTableWeight,
    Nat.zero_lt_succ, not_true_eq_false, ite_false, if_false, Nat.add_lt_add_iff_right]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SourceRankedRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Restrict only the recursive table keys of a mixed source/table query.
The source reads remain explicit. This preserves the finite cache domain
without materializing any counterfactual table. -/

namespace EditApproximation.SourceRanked

variable {σ κ : Type*} (tableRank : κ → ℕ) (supported : κ → Prop)







 theorem restrictBody_cost
    (tableBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
    (sourceValue : σ → ℚ) (tableValue : κ → ℚ) (sourceWeight : σ → ℕ) (tableWeight : κ → ℕ)
    (parent : {key : κ // supported key})
    (hkeys : ∀ key ∈ (tableBody parent.val).keys (Sum.elim sourceValue (fun key => tableValue key.val)),
      supportedChild tableRank supported parent.val key) :
    (restrictBody tableRank supported tableBody parent).cost
        (Sum.elim sourceValue (fun key => tableValue key.val.val))
        (Sum.elim sourceWeight (fun key => tableWeight key.val.val)) =
      (tableBody parent.val).cost (Sum.elim sourceValue (fun key => tableValue key.val))
        (Sum.elim sourceWeight (fun key => tableWeight key.val)) := by
  classical
  unfold restrictBody
  rw [FiniteQuery.mapKeys_cost]
  have horacle :
      (Sum.elim sourceValue (fun key => tableValue key.val.val)) ∘
        supportedChildMap tableRank supported parent =
      (fun key => (Sum.elim sourceValue (fun key => tableValue key.val)) key.val) := by
    funext key
    rcases key with ⟨key, hs⟩
    cases key <;> rfl
  have hweight :
      (Sum.elim sourceWeight (fun key => tableWeight key.val.val)) ∘
        supportedChildMap tableRank supported parent =
      (fun key => (Sum.elim sourceWeight (fun key => tableWeight key.val)) key.val) := by
    funext key
    rcases key with ⟨key, hs⟩
    cases key <;> rfl
  rw [horacle, hweight]
  exact FiniteQuery.restrict_cost _ _ _ _ hkeys

end EditApproximation.SourceRanked

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRandomBoundedCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Bounded

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (initial : PhysicalEntry M J target.length → ℕ)
  (sourceValue : σ → ℚ) (tableValue : PhysicalTableRequest M J target.length → ℚ)

 theorem physicalRandomBoundedQuery_cost (sourceWeight : σ → ℕ)
    (tableWeight : PhysicalTableRequest M J target.length → ℕ)
    (request : {request : PhysicalTableRequest M J target.length // request.Bounded passes copies T S}) :
    (physicalRandomBoundedQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request).cost
      (Sum.elim sourceValue (fun child => tableValue child.val.val))
      (Sum.elim sourceWeight (fun child => tableWeight child.val.val)) =
    (physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request.val).cost
      (Sum.elim sourceValue (fun child => tableValue child.val))
      (Sum.elim sourceWeight (fun child => tableWeight child.val)) := by
  unfold physicalRandomBoundedQuery
  exact SourceRanked.restrictBody_cost _ _ _ _ _ _ _ request
    (physicalRandomGlobalQuery_keys_bounded source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta readGroup readInteger initial request.val request.property _)

end Bounded

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRandomPassCopy
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every recursive table read of an adaptive random query stays in the same
pass and copy and has no larger local index. -/

namespace EditApproximation

 theorem physicalRandomDataRequest_keys_pass_copy {σ α : Type*} (source target : List α)
    {M J : ℕ} [NeZero M] (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ)
    (pass copy T S t : ℕ) (ht : 0 < t)
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (readGroup : GroupScalarKey M F Q → FiniteQuery σ)
    (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
    (q : TargetInterval target.length) (oracle) :
    ∀ key ∈ (physicalRandomDataRequestQuery source target N P F exponent H Q tau a eta kappa delta
      pass copy T S t ht node hbelow readGroup readInteger q).keys oracle,
      match key with
      | .inl _ => True
      | .inr table => table.val.pass = pass ∧ table.val.copy = copy ∧ table.val.index ≤ T + t := by
  unfold physicalRandomDataRequestQuery
  apply localRandomDataQuery_keys_all
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    intro key _
    trivial
  · intro input range
    apply FiniteQuery.keys_all_mapKeys
    intro key _
    trivial
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    intro key hk
    unfold physicalRefinementEarlierQuery at hk
    split_ifs at hk with hs
    · simp only [FiniteQuery.keys, List.mem_singleton] at hk
      subst key
      exact ⟨rfl, rfl, by change T + input.2.1 ≤ T + t; omega⟩
    · exact False.elim (List.not_mem_nil hk)
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    intro key hk
    simp only [physicalRefinementCurrentQuery, FiniteQuery.keys, List.mem_singleton] at hk
    subst key
    exact ⟨rfl, rfl, le_rfl⟩
  · intro r
    apply FiniteQuery.keys_all_mapKeys
    intro key hk
    exact physicalRefinementWarmupRead_keys_pass_copy pass copy T S t ht node q node le_rfl
      0 (Nat.zero_le T) r _ key hk
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    unfold physicalRefinementMassQuery
    apply FiniteQuery.keys_all_collect
    · intro j _ key hk
      exact physicalRefinementWarmupRead_keys_pass_copy pass copy T S t ht node q
        (physicalChild node hbelow input.1) _ j.val (Nat.le_of_lt j.isLt) input.2 _ key hk
    · intro values key hk
      exact False.elim (List.not_mem_nil hk)
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    intro key hk
    exact physicalRefinementWarmupRead_keys_pass_copy pass copy T S t ht node q
      (physicalChild node hbelow input.1) _ 0 (Nat.zero_le T) input.2 _ key hk

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRandomRankCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! For a fixed pass, the physical rank partition equals the concrete
warmup/refinement index partition on every emitted data-query key. -/

namespace EditApproximation

section Costs

variable {σ α : Type*} (source target : List α) {M J : ℕ} [NeZero M]
  (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ)
  (pass copy T S t : ℕ) (ht : 0 < t) (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (readGroup : GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ)
  (q : TargetInterval target.length) (answer : PhysicalTableRequest M J target.length → ℚ)

theorem physicalRandomDataRequest_same_rank_cost :
    (physicalRandomDataRequestQuery source target N P F exponent H Q tau a eta kappa delta
      pass copy T S t ht node hbelow readGroup readInteger q).cost (Sum.elim sourceAnswer (fun child => answer child.val))
      (Sum.elim (fun _ => 0) (fun child => if ¬ child.val.rank T S <
        (PhysicalTableRequest.refinement pass copy node T t q).rank T S then 1 else 0)) =
    (physicalRandomDataRequestQuery source target N P F exponent H Q tau a eta kappa delta
      pass copy T S t ht node hbelow readGroup readInteger q).cost (Sum.elim sourceAnswer (fun child => answer child.val))
      (Sum.elim (fun _ => 0) (fun child => physicalCurrentReadWeight (T + t) child.val)) := by
  apply FiniteQuery.cost_congr_weights
  intro key hk
  have hkey := physicalRandomDataRequest_keys_pass_copy source target N P F exponent H Q
    tau a eta kappa delta pass copy T S t ht node hbelow readGroup readInteger q _ key hk
  cases key with
  | inl key => rfl
  | inr key =>
    simp only [Sum.elim_inr]
    have heq := PhysicalTableRequest.rank_not_lt_iff_index_eq_of_pass T S
      (PhysicalTableRequest.refinement pass copy node T t q) key.val hkey.1 hkey.2.2
    by_cases hi : key.val.index = T + t
    · have hr := heq.mpr hi
      simp only [ite_eq_left hr, physicalCurrentReadWeight, ite_eq_left hi]
    · have hr : ¬ ¬ key.val.rank T S <
          (PhysicalTableRequest.refinement pass copy node T t q).rank T S := fun h => hi (heq.mp h)
      simp only [ite_eq_right hr, physicalCurrentReadWeight, ite_eq_right hi]

end Costs

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedRandomCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Cost

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (initial : PhysicalEntry M J target.length → ℕ)
  (sourceAnswer : σ → ℚ) (answer : PhysicalTableRequest M J target.length → ℚ)
  (sourceWeight : σ → ℕ) (coarse : ℕ) (weight : PhysicalTableRequest M J target.length → ℕ)

 theorem physicalRandomGlobalQuery_refinement_cost
    (request : PhysicalTableRequest M J target.length)
    (hindex : T < request.index) (hbelow : request.node.1.val < J)
    (hshort : ¬ (physicalSourceInterval source.length request.node).hi -
      (physicalSourceInterval source.length request.node).lo ≤ 1) :
    (physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request).cost
      (Sum.elim sourceAnswer (fun child => answer child.val))
      (Sum.elim sourceWeight (fun child => weight child.val)) =
    (physicalRandomDataRequestQuery source target N P F exponent H Q tau
      (refinementFactor (factor request.pass) F) eta kappa delta request.pass request.copy T S
      (request.index - T) (Nat.sub_pos_of_lt hindex) request.node hbelow
      (readGroup request.pass request.copy ⟨request.node, hbelow⟩ (Fin.ofNat R (request.index - T - 1)))
      (readInteger request.pass request.copy ⟨request.node, hbelow⟩ (Fin.ofNat R (request.index - T - 1)))
      request.state).cost (Sum.elim sourceAnswer (fun child => answer child.val))
        (Sum.elim sourceWeight (fun child => weight child.val)) := by
  unfold physicalRandomGlobalQuery
  rw [dite_eq_left ⟨hindex, hbelow, hshort⟩, FiniteQuery.mapKeys_cost]
  congr 1 <;> (funext key; cases key <;> rfl)

 theorem chargedRandomGlobalQuery_refinement_cost
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
    (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J)
    (hshort : ¬ (physicalSourceInterval source.length parent.val.node).hi -
      (physicalSourceInterval source.length parent.val.node).lo ≤ 1) :
    (chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger initial (Sum.inr parent)).cost
      (Sum.elim sourceAnswer (fun child => Sum.elim (fun entry => (initial entry : ℚ))
        (fun r => answer r.val) child.val))
      (Sum.elim sourceWeight (fun child => chargedTableWeight coarse weight child.val)) =
    (physicalRandomDataRequestQuery source target N P F exponent H Q tau
      (refinementFactor (factor parent.val.pass) F) eta kappa delta parent.val.pass parent.val.copy T S
      (parent.val.index - T) (Nat.sub_pos_of_lt hindex) parent.val.node hbelow
      (readGroup parent.val.pass parent.val.copy ⟨parent.val.node, hbelow⟩
        (Fin.ofNat R (parent.val.index - T - 1)))
      (readInteger parent.val.pass parent.val.copy ⟨parent.val.node, hbelow⟩
        (Fin.ofNat R (parent.val.index - T - 1))) parent.val.state).cost
      (Sum.elim sourceAnswer (fun child => answer child.val))
      (Sum.elim sourceWeight (fun child => weight child.val)) := by
  unfold chargedRandomGlobalQuery
  dsimp only
  rw [ite_eq_right (Nat.not_le.mpr hindex), ite_eq_left hbelow, ite_eq_right hshort, FiniteQuery.mapKeys_cost]
  have hcost := physicalRandomBoundedQuery_cost source target N P F exponent H Q T S passes copies
    factor multiplier tau eta kappa delta readGroup readInteger initial sourceAnswer answer
    sourceWeight weight parent
  have heq : (physicalRandomBoundedQuery source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta readGroup readInteger initial parent).cost
      (Sum.elim sourceAnswer (fun child => answer child.val.val))
      (Sum.elim sourceWeight (fun child => weight child.val.val)) = _ := hcost
  calc
    _ = (physicalRandomBoundedQuery source target N P F exponent H Q T S passes copies
        factor multiplier tau eta kappa delta readGroup readInteger initial parent).cost
        (Sum.elim sourceAnswer (fun child => answer child.val.val))
        (Sum.elim sourceWeight (fun child => weight child.val.val)) := by
      congr 1 <;> (funext key; cases key <;> rfl)
    _ = _ := heq.trans (physicalRandomGlobalQuery_refinement_cost source target N P F exponent H Q T S
      copies factor multiplier tau eta kappa delta readGroup readInteger initial sourceAnswer answer
      sourceWeight weight parent.val hindex hbelow hshort)

end Cost

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryDependencyExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dependency tree here is obtained from the requests made by the
finite adaptive program at its actual answers. Local depth/index progress
therefore bounds execution, rather than an independently supplied tree. -/

namespace EditApproximation

open Finset

section Queries

variable {κ : Type*} (depth index : κ → ℕ)
  (program : (key : κ) → FiniteQuery
    {child : κ // depth child + index child < depth key + index key})

variable (progress : ∀ key child, child ∈ queryRequestList depth index program key →
  (depth child < depth key ∧ index child ≤ index key) ∨
  (depth child ≤ depth key ∧ index child < index key))

include progress

theorem queryDependencyExpansion_valid (a b : ℕ)
    (hsame : ∀ key, (querySameRequests depth index program key).length ≤ a)
    (hearlier : ∀ key, (queryEarlierRequests depth index program key).length ≤ b) (root : κ) :
    DependencyExpansion.Valid a b (queryDependencyExpansion depth index program progress root) :=
  DependencyExpansion.build_valid _ _ _ _ _ _ _ _ a b hsame hearlier root

end Queries

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryDependencyCosts
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted read counts are the actual same-index and earlier-index
lengths used by the dependency expansion, after identifying its values
with the local mathematical recurrence. -/

namespace EditApproximation

theorem list_filter_length_eq_sum {κ : Type*} (keys : List κ) (predicate : κ → Bool) :
    (keys.filter predicate).length = (keys.map fun key => if predicate key then 1 else 0).sum := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
    cases hp : predicate key <;> simp [hp, ih, Nat.add_comm]


section Queries

variable {κ : Type*} (depth index : κ → ℕ)
  (program : (key : κ) → FiniteQuery {child : κ // depth child + index child < depth key + index key})
  (expected : κ → ℚ)
  (hstep : ∀ key, (program key).value (fun child => expected child.val) = expected key)

include hstep

theorem queryRequestList_expected (key : κ) :
    queryRequestList depth index program key =
      ((program key).keys (fun child => expected child.val)).map Subtype.val := by
  unfold queryRequestList
  simp only [rankedProgramValue_eq (fun key => depth key + index key) program expected hstep]

theorem querySameRequests_length_eq_cost (key : κ) :
    (querySameRequests depth index program key).length =
      (program key).cost (fun child => expected child.val)
        (fun child => if ¬ index child.val < index key then 1 else 0) := by
  unfold querySameRequests
  rw [queryRequestList_expected depth index program expected hstep,
    list_filter_length_eq_sum, FiniteQuery.cost_eq_sum, List.map_map]
  simp only [Function.comp_def, Bool.not_eq_true', decide_eq_false_iff_not]

theorem queryEarlierRequests_length_eq_cost (key : κ) :
    (queryEarlierRequests depth index program key).length =
      (program key).cost (fun child => expected child.val)
        (fun child => if index child.val < index key then 1 else 0) := by
  unfold queryEarlierRequests
  rw [queryRequestList_expected depth index program expected hstep,
    list_filter_length_eq_sum, FiniteQuery.cost_eq_sum, List.map_map]
  simp only [Function.comp_def, decide_eq_true_eq]

end Queries

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteQueryCostOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.FiniteQuery

theorem cost_zero {ι : Type*} (oracle : ι → ℚ) (program : FiniteQuery ι) :
    program.cost oracle (fun _ => 0) = 0 := by
  induction program with
  | done result => rfl
  | read key next ih => simpa only [cost, Nat.zero_add] using ih (oracle key)

theorem cost_eq_zero_of_keys {ι : Type*} (oracle : ι → ℚ) (program : FiniteQuery ι)
    (weight : ι → ℕ) (hzero : ∀ key ∈ program.keys oracle, weight key = 0) :
    program.cost oracle weight = 0 :=
  (cost_congr_weights oracle program weight (fun _ => 0) hzero).trans (cost_zero oracle program)

end EditApproximation.FiniteQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedTerminalCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Warmup and terminal queries have no same-index requests. Their
charged seed reads strictly decrease the pass index, including coarse
entries at pass zero. -/

namespace EditApproximation

theorem chargedWarmupQuery_same_cost_zero {α : Type*} [DecidableEq α] {M J passes copies T S : ℕ}
    (source target : List α) (N P F : ℕ) (factor : ℕ → ℚ) (multiplier : ℕ → ℕ)
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S}) (oracle) :
    (chargedWarmupQuery source target N P F factor multiplier parent).cost oracle
      (fun child => chargedSameWeight (Sum.inr parent) child.val) = 0 := by
  apply FiniteQuery.cost_eq_zero_of_keys
  intro key hk
  have h := chargedWarmupQuery_keys_earlier source target N P F factor multiplier parent oracle key hk
  exact ite_eq_right (not_not_intro h.2)

theorem chargedInitialQuery_same_cost_zero {α : Type*} [DecidableEq α] {M J passes copies T S : ℕ}
    (source target : List α) (N P F : ℕ) (factor : ℕ → ℚ) (multiplier : ℕ → ℕ)
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S}) (oracle) :
    (physicalInitialQuery source target N P F (factor parent.val.pass)
      (chargedSeedQuery N multiplier parent) (parent.val.node, parent.val.state)).cost oracle
      (fun child => chargedSameWeight (Sum.inr parent) child.val) = 0 := by
  apply FiniteQuery.cost_eq_zero_of_keys
  have hkeys := physicalInitialQuery_keys_all source target N P F (factor parent.val.pass)
    (chargedSeedQuery N multiplier parent) parent.val.node parent.val.state oracle
    (fun key => key.val.index < ChargedPhysicalRequest.index (Sum.inr parent))
    (fun q key hk => (chargedSeedQuery_keys_earlier N multiplier parent (parent.val.node, q) oracle key hk).2)
  intro key hk
  exact ite_eq_right (not_not_intro (hkeys key hk))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SourceErasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing already fixed source answers is a proof operation on a
query. It preserves the table trace and separates source/table charges;
the implementation continues to cache and sample explicit source keys. -/

namespace EditApproximation.FiniteQuery

variable {σ κ : Type*}

 theorem eraseSources_cost (sourceAnswer : σ → ℚ) (tableAnswer : κ → ℚ)
    (tableWeight : κ → ℕ) (query : FiniteQuery (Sum σ κ)) :
    (eraseSources sourceAnswer query).cost tableAnswer tableWeight =
      query.cost (Sum.elim sourceAnswer tableAnswer) (Sum.elim (fun _ => 0) tableWeight) := by
  induction query with
  | done value => rfl
  | read key next ih =>
    cases key with
    | inl source => simpa only [eraseSources, cost, Sum.elim_inl, Nat.zero_add] using ih (sourceAnswer source)
    | inr table => exact congrArg (tableWeight table + ·) (ih (tableAnswer table))

end EditApproximation.FiniteQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedRandomIndexCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Costs

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R → (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ) (answer : PhysicalTableRequest M J target.length → ℚ)
  (initial : PhysicalEntry M J target.length → ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
  (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J)
  (hshort : ¬ (physicalSourceInterval source.length parent.val.node).hi -
    (physicalSourceInterval source.length parent.val.node).lo ≤ 1)

include hindex hbelow hshort

theorem chargedRandomGlobalQuery_current_cost :
    (chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger initial (Sum.inr parent)).cost
      (Sum.elim sourceAnswer (fun child => Sum.elim (fun entry => (initial entry : ℚ))
        (fun r => answer r.val) child.val))
      (Sum.elim (fun _ => 0) (fun child => chargedSameWeight (Sum.inr parent) child.val)) =
    (physicalRandomDataRequestQuery source target N P F exponent H Q tau
      (refinementFactor (factor parent.val.pass) F) eta kappa delta parent.val.pass parent.val.copy T S
      (parent.val.index - T) (Nat.sub_pos_of_lt hindex) parent.val.node hbelow
      (readGroup parent.val.pass parent.val.copy ⟨parent.val.node, hbelow⟩ (Fin.ofNat R (parent.val.index - T - 1)))
      (readInteger parent.val.pass parent.val.copy ⟨parent.val.node, hbelow⟩ (Fin.ofNat R (parent.val.index - T - 1)))
      parent.val.state).cost
      (Sum.elim sourceAnswer (fun child => answer child.val))
      (Sum.elim (fun _ => 0) (fun child => physicalCurrentReadWeight (T + (parent.val.index - T)) child.val)) := by
  simp only [chargedSameWeight_table]
  rw [chargedRandomGlobalQuery_refinement_cost source target N P F exponent H Q T S passes copies
    factor multiplier tau eta kappa delta readGroup readInteger initial sourceAnswer answer (fun _ => 0) _ _ parent hindex hbelow hshort]
  have hrank : (PhysicalTableRequest.refinement parent.val.pass parent.val.copy parent.val.node
      T (parent.val.index - T) parent.val.state).rank T S = parent.val.rank T S := by
    unfold PhysicalTableRequest.refinement PhysicalTableRequest.rank
    dsimp only
    congr 1
    omega
  rw [← hrank]
  exact physicalRandomDataRequest_same_rank_cost source target N P F exponent H Q tau
    (refinementFactor (factor parent.val.pass) F) eta kappa delta parent.val.pass parent.val.copy T S
    (parent.val.index - T) (Nat.sub_pos_of_lt hindex) parent.val.node hbelow _ _ sourceAnswer parent.val.state answer

end Costs

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedRandomPhysicalCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Physical

variable {σ α : Type*} (source target : List α) {M J : ℕ} [NeZero M]
  (N P H : ℕ) (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
  (hM : M = (integerParameters N).M) (hP : P = (integerParameters N).P)
  (A tau eta kappa delta : ℚ) (hA : A ≤ ((integerParameters N).initialFactor : ℚ))
  (pass copy T S t : ℕ) (hT : T = (integerParameters N).T)
  (ht : 0 < t) (htime : t ≤ (integerParameters N).S)
  (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (readGroup : GroupScalarKey M (inputSmallLog N) (inputSmallLog N ^ 80) → FiniteQuery σ)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (q : TargetInterval target.length) (sourceAnswer : σ → ℚ)
  (answer : PhysicalTableRequest M J target.length → ℚ)
  (hw : 0 ≤ answer (PhysicalTableRequest.warmup pass copy node 0 q))

include hN hell hM hP hA hT ht htime hw

 theorem computed_physicalRandom_current_reads :
    (physicalRandomDataRequestQuery source target N P (inputSmallLog N) (40 * smallLogExponent N)
      H (inputSmallLog N ^ 80) tau (refinementFactor A (inputSmallLog N)) eta kappa delta
      pass copy T S t ht node hbelow readGroup readInteger q).cost
      (Sum.elim sourceAnswer (fun key => answer key.val))
      (Sum.elim (fun _ => 0) (fun key => physicalCurrentReadWeight (T + t) key.val)) ≤
        2 * M * inputSmallLog N ^ 256 := by
  unfold physicalRandomDataRequestQuery
  refine (computed_localRandomDataQuery_table_cost source target _ N P H T t hN hell hM hP hT
    ht htime A tau eta kappa delta hA _ _ _ _ _ q _ _ _ _ 0 0 1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
  · intro r
    rw [FiniteQuery.mapKeys_cost]
    exact (physicalRefinementWarmupRead_cost_current pass copy T S t ht node q node le_rfl
      0 (Nat.zero_le T) r _).le
  · intro input
    rw [FiniteQuery.mapKeys_cost]
    simpa only [Nat.mul_zero, Function.comp_def, Sum.elim_inr] using
      (physicalRefinementMassQuery_cost_current pass copy T S t ht node hbelow q input _).le
  · intro input
    rw [FiniteQuery.mapKeys_cost]
    exact (physicalRefinementWarmupRead_cost_current pass copy T S t ht node q
      (physicalChild node hbelow input.1) _ 0 (Nat.zero_le T) input.2 _).le
  · intro key
    rw [FiniteQuery.mapKeys_cost]
    exact FiniteQuery.cost_zero _ _
  · intro key range
    rw [FiniteQuery.mapKeys_cost]
    exact FiniteQuery.cost_zero _ _
  · intro input
    rw [FiniteQuery.mapKeys_cost]
    exact (physicalRefinementEarlierQuery_cost_current pass copy T S t node hbelow q input _).le
  · intro input
    rw [FiniteQuery.mapKeys_cost]
    exact (physicalRefinementCurrentQuery_cost_current pass copy T S t node hbelow q input _).le
  · exact hw
  · simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add]
    exact le_rfl

end Physical

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedChargedRandomBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform edge budgets for the actual charged global interpreter.
The bounds hold for every initial seed and every draw, including failed
approximation events. -/

namespace EditApproximation

section Current

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    CellGroupDraws M (inputSmallLog N) (inputSmallLog N ^ 80))
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

variable
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    GroupScalarKey M (inputSmallLog N) (inputSmallLog N ^ 80) → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ)

local notation "values" => localRequestValue source target N P (inputSmallLog N)
  (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S copies factor multiplier
    tau eta kappa delta group integer initial

variable (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
  (hM : M = (integerParameters N).M)
  (hAmax : ∀ pass, factor pass ≤ ((integerParameters N).initialFactor : ℚ))
  (hP : P = (integerParameters N).P) (hT : T = (integerParameters N).T)
  (hS : S = (integerParameters N).S)

include hN hell hM hAmax hP hT hS in
 theorem computed_chargedRandomGlobalQuery_current_reads
    (request : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedRandomGlobalQuery source target N P (inputSmallLog N) (40 * smallLogExponent N)
      H (inputSmallLog N ^ 80) T S passes copies factor multiplier tau eta kappa delta
      readGroup readInteger initial request).cost
      (Sum.elim sourceAnswer (fun child => chargedRequestValue source target N P (inputSmallLog N) (40 * smallLogExponent N)
        H (inputSmallLog N ^ 80) T S passes copies factor multiplier tau eta kappa delta
        group integer initial child.val))
      (Sum.elim (fun _ => 0) (fun child => chargedSameWeight request child.val)) ≤ 2 * M * inputSmallLog N ^ 256 := by
  cases request with
  | inl entry => exact Nat.zero_le _
  | inr parent =>
    by_cases hi : parent.val.index ≤ T
    · unfold chargedRandomGlobalQuery
      dsimp only
      rw [ite_eq_left hi, FiniteQuery.mapKeys_cost]
      simp only [Function.comp_def, Sum.elim_inr]
      rw [chargedWarmupQuery_same_cost_zero]
      exact Nat.zero_le _
    · by_cases hb : parent.val.node.1.val < J
      · by_cases hs : (physicalSourceInterval source.length parent.val.node).hi -
            (physicalSourceInterval source.length parent.val.node).lo ≤ 1
        · unfold chargedRandomGlobalQuery
          dsimp only
          rw [ite_eq_right hi, ite_eq_left hb, ite_eq_left hs, FiniteQuery.mapKeys_cost]
          simp only [Function.comp_def, Sum.elim_inr]
          rw [chargedInitialQuery_same_cost_zero]
          exact Nat.zero_le _
        · have hanswer : chargedRequestValue source target N P (inputSmallLog N)
              (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
              tau eta kappa delta group integer initial =
              Sum.elim (fun entry => (initial entry : ℚ)) (fun r => values r.val) := by
            funext key
            cases key <;> rfl
          rw [hanswer]
          rw [chargedRandomGlobalQuery_current_cost source target N P (inputSmallLog N)
            (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
            tau eta kappa delta readGroup readInteger sourceAnswer values initial parent (by omega) hb hs]
          apply computed_physicalRandom_current_reads source target N P H hN hell hM hP
            (factor parent.val.pass) tau eta kappa delta (hAmax _) parent.val.pass parent.val.copy
            T S (parent.val.index - T) hT (by omega)
            (by have hi := parent.property.2.2; omega) parent.val.node hb
          rw [localRequestValue_initial]
          exact stageInitial_nonneg_all_seeds _ _ _ _ _ _ _ _
      · unfold chargedRandomGlobalQuery
        dsimp only
        rw [ite_eq_right hi, ite_eq_right hb, FiniteQuery.mapKeys_cost]
        simp only [Function.comp_def, Sum.elim_inr]
        rw [chargedInitialQuery_same_cost_zero]
        exact Nat.zero_le _


end Current

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedRandomExpansion
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Expansion

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    CellGroupDraws M (inputSmallLog N) (inputSmallLog N ^ 80))
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

variable
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    GroupScalarKey M (inputSmallLog N) (inputSmallLog N ^ 80) → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ)

local notation "mixedProgram" => chargedRandomGlobalQuery source target N P (inputSmallLog N)
  (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
  tau eta kappa delta readGroup readInteger initial
local notation "program" => SourceRanked.projectedBody ChargedPhysicalRequest.rank mixedProgram sourceAnswer
local notation "values" => chargedRequestValue source target N P (inputSmallLog N)
  (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
  tau eta kappa delta group integer initial
local notation "depth" => @ChargedPhysicalRequest.depth M J target.length passes copies T S
local notation "index" => @ChargedPhysicalRequest.index M J target.length passes copies T S

variable (hbody : ∀ (request : ChargedPhysicalRequest M J target.length passes copies T S),
  (chargedRandomGlobalQuery source target N P (inputSmallLog N)
    (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
    tau eta kappa delta readGroup readInteger initial request).value
    (Sum.elim sourceAnswer (fun child : {child : ChargedPhysicalRequest M J target.length passes copies T S //
      child.rank < request.rank} => chargedRequestValue source target N P (inputSmallLog N)
        (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
        tau eta kappa delta group integer initial child.val)) =
    chargedRequestValue source target N P (inputSmallLog N)
      (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
      tau eta kappa delta group integer initial request)

include hbody

variable (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
  (hM : M = (integerParameters N).M) (hP : P = (integerParameters N).P)
  (hT : T = (integerParameters N).T) (hS : S = (integerParameters N).S)
  (hcopies : copies ≤ inputHeight N ^ 2)
  (hAmin : ∀ pass, 1 ≤ factor pass)
  (hAmax : ∀ pass, factor pass ≤ ((integerParameters N).initialFactor : ℚ))

include hN hell hM hP hT hS hcopies hAmin hAmax in
 theorem chargedRandomDependencyTree_valid (root : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedRandomDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody root).Valid
      (M * inputSmallLog N ^ 257)
      (inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1))) := by
  apply queryDependencyExpansion_valid
  · intro key
    rw [querySameRequests_length_eq_cost depth index program values
      (SourceRanked.projectedBody_value ChargedPhysicalRequest.rank mixedProgram sourceAnswer values hbody)]
    change (FiniteQuery.eraseSources sourceAnswer (mixedProgram key)).cost
      (fun child => values child.val) (fun child => chargedSameWeight key child.val) ≤ _
    rw [FiniteQuery.eraseSources_cost]
    have h := computed_chargedRandomGlobalQuery_current_reads source target N P H T S passes copies
      factor multiplier tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hN hell hM hAmax hP hT hS key
    apply h.trans
    calc
      2 * M * inputSmallLog N ^ 256 ≤ inputSmallLog N * M * inputSmallLog N ^ 256 := by
        gcongr
        omega
      _ = M * inputSmallLog N ^ 257 := by ring
  · intro key
    rw [queryEarlierRequests_length_eq_cost depth index program values
      (SourceRanked.projectedBody_value ChargedPhysicalRequest.rank mixedProgram sourceAnswer values hbody)]
    change (FiniteQuery.eraseSources sourceAnswer (mixedProgram key)).cost
      (fun child => values child.val) (fun child => chargedEarlierWeight key child.val) ≤ _
    rw [FiniteQuery.eraseSources_cost]
    exact computed_chargedRandomGlobalQuery_earlier_reads source target N P H T S passes copies
      factor multiplier tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hN hell hM hAmax hP hT hS hcopies hAmin key


end Expansion

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Work

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (initial : PhysicalEntry M J target.length → ℕ) (hPpos : 0 < P)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies)

local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "group" => physicalFamilyGroup target N P ell exponent H (ell ^ 80) passes copies draw
local notation "integer" => physicalFamilyInteger source target N P ell exponent H (ell ^ 80)
  T S passes copies factor multiplier tau eta kappa delta hPpos draw initial
local notation "readGroup" => physicalFamilyGroupRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "readInteger" => physicalFamilyOnlineRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "answer" => physicalFamilyAnswer target N P ell exponent H (ell ^ 80) passes copies draw
local notation "bodyValue" => physicalFamilyProgram_value source target N P ell exponent H (ell ^ 80)
  T S passes copies factor multiplier tau eta kappa delta initial hPpos draw

 theorem physicalFamilyDependencyTree_valid_oai
    (hN : 0 < N) (hell : 200 ≤ ell) (hM : M = (integerParameters N).M)
    (hP : P = (integerParameters N).P) (hT : T = (integerParameters N).T)
    (hS : S = (integerParameters N).S) (hcopies : copies ≤ inputHeight N ^ 2)
    (hAmin : ∀ pass, 1 ≤ factor pass)
    (hAmax : ∀ pass, factor pass ≤ ((integerParameters N).initialFactor : ℚ))
    (root : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) :
    (physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta initial hPpos draw root).Valid
      (M * ell ^ 257) (inputHeight N ^ (512 * (coarseExponent ell + 1))) :=
  chargedRandomDependencyTree_valid source target N P H T S (passes + 1) copies factor multiplier
    tau eta kappa delta group integer initial readGroup readInteger answer bodyValue
    hN hell hM hP hT hS hcopies hAmin hAmax root

end Work

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.physicalFamilyDependencyTree_valid_oai.{u_1} := @OAI.EditApproximation.physicalFamilyDependencyTree_valid_oai.{u_1}
