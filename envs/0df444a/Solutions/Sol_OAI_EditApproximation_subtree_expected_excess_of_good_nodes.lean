-- Prove2me | solution 1 for OAI.EditApproximation.subtree_expected_excess_of_good_nodes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:47:28.814574+00:00
-- url     : https://prove2.me/submissions/7d8671f1-b9d4-4145-8b60-77e9584b6ccc

import Mathlib
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_physicalNode_generic_regret
import Theorems.Thm_OAI_EditApproximation_physicalRefinement_zero_cost
import Theorems.Thm_OAI_EditApproximation_stageComparison_positive_movement
import Theorems.Thm_OAI_EditApproximation_stageWarmupMass_child_lower
import Theorems.Thm_OAI_EditApproximation_stageWarmup_invariants
import Theorems.Thm_OAI_EditApproximation_stageWarmup_postfixed
import Theorems.Thm_OAI_EditApproximation_subtreeComparisonBadRegret_bound

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Connections
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Connection costs with arbitrary gaps and overlaps

This proves the edit-cost part of the connection inequality of Section 2
for actual substrings and edit scripts. Prefixes telescope across the
child intervals; common-prefix cancellation then removes the outside
prefix. The children need not have ordered or shared target endpoints.
-/

namespace EditApproximation

open EditDistortion

universe u

theorem edit_drop_insert_le {α : Type u} (p q : List α) (a : α) (k : ℕ) :
    edit ((p ++ q).drop k) ((p ++ a :: q).drop k) ≤ 1 := by
  by_cases hk : k ≤ p.length
  · simp only [List.drop_append_of_le_length hk]
    exact cost_le (Script.single (Step.insert (p.drop k) q a))
  · have hp : p.length ≤ k := by omega
    have hpos : 0 < k - p.length := by omega
    simp only [List.drop_append, List.drop_eq_nil_of_le hp, List.nil_append,
      List.drop_cons hpos]
    apply (edit_drop_indices_le q (k - p.length) (k - p.length - 1)).trans
    unfold Nat.dist
    omega

theorem edit_drop_step_le {α : Type u} {x y : List α} (h : Step true x y) (k : ℕ) :
    edit (x.drop k) (y.drop k) ≤ 1 := by
  cases h with
  | insert p q a => exact edit_drop_insert_le p q a k
  | delete p q a =>
    rw [show edit ((p ++ a :: q).drop k) ((p ++ q).drop k) =
      edit ((p ++ q).drop k) ((p ++ a :: q).drop k) from cost_symm _ _]
    exact edit_drop_insert_le p q a k
  | substitute _ p q a b =>
    by_cases hk : k ≤ p.length
    · simp only [List.drop_append_of_le_length hk]
      exact cost_le (Script.single (Step.substitute rfl (p.drop k) q a b))
    · have hp : p.length ≤ k := by omega
      have hpos : 0 < k - p.length := by omega
      simp only [List.drop_append, List.drop_eq_nil_of_le hp, List.nil_append,
        List.drop_cons hpos]
      have hrefl : edit (q.drop (k - p.length - 1)) (q.drop (k - p.length - 1)) = 0 :=
        cost_refl _
      rw [hrefl]
      omega

theorem edit_drop_script_le {α : Type u} {x y : List α} {n : ℕ}
    (h : Script true n x y) (k : ℕ) : edit (x.drop k) (y.drop k) ≤ n := by
  induction h with
  | nil x => exact (cost_refl (x.drop k)).le
  | @cons n x y z step rest ih =>
    have hstep := edit_drop_step_le step k
    exact (cost_triangle (s := true) (x.drop k) (y.drop k) (z.drop k)).trans
      (by change edit (x.drop k) (y.drop k) + edit (y.drop k) (z.drop k) ≤ n + 1; omega)

theorem edit_drop_nonexpansive {α : Type u} (x y : List α) (k : ℕ) :
    edit (x.drop k) (y.drop k) ≤ edit x y := by
  simpa only [cost, edit] using edit_drop_script_le (cost_spec (s := true) x y) k

theorem edit_append_right_le {α : Type u} (x y suffix : List α) :
    edit (x ++ suffix) (y ++ suffix) ≤ edit x y :=
  cost_le ((cost_spec (s := true) x y).append_right suffix)



theorem prefix_append_substring {α : Type u} (word : List α) {lo hi : ℕ}
    (horder : lo ≤ hi) : word.take lo ++ substring word lo hi = word.take hi := by
  have htake : (word.take hi).take lo = word.take lo := by
    simp only [List.take_take, Nat.min_eq_left horder]
  rw [substring, ← htake]
  exact List.take_append_drop lo (word.take hi)

theorem prefix_child_step {α : Type u} (word : List α) (start : ℕ)
    (state : TargetInterval word.length) :
    edit (word.take start ++ substring word state.lo state.hi) (word.take state.hi) ≤
      Nat.dist start state.lo := by
  rw [← prefix_append_substring word state.ordered]
  apply (edit_append_right_le _ _ _).trans
  simpa only [substring, List.drop_zero] using
    edit_substring_right_le word 0 start state.lo

theorem prefix_connection_bound {α : Type u} (word : List α)
    (states : List (TargetInterval word.length)) (start finish : ℕ) :
    edit (word.take start ++ targetConcatenation word states) (word.take finish) ≤
      connectionBudget start states finish := by
  induction states generalizing start with
  | nil =>
    simpa only [targetConcatenation, List.map_nil, List.flatten_nil, List.append_nil,
      connectionBudget, substring, List.drop_zero] using
      edit_substring_right_le word 0 start finish
  | cons state rest ih =>
    simp only [targetConcatenation, List.map_cons, List.flatten_cons]
    rw [← List.append_assoc]
    have hstep := (edit_append_right_le _ _ (targetConcatenation word rest)).trans
      (prefix_child_step word start state)
    have htri := cost_triangle (s := true)
      ((word.take start ++ substring word state.lo state.hi) ++ targetConcatenation word rest)
      (word.take state.hi ++ targetConcatenation word rest) (word.take finish)
    exact htri.trans (Nat.add_le_add hstep (ih state.hi))

/-- The target-only part of the connection inequality. The prefix proof
accounts for overlaps and backwards connecting jumps automatically. -/
theorem target_connection_bound {α : Type u} (word : List α)
    (states : List (TargetInterval word.length)) (parent : TargetInterval word.length) :
    edit (targetConcatenation word states) (substring word parent.lo parent.hi) ≤
      connectionBudget parent.lo states parent.hi := by
  have h := edit_drop_nonexpansive
    (word.take parent.lo ++ targetConcatenation word states)
    (word.take parent.hi) parent.lo
  have hlen : (word.take parent.lo).length = parent.lo := by
    simp only [List.length_take, Nat.min_eq_left (parent.ordered.trans parent.valid)]
  have hdrop : (word.take parent.lo ++ targetConcatenation word states).drop parent.lo =
      targetConcatenation word states := by
    simpa only [hlen] using List.drop_append_length
      (l₁ := word.take parent.lo) (l₂ := targetConcatenation word states)
  rw [hdrop] at h
  exact h.trans (prefix_connection_bound word states parent.lo parent.hi)

theorem edit_flatten_pairs_le {α : Type u} (pairs : List (List α × List α)) :
    edit (pairs.map Prod.fst).flatten (pairs.map Prod.snd).flatten ≤
      (pairs.map fun pair => edit pair.1 pair.2).sum := by
  induction pairs with
  | nil => exact (cost_refl ([] : List α)).le
  | cons pair rest ih =>
    simp only [List.map_cons, List.flatten_cons, List.sum_cons]
    exact (cost_append_le (s := true) pair.1 pair.2
      (rest.map Prod.fst).flatten (rest.map Prod.snd).flatten).trans
      (Nat.add_le_add_left ih _)

/-- Child editing plus endpoint connections bounds the parent cost, for
an actual concatenated partition of the source string. -/
theorem child_connection_bound {α : Type u} (word : List α)
    (children : List (List α × TargetInterval word.length))
    (parent : TargetInterval word.length) :
    edit (children.map Prod.fst).flatten (substring word parent.lo parent.hi) ≤
      (children.map fun child => edit child.1 (substring word child.2.lo child.2.hi)).sum +
        connectionBudget parent.lo (children.map Prod.snd) parent.hi := by
  have hchildren := edit_flatten_pairs_le
    (children.map fun child => (child.1, substring word child.2.lo child.2.hi))
  simp only [List.map_map, Function.comp_def] at hchildren
  have htarget := target_connection_bound word (children.map Prod.snd) parent
  have htri := cost_triangle (s := true) (children.map Prod.fst).flatten
    (targetConcatenation word (children.map Prod.snd)) (substring word parent.lo parent.hi)
  apply htri.trans
  exact Nat.add_le_add (by simpa only [targetConcatenation, List.map_map,
    Function.comp_def, cost, edit] using hchildren) htarget

theorem signedLengthGap_append {α : Type u} (x y u v : List α) :
    signedLengthGap (x ++ u) (y ++ v) = signedLengthGap x y + signedLengthGap u v := by
  simp only [signedLengthGap, List.length_append, Nat.cast_add]
  ring

theorem flattened_length_gap_le {α : Type u} (pairs : List (List α × List α)) :
    |signedLengthGap (pairs.map Prod.fst).flatten (pairs.map Prod.snd).flatten| ≤
      (pairs.map fun pair => |signedLengthGap pair.1 pair.2|).sum := by
  induction pairs with
  | nil => simp [signedLengthGap]
  | cons pair rest ih =>
    simp only [List.map_cons, List.flatten_cons, List.sum_cons, signedLengthGap_append]
    exact (abs_add_le _ _).trans (add_le_add le_rfl ih)

/-- Length gaps obey the same arbitrary-gap connection inequality as
the edit costs. This is the second lower invariant of the Bellman operator. -/
theorem child_shift_connection_bound {α : Type u} (word : List α)
    (children : List (List α × TargetInterval word.length))
    (parent : TargetInterval word.length) :
    |signedLengthGap (children.map Prod.fst).flatten (substring word parent.lo parent.hi)| ≤
      (children.map fun child =>
        |signedLengthGap child.1 (substring word child.2.lo child.2.hi)|).sum +
        (connectionBudget parent.lo (children.map Prod.snd) parent.hi : ℝ) := by
  let pairs := children.map fun child => (child.1, substring word child.2.lo child.2.hi)
  have hflatten := flattened_length_gap_le pairs
  have htarget := target_connection_bound word (children.map Prod.snd) parent
  have hgap := abs_length_gap_le_edit (targetConcatenation word (children.map Prod.snd))
    (substring word parent.lo parent.hi)
  have hbudget : |signedLengthGap (targetConcatenation word (children.map Prod.snd))
      (substring word parent.lo parent.hi)| ≤
        (connectionBudget parent.lo (children.map Prod.snd) parent.hi : ℝ) :=
    hgap.trans (by exact_mod_cast htarget)
  have hid : signedLengthGap (children.map Prod.fst).flatten
      (substring word parent.lo parent.hi) =
        signedLengthGap (pairs.map Prod.fst).flatten (pairs.map Prod.snd).flatten +
          signedLengthGap (targetConcatenation word (children.map Prod.snd))
            (substring word parent.lo parent.hi) := by
    simp only [pairs, List.map_map, Function.comp_def, targetConcatenation, signedLengthGap]
    ring
  rw [hid]
  apply (abs_add_le _ _).trans
  have hsum := add_le_add hflatten hbudget
  simpa only [pairs, List.map_map, Function.comp_def] using hsum

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_TreeAccounting
attribute [-instance] _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Finite comparison-tree accounting

A complete tree is indexed by its physical depth and child labels. Terminal
comparison costs may be carried forward, with zero costs in the other child
slots. The identities apply to that representation without any probability
or sampling hypothesis.
-/

namespace EditApproximation

open Finset

/-- Labeled nodes of a complete `M`-ary tree at one physical depth. -/




theorem tree_layer_sum {M d : ℕ} (weight : TreeLayer M (d + 1) → ℝ) :
    (∑ node : TreeLayer M d, ∑ child : Fin M, weight (node, child)) =
      ∑ node : TreeLayer M (d + 1), weight node := by
  exact (Fintype.sum_prod_type weight).symm

/-- Mass/energy differences cancel exactly between successive frontiers. -/
theorem tree_frontier_telescope (M J : ℕ)
    (weight : (d : ℕ) → TreeLayer M d → ℝ) :
    (∑ d ∈ range J, ∑ node : TreeLayer M d,
      (weight d node - ∑ child : Fin M, weight (d + 1) (node, child))) =
        weight 0 PUnit.unit - ∑ node : TreeLayer M J, weight J node := by
  have hstep (d : ℕ) : (∑ node : TreeLayer M d,
      (weight d node - ∑ child : Fin M, weight (d + 1) (node, child))) =
        (∑ node : TreeLayer M d, weight d node) -
          (∑ node : TreeLayer M (d + 1), weight (d + 1) node) := by
    rw [sum_sub_distrib, tree_layer_sum]
  simp_rw [hstep]
  induction J with
  | zero =>
    let : Unique (TreeLayer M 0) := ⟨⟨PUnit.unit⟩, fun a => by cases a; rfl⟩
    rw [sum_range_zero, Fintype.sum_unique]
    exact (sub_self _).symm
  | succ J ih =>
    rw [sum_range_succ, ih]
    ring

/-- The explicit small-growth bound used for the comparison frontiers. -/
theorem small_growth_pow {x : ℝ} (n : ℕ) (hx : 0 ≤ x)
    (hsmall : (n : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ n ≤ 1 + 2 * n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (n : ℝ) * x ≤ 1 / 2 := by
      push_cast at hsmall
      nlinarith
    have hprev := mul_le_mul_of_nonneg_right (ih hn) (by positivity : 0 ≤ 1 + x)
    rw [pow_succ]
    apply hprev.trans
    push_cast
    have hprod : 0 ≤ x * (1 - 2 * n * x) := by
      apply mul_nonneg hx
      nlinarith
    nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ActualActionValues
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Connection values at labeled physical children

Child table values retain their child labels even when two source
substrings coincide. The edit and shift lower bounds are proved for
the actual finite sum of these labeled values.
-/

namespace EditApproximation

open Finset EditDistortion



theorem actual_endpoint_action_lower {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (parent : TargetInterval source.length)
    (q : TargetInterval target.length) (states : Fin M → TargetInterval target.length)
    (a : ℝ) (ha : 1 ≤ a) (value : Fin M → TargetInterval target.length → ℝ)
    (hcost : ∀ i, (stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (states i) : ℝ) / a ≤
        value i (states i))
    (hgap : ∀ i, |stateLengthGap
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (states i)| ≤
        value i (states i)) :
    max ((stateEditCost (substring source parent.lo parent.hi) target q : ℝ) / a)
      |stateLengthGap (substring source parent.lo parent.hi) target q| ≤
        endpointActionValue q states value := by
  let piece := fun i : Fin M =>
    substring source (sourceChild parent i).lo (sourceChild parent i).hi
  let children := List.ofFn fun i : Fin M => (piece i, states i)
  have hsource : (List.ofFn piece).flatten = substring source parent.lo parent.hi :=
    sourceChild_partition source hM parent
  have htarget : (children.map Prod.snd) = List.ofFn states := by
    simp only [children, List.map_ofFn, Function.comp_def]
  have hchildSource : (children.map Prod.fst).flatten = substring source parent.lo parent.hi := by
    simpa only [children, List.map_ofFn, Function.comp_def] using hsource
  have hconnection := child_connection_bound target children q
  rw [hchildSource, htarget] at hconnection
  simp only [children, List.map_ofFn, List.sum_ofFn, Function.comp_def] at hconnection
  have hconnectionR : (stateEditCost (substring source parent.lo parent.hi) target q : ℝ) ≤
      (∑ i, (stateEditCost (piece i) target (states i) : ℝ)) + endpointActionConnection q states := by
    exact_mod_cast hconnection
  have hshift := child_shift_connection_bound target children q
  rw [hchildSource, htarget] at hshift
  simp only [children, List.map_ofFn, List.sum_ofFn, Function.comp_def] at hshift
  have hgapSum : (∑ i, |signedLengthGap (piece i)
      (substring target (states i).lo (states i).hi)|) ≤ ∑ i, value i (states i) := by
    apply sum_le_sum
    intro i hi
    rw [← stateLengthGap_actual]
    exact hgap i
  have hcostSum : (∑ i, (stateEditCost (piece i) target (states i) : ℝ)) / a ≤
      ∑ i, value i (states i) := by
    rw [sum_div]
    exact sum_le_sum (fun i _ => hcost i)
  have hconn0 : (0 : ℝ) ≤ endpointActionConnection q states := Nat.cast_nonneg _
  have ha0 : 0 < a := by linarith
  have hconnDiv : (endpointActionConnection q states : ℝ) / a ≤ endpointActionConnection q states := by
    apply (div_le_iff₀ ha0).2
    nlinarith
  apply max_le
  · have hdivide := div_le_div_of_nonneg_right hconnectionR ha0.le
    rw [add_div] at hdivide
    unfold endpointActionValue
    linarith
  · rw [stateLengthGap_actual]
    unfold endpointActionValue endpointActionConnection
    linarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BalancedWidths
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalSubtreeNode_zero _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.treeLayerCodeWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Width and node counts for the fixed interval tree

Repeated ceiling division gives the physical-depth width bound. This
includes empty children and repeated interval labels, which must still
be counted as distinct nodes in the lazy evaluation analysis.
-/

namespace EditApproximation

open Finset

theorem ceilDiv_comp (n a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (n ⌈/⌉ a) ⌈/⌉ b = n ⌈/⌉ (a * b) := by
  apply eq_of_forall_ge_iff
  intro k
  rw [ceilDiv_le_iff_le_mul hb, ceilDiv_le_iff_le_mul ha,
    ceilDiv_le_iff_le_mul (Nat.mul_pos ha hb), Nat.mul_assoc]

theorem balanced_child_width_le_ceiling (width M i : ℕ) (hM : 0 < M) :
    ((i + 1) * width / M) - i * width / M ≤ width ⌈/⌉ M := by
  let c := width ⌈/⌉ M
  have hceil : width ≤ M * c := (ceilDiv_le_iff_le_mul hM).mp (le_refl c)
  have hfloor := Nat.lt_mul_div_succ (i * width) hM
  have hsum : i * width + width < (i * width / M + c + 1) * M := by nlinarith
  have hdiv := (Nat.div_lt_iff_lt_mul hM).2 hsum
  have hid : (i + 1) * width = i * width + width := by ring
  rw [hid]
  omega

theorem sourceChild_width_le_ceiling {n M : ℕ} (parent : TargetInterval n) (child : Fin M) :
    (sourceChild parent child).hi - (sourceChild parent child).lo ≤
      (parent.hi - parent.lo) ⌈/⌉ M := by
  dsimp only [sourceChild, balancedCut]
  rw [Nat.add_sub_add_left]
  exact balanced_child_width_le_ceiling _ _ _ (Nat.zero_lt_of_lt child.isLt)

theorem sourceIntervalAt_width (M n d : ℕ) (hM : 0 < M) (node : TreeLayer M d) :
    (sourceIntervalAt M n d node).hi - (sourceIntervalAt M n d node).lo ≤ n ⌈/⌉ M ^ d := by
  induction d with
  | zero => simp [sourceIntervalAt]
  | succ d ih =>
    have hchild := sourceChild_width_le_ceiling (sourceIntervalAt M n d node.1) node.2
    have hmono := (gc_mul_ceilDiv hM).monotone_l (ih node.1)
    have hcomp := ceilDiv_comp n (M ^ d) M (pow_pos hM d) hM
    change (sourceChild (sourceIntervalAt M n d node.1) node.2).hi -
        (sourceChild (sourceIntervalAt M n d node.1) node.2).lo ≤ n ⌈/⌉ M ^ (d + 1)
    exact hchild.trans (hmono.trans_eq (by rw [hcomp, pow_succ]))

theorem sourceIntervalAt_leaf_width (M n J : ℕ) (hM : 0 < M) (hcapacity : n ≤ M ^ J)
    (node : TreeLayer M J) :
    (sourceIntervalAt M n J node).hi - (sourceIntervalAt M n J node).lo ≤ 1 := by
  apply (sourceIntervalAt_width M n J hM node).trans
  apply (ceilDiv_le_iff_le_mul (pow_pos hM J)).2
  simpa only [Nat.mul_one] using hcapacity

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Bellman
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite Bellman propagation and warmup

The action minimum is computed by a finite list with the initial cone as
fallback. Empty action families need no extended-real convention. The
warmup lemmas concern the actual repeated finite Bellman operator.
-/

namespace EditApproximation

open Finset

theorem le_finiteMinimum_iff (lower fallback : ℝ) (values : List ℝ) :
    lower ≤ finiteMinimum fallback values ↔ lower ≤ fallback ∧ ∀ v ∈ values, lower ≤ v := by
  induction values with
  | nil => simp [finiteMinimum]
  | cons v rest ih => simp only [finiteMinimum, le_min_iff, ih, List.mem_cons,
      forall_eq_or_imp]; tauto

theorem finiteMinimum_le_member (fallback : ℝ) (values : List ℝ)
    {value : ℝ} (hvalue : value ∈ values) : finiteMinimum fallback values ≤ value := by
  induction values with
  | nil => simp at hvalue
  | cons v rest ih =>
    rcases List.mem_cons.mp hvalue with rfl | hvalue
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hvalue)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ComparisonAccounting
attribute [-instance] _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Accuracy accounting on the comparison tree

The clipped regrets cancel across every physical frontier. Terminal nodes
can be carried forward in one child slot, with zero in the others, as in
the complete-tree representation used for the curvature accounting.
-/

namespace EditApproximation

open Finset

theorem tree_regret_telescope (M J : ℕ)
    (value charge : (d : ℕ) → TreeLayer M d → ℝ) :
    (∑ d ∈ range J, ∑ node : TreeLayer M d,
      (value d node - charge d node -
        ∑ child : Fin M, value (d + 1) (node, child))) =
      value 0 PUnit.unit - (∑ node : TreeLayer M J, value J node) -
        ∑ d ∈ range J, ∑ node : TreeLayer M d, charge d node := by
  have hpoint d (node : TreeLayer M d) :
      value d node - charge d node - (∑ child : Fin M, value (d + 1) (node, child)) =
        (value d node - ∑ child : Fin M, value (d + 1) (node, child)) - charge d node := by ring
  simp_rw [hpoint, sum_sub_distrib]
  have htelescope := tree_frontier_telescope M J value
  simp only [sum_sub_distrib] at htelescope
  rw [htelescope]

theorem tree_regret_time_bound (M J S : ℕ)
    (value : ℕ → (d : ℕ) → TreeLayer M d → ℝ)
    (charge : (d : ℕ) → TreeLayer M d → ℝ) (terminalBound : ℝ)
    (hmonotone : ∀ t < S, value S 0 PUnit.unit ≤ value (t + 1) 0 PUnit.unit)
    (hterminal : ∀ t < S, (∑ node : TreeLayer M J, value (t + 1) J node) ≤ terminalBound) :
    (S : ℝ) * value S 0 PUnit.unit ≤
      (S : ℝ) * (terminalBound + ∑ d ∈ range J, ∑ node : TreeLayer M d, charge d node) +
        ∑ t ∈ range S, ∑ d ∈ range J, ∑ node : TreeLayer M d,
          (value (t + 1) d node - charge d node -
            ∑ child : Fin M, value (t + 1) (d + 1) (node, child)) := by
  have hpoint (t : ℕ) (ht : t ∈ range S) : value S 0 PUnit.unit ≤
      terminalBound + (∑ d ∈ range J, ∑ node : TreeLayer M d, charge d node) +
        ∑ d ∈ range J, ∑ node : TreeLayer M d,
          (value (t + 1) d node - charge d node -
            ∑ child : Fin M, value (t + 1) (d + 1) (node, child)) := by
    rw [tree_regret_telescope]
    linarith [hmonotone t (mem_range.mp ht), hterminal t (mem_range.mp ht)]
  have hsum := sum_le_sum hpoint
  simpa only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_add] using hsum

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Regret
attribute [-instance] _root_.OAI.EditApproximation.physicalFamilyRange_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Clipped Bellman regret for edit-distance refinement

The deterministic bound of Lemma `lem:generic-regret` in
Section 7 of *An Almost-Linear Approximation Scheme for Edit Distance*
(manuscript of September 24, 2026) applies to an arbitrary finite set of
children satisfying the Bellman inequality and exact-cost connection
inequality.
-/

namespace EditApproximation

open Finset

/-- At a comparison node whose predicted normalized length gap is close
to one, almost all warmup mass is accounted for by the absolute gap. -/
theorem predicted_length_gap_bound (W Z gap τ : ℝ)
    (hZ : 0 < Z) (hZW : Z ≤ W) (hτ : 0 ≤ τ)
    (hprediction : 1 - τ < |gap| / Z) :
    W - |gap| ≤ (W - Z) + τ * W := by
  have hp : (1 - τ) * Z < |gap| := (lt_div_iff₀ hZ).mp hprediction
  have hmass : 0 ≤ τ * (W - Z) := mul_nonneg hτ (sub_nonneg.mpr hZW)
  nlinarith

/-- The refined generic bound at a node that is not bad and whose
normalized length-gap predictor lies near one. The parameter `q` is
`H^(-1/4)` in the manuscript. -/
theorem near_length_gap_regret_bound (W Z gap τ q F cost : ℝ)
    (hZ : 0 < Z) (hZW : Z ≤ W) (hτ : 0 ≤ τ)
    (hprediction : 1 - τ < |gap| / Z)
    (hdiscrepancy : W - Z ≤ q * cost)
    (hmass : W ≤ 4 * F * cost) :
    W - |gap| ≤ (q + 4 * τ * F) * cost := by
  have hpred := predicted_length_gap_bound W Z gap τ hZ hZW hτ hprediction
  have hscale := mul_le_mul_of_nonneg_left hmass hτ
  nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ComparisonTree
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalSubtreeNode_zero _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.treeLayerCodeWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The input-determined rounded comparison tree

The choices here are only for the proof. They use the exact input edit
costs and a fixed classical choice of optimal alignment, and have no
sampling argument. Stopped states are carried in child zero, with the
remaining physical slots empty.
-/

namespace EditApproximation

open Finset

theorem comparisonChildren_cost_bound {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (hc : 0 < stateEditCost (substring source parent.lo parent.hi) target q) :
    (∑ i, (stateEditCost (substring source (sourceChild parent i).lo (sourceChild parent i).hi)
      target (comparisonChildren source target hM P hP parent q hc i) : ℝ)) ≤
        (1 + 4 * (M : ℝ) / P) * stateEditCost (substring source parent.lo parent.hi) target q :=
  (Classical.choose_spec (rounded_comparison_action source target hM parent q
    (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)) P hP
    (cost_dyadicScale _ _ hc le_rfl).2.1 (cost_dyadicScale _ _ hc le_rfl).2.2)).2.2.2.2

theorem comparisonStateCost_nonneg {α : Type*} (source target : List α)
    (node : ComparisonState source.length target.length) :
    0 ≤ comparisonStateCost source target node := by
  cases node with
  | none => exact le_rfl
  | some state => exact Nat.cast_nonneg _

theorem comparisonStep_cost_bound {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (node : ComparisonState source.length target.length) :
    (∑ i, comparisonStateCost source target (comparisonStep source target hM P hP node i)) ≤
      (1 + 4 * (M : ℝ) / P) * comparisonStateCost source target node := by
  classical
  cases node with
  | none => simp only [comparisonStep, comparisonStateCost, sum_const_zero, mul_zero, le_refl]
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hs : comparisonStopped source target parent q
    · simp only [comparisonStep, dite_eq_left hs]
      have hsum : (∑ i : Fin M, comparisonStateCost source target
          (if i = ⟨0, hM⟩ then some (parent, q) else none)) =
          comparisonStateCost source target (some (parent, q)) := by
        have hpoint (i : Fin M) : comparisonStateCost source target
            (if i = ⟨0, hM⟩ then some (parent, q) else none) =
            if i = ⟨0, hM⟩ then comparisonStateCost source target (some (parent, q)) else 0 := by
          split_ifs <;> rfl
        simp_rw [hpoint]
        simp
      rw [hsum]
      have hnonneg := comparisonStateCost_nonneg source target (some (parent, q))
      have hf : 0 ≤ 4 * (M : ℝ) / P := by positivity
      nlinarith
    · simpa only [comparisonStep, dite_eq_right hs, comparisonStateCost] using
        comparisonChildren_cost_bound source target hM P hP parent q
          (by unfold comparisonStopped at hs; omega)

theorem comparison_frontier_cost_bound {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (root : ComparisonState source.length target.length) (d : ℕ) :
    (∑ node : TreeLayer M d, comparisonStateCost source target
      (comparisonFrontier source target hM P hP root d node)) ≤
        (1 + 4 * (M : ℝ) / P) ^ d * comparisonStateCost source target root := by
  induction d with
  | zero =>
    change (∑ _ : PUnit, comparisonStateCost source target root) ≤ _
    simp
  | succ d ih =>
    rw [← tree_layer_sum]
    have hsum := sum_le_sum (fun node (_ : node ∈ (univ : Finset (TreeLayer M d))) =>
      comparisonStep_cost_bound source target hM P hP
        (comparisonFrontier source target hM P hP root d node))
    have hf : 0 ≤ 1 + 4 * (M : ℝ) / P := by positivity
    calc
      _ ≤ ∑ node : TreeLayer M d, (1 + 4 * (M : ℝ) / P) *
          comparisonStateCost source target
            (comparisonFrontier source target hM P hP root d node) := hsum
      _ = (1 + 4 * (M : ℝ) / P) * ∑ node : TreeLayer M d,
          comparisonStateCost source target
            (comparisonFrontier source target hM P hP root d node) := by rw [mul_sum]
      _ ≤ (1 + 4 * (M : ℝ) / P) *
          ((1 + 4 * (M : ℝ) / P) ^ d * comparisonStateCost source target root) :=
            mul_le_mul_of_nonneg_left ih hf
      _ = _ := by rw [pow_succ]; ring

theorem comparison_frontier_cost_le_twice {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (root : ComparisonState source.length target.length) (J d : ℕ) (hd : d ≤ J)
    (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) :
    (∑ node : TreeLayer M d, comparisonStateCost source target
      (comparisonFrontier source target hM P hP root d node)) ≤
        2 * comparisonStateCost source target root := by
  have hx : 0 ≤ 4 * (M : ℝ) / P := by positivity
  have hdR : (d : ℝ) ≤ J := by exact_mod_cast hd
  have hdx : (d : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right hdR hx).trans hsmall
  have hpow := small_growth_pow d hx hdx
  have htwo : (1 + 4 * (M : ℝ) / P) ^ d ≤ 2 := by linarith
  exact (comparison_frontier_cost_bound source target hM P hP root d).trans
    (mul_le_mul_of_nonneg_right htwo (comparisonStateCost_nonneg source target root))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ComparisonBounds
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual terminal, nonterminal-cost and endpoint-movement bounds. -/

namespace EditApproximation

open Finset

theorem comparisonActiveCost_bounds {α : Type*} (source target : List α)
    (node : ComparisonState source.length target.length) :
    0 ≤ comparisonActiveCost source target node ∧
      comparisonActiveCost source target node ≤ comparisonStateCost source target node := by
  classical
  cases node with
  | none => exact ⟨le_rfl, le_rfl⟩
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hs : comparisonStopped source target parent q
    · simp only [comparisonActiveCost, ite_eq_left hs, comparisonStateCost]
      exact ⟨le_rfl, Nat.cast_nonneg _⟩
    · simp only [comparisonActiveCost, ite_eq_right hs, comparisonStateCost]
      exact ⟨Nat.cast_nonneg _, le_rfl⟩

theorem comparisonMovement_bound {α : Type*} (source target : List α)
    (P : ℕ) (hP : 0 < P) (node : ComparisonState source.length target.length) :
    comparisonMovement source target P node * P ≤ 2 * comparisonActiveCost source target node := by
  classical
  cases node with
  | none => simp only [comparisonMovement, comparisonActiveCost, zero_mul, mul_zero, le_refl]
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hs : comparisonStopped source target parent q
    · simp only [comparisonMovement, comparisonActiveCost, ite_eq_left hs, zero_mul, mul_zero, le_refl]
    · have hc : 0 < stateEditCost (substring source parent.lo parent.hi) target q := by
        unfold comparisonStopped at hs
        omega
      have hb := (cost_dyadicScale _ _ hc le_rfl).2.1
      have herror := rounded_seedGrid_error
        (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)) P hP q
      have herrorR : (targetEndpointDistance q (roundInterval (seedGridSpacing
          (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)) P) q) : ℝ) * P ≤
          2 * (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q) : ℕ) := by
        exact_mod_cast herror
      have hbR : ((2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q) : ℕ) : ℝ) ≤
          stateEditCost (substring source parent.lo parent.hi) target q := by exact_mod_cast hb
      simp only [comparisonMovement, comparisonActiveCost, ite_eq_right hs]
      linarith

theorem comparison_total_active_cost_bound {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (root : ComparisonState source.length target.length) (J : ℕ)
    (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) :
    (∑ d ∈ range J, ∑ node : TreeLayer M d, comparisonActiveCost source target
      (comparisonFrontier source target hM P hP root d node)) ≤
        2 * J * comparisonStateCost source target root := by
  have hlevel (d : ℕ) (hd : d ∈ range J) :
      (∑ node : TreeLayer M d, comparisonActiveCost source target
        (comparisonFrontier source target hM P hP root d node)) ≤
          2 * comparisonStateCost source target root := by
    exact (sum_le_sum (fun node _ => (comparisonActiveCost_bounds source target _).2)).trans
      (comparison_frontier_cost_le_twice source target hM P hP root J d (mem_range.mp hd).le hsmall)
  have hsum := sum_le_sum hlevel
  simpa only [sum_const, card_range, nsmul_eq_mul, mul_assoc, mul_left_comm] using hsum

theorem comparison_total_movement_bound {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (root : ComparisonState source.length target.length) (J : ℕ)
    (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) :
    (∑ d ∈ range J, ∑ node : TreeLayer M d, comparisonMovement source target P
      (comparisonFrontier source target hM P hP root d node)) ≤
        4 * J * comparisonStateCost source target root / P := by
  have hPpos : 0 < P := by omega
  have hPr : (0 : ℝ) < P := by exact_mod_cast hPpos
  have hsum := sum_le_sum (fun d (_ : d ∈ range J) => sum_le_sum
    (fun node (_ : node ∈ (univ : Finset (TreeLayer M d))) =>
      comparisonMovement_bound source target P hPpos
        (comparisonFrontier source target hM P hP root d node)))
  simp only [← sum_mul, ← mul_sum] at hsum
  have hcost := comparison_total_active_cost_bound source target hM P hP root J hsmall
  apply (le_div_iff₀ hPr).2
  linarith

theorem comparison_frontier_cost_slack {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (root : ComparisonState source.length target.length) (J : ℕ)
    (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) :
    (∑ node : TreeLayer M J, comparisonStateCost source target
      (comparisonFrontier source target hM P hP root J node)) ≤
        (1 + 8 * (M : ℝ) * J / P) * comparisonStateCost source target root := by
  have hx : 0 ≤ 4 * (M : ℝ) / P := by positivity
  have hpow := small_growth_pow J hx hsmall
  have heq : 1 + 2 * (J : ℝ) * (4 * (M : ℝ) / P) = 1 + 8 * (M : ℝ) * J / P := by ring
  rw [heq] at hpow
  exact (comparison_frontier_cost_bound source target hM P hP root J).trans
    (mul_le_mul_of_nonneg_right hpow (comparisonStateCost_nonneg source target root))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ComparisonPhysical
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Active comparison states have precisely the corresponding physical source interval. -/

namespace EditApproximation

theorem comparisonStep_active_parent {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (node : ComparisonState source.length target.length) (i : Fin M)
    (resultParent : TargetInterval source.length) (resultQ : TargetInterval target.length)
    (heq : comparisonStep source target hM P hP node i = some (resultParent, resultQ))
    (hactive : ¬ comparisonStopped source target resultParent resultQ) :
    ∃ parent q, node = some (parent, q) ∧ ¬ comparisonStopped source target parent q ∧
      resultParent = sourceChild parent i := by
  classical
  cases node with
  | none => cases heq
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hs : comparisonStopped source target parent q
    · simp only [comparisonStep, dite_eq_left hs] at heq
      split_ifs at heq with hi
      · have hpq := Option.some.inj heq
        have hp : parent = resultParent := congrArg Prod.fst hpq
        have hq : q = resultQ := congrArg Prod.snd hpq
        exact False.elim (hactive (by rw [← hp, ← hq]; exact hs))
    · simp only [comparisonStep, dite_eq_right hs] at heq
      have hpq := Option.some.inj heq
      have hp : sourceChild parent i = resultParent := congrArg Prod.fst hpq
      exact ⟨parent, q, rfl, hs, hp.symm⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ComparisonLift
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual physical tables on the stopped comparison tree. Stopped states retain
their exact cost while the complete-tree representation carries them forward.
-/

namespace EditApproximation

open Finset

theorem stoppedComparisonValue_physical {α : Type*} {M J : ℕ} (source target : List α)
    (table : PhysicalEntry M J target.length → ℝ)
    (hterminal : ∀ node q, comparisonStopped source target (physicalSourceInterval source.length node) q →
      table (node, q) = stateEditCost (physicalSource source node) target q)
    (node : PhysicalNode M J) (q : TargetInterval target.length) :
    stoppedComparisonValue source target (fun r => table (node, r))
      (some (physicalSourceInterval source.length node, q)) = table (node, q) := by
  classical
  unfold stoppedComparisonValue
  dsimp only
  split_ifs with hstop
  · exact (hterminal node q hstop).symm
  · rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PrefixComparison
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual comparison prefixes in the finite wide action family

The cut is the start of the remaining comparator suffix, or the parent's
end when that suffix is empty. Splitting at this cut preserves the literal
connection budget. Splicing any enumerated prefix to the comparator suffix
remains an enumerated wide action.
-/

namespace EditApproximation

open Finset

theorem wideActionMinimum_le_member {nx ny M b P : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (hnonempty : wideActionList M parent r b P ≠ [])
    (child : Fin M → TargetInterval ny → ℝ) (action : Fin M → TargetInterval ny)
    (haction : action ∈ wideActionList M parent r b P) :
    wideActionMinimum parent r b P hnonempty child ≤ endpointActionValue r action child :=
  finiteMinimum_le_member _ _ (List.mem_map.mpr ⟨action, haction, rfl⟩)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RepresentativeBands
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The actual rational wide minimum, computed velocity and representative band. -/

namespace EditApproximation

open Finset



theorem rationalEndpointActionValue_cast {ny M : ℕ} (r : TargetInterval ny)
    (states : Fin M → TargetInterval ny) (child : Fin M → TargetInterval ny → ℚ) :
    (rationalEndpointActionValue r states child : ℝ) =
      endpointActionValue r states (fun i s => (child i s : ℝ)) := by
  simp only [rationalEndpointActionValue, endpointActionValue, Rat.cast_add,
    Rat.cast_natCast, Rat.cast_sum]



theorem rationalWideActionMinimum_cast {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (hnonempty : wideActionList M parent r b P ≠ [])
    (child : Fin M → TargetInterval ny → ℚ) :
    (rationalWideActionMinimum parent r b P hnonempty child : ℝ) =
      wideActionMinimum parent r b P hnonempty (fun i s => (child i s : ℝ)) := by
  rw [rationalWideActionMinimum, rationalMinimum_cast]
  simp only [wideActionMinimum, rationalEndpointActionValue_cast, List.map_map, Function.comp_def]

theorem wideActionMinimum_lower {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (parent : TargetInterval source.length)
    (r : TargetInterval target.length) (b P : ℕ)
    (hnonempty : wideActionList M parent r b P ≠ []) (a : ℝ) (ha : 1 ≤ a)
    (child : Fin M → TargetInterval target.length → ℝ)
    (hchild : ∀ i s, max ((stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s : ℝ) / a)
        |stateLengthGap (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s| ≤
          child i s) :
    max ((stateEditCost (substring source parent.lo parent.hi) target r : ℝ) / a)
      |stateLengthGap (substring source parent.lo parent.hi) target r| ≤
        wideActionMinimum parent r b P hnonempty child := by
  have hlower (states : Fin M → TargetInterval target.length) :
      max ((stateEditCost (substring source parent.lo parent.hi) target r : ℝ) / a)
        |stateLengthGap (substring source parent.lo parent.hi) target r| ≤ endpointActionValue r states child :=
    actual_endpoint_action_lower source target hM parent r states a ha child
      (fun i => (le_max_left _ _).trans (hchild i (states i)))
      (fun i => (le_max_right _ _).trans (hchild i (states i)))
  apply (le_finiteMinimum_iff _ _ _).2
  refine ⟨hlower _, ?_⟩
  intro value hvalue
  obtain ⟨states, hs, rfl⟩ := List.mem_map.mp hvalue
  exact hlower states



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_RationalWideStep
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! One literal refinement update with finite selected-group cones and online action values. -/

namespace EditApproximation

open Finset

theorem rationalMinimum_map_mono {ι : Type*} (indices : List ι)
    (fallback fallback' : ℚ) (value value' : ι → ℚ)
    (hfallback : fallback ≤ fallback') (hvalue : ∀ i ∈ indices, value i ≤ value' i) :
    rationalMinimum fallback (indices.map value) ≤ rationalMinimum fallback' (indices.map value') := by
  induction indices with
  | nil => exact hfallback
  | cons i rest ih =>
    exact min_le_min (hvalue i (by simp)) (ih fun j hj => hvalue j (by simp [hj]))

theorem rationalBellman_mono {Parent Child : Type*} {M : ℕ}
    (fallback : Parent → ℚ) (distance : Parent → Parent → ℚ) (L : ℚ)
    (actions : List (RationalBellmanAction Parent Child M)) {child child' : Child → ℚ}
    (hchild : child ≤ child') (q : Parent) :
    rationalBellman fallback distance L actions child q ≤ rationalBellman fallback distance L actions child' q := by
  apply rationalMinimum_map_mono _ _ _ _ _ le_rfl
  intro action _
  exact add_le_add le_rfl (sum_le_sum fun i _ => hchild (action.childState i))

theorem rationalBellman_le_action {Parent Child : Type*} {M : ℕ}
    (fallback : Parent → ℚ) (distance : Parent → Parent → ℚ) (L : ℚ)
    (actions : List (RationalBellmanAction Parent Child M)) (child : Child → ℚ)
    (q : Parent) (action : RationalBellmanAction Parent Child M) (haction : action ∈ actions) :
    rationalBellman fallback distance L actions child q ≤ rationalActionValue distance L child q action :=
  rationalMinimum_le_member _ _ (List.mem_map.mpr ⟨action, haction, rfl⟩)



theorem rationalOnlineMinimum_lower (lower : ℚ) (values : List ℚ)
    (hvalues : ∀ v ∈ values, lower ≤ v) {online : ℚ}
    (honline : rationalOnlineMinimum values = some online) : lower ≤ online := by
  cases values with
  | nil => cases honline
  | cons first rest =>
    have heq : rationalMinimum first rest = online := Option.some.inj honline
    rw [← heq]
    exact (le_rationalMinimum_iff _ _ _).2
      ⟨hvalues first (by simp), fun v hv => hvalues v (by simp [hv])⟩

/-- Both lower candidates are genuine current-child wide Bellman cones.
The sampled choices enter only through literal membership in the wide list. -/
theorem rationalWideStep_bellman_sandwich {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ)
    (initial : TargetInterval ny → ℚ) (L delta : ℚ)
    (old current : Fin M × TargetInterval ny → ℚ) (hmono : current ≤ old)
    (groups online : List (RationalBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (hgroups : ∀ action ∈ groups, action ∈ rationalActualWideActions parent representatives P)
    (honline : ∀ action ∈ online, action ∈ rationalActualWideActions parent representatives P)
    (q : TargetInterval ny) :
    rationalBellman initial (fun q r => targetEndpointDistance q r) L
        (rationalActualWideActions parent representatives P) current q ≤
      rationalWideStep parent representatives P initial L delta old current groups online q ∧
    rationalWideStep parent representatives P initial L delta old current groups online q ≤
      rationalBellman initial (fun q r => targetEndpointDistance q r) L
        (rationalActualWideActions parent representatives P) old q := by
  let actions := rationalActualWideActions (M := M) parent representatives P
  let distance := fun q r : TargetInterval ny => (targetEndpointDistance q r : ℚ)
  let lower := rationalBellman initial distance L actions current q
  let upper := rationalBellman initial distance L actions old q
  let cone := rationalWideStepCone parent representatives P initial L old current groups q
  have hcone : lower ≤ cone := by
    apply (le_rationalMinimum_iff _ _ _).2
    refine ⟨rationalBellman_mono initial distance L actions hmono q, ?_⟩
    intro value hvalue
    obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hvalue
    exact rationalBellman_le_action initial distance L actions current q action (hgroups action ha)
  have hupper : cone ≤ upper := rationalMinimum_le_fallback _ _
  have honlineLower : ∀ value ∈ online.map (rationalActionValue distance L current q), lower ≤ value := by
    intro value hvalue
    obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hvalue
    exact rationalBellman_le_action initial distance L actions current q action (honline action ha)
  change lower ≤ rationalRefinementUpdate delta cone
      (rationalOnlineMinimum (online.map (rationalActionValue distance L current q))) ∧
    rationalRefinementUpdate delta cone
      (rationalOnlineMinimum (online.map (rationalActionValue distance L current q))) ≤ upper
  cases hmin : rationalOnlineMinimum (online.map (rationalActionValue distance L current q)) with
  | none => exact ⟨hcone, hupper⟩
  | some value =>
    have hlower := rationalOnlineMinimum_lower lower _ honlineLower hmin
    exact ⟨le_min hcone (hlower.trans (le_max_right _ _)), (min_le_left _ _).trans hupper⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLeaves
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact source leaves remain exact throughout the actual physical warmup. -/

namespace EditApproximation

open Finset

theorem physicalSource_length_eq {α : Type*} {M J : ℕ} (source : List α)
    (node : PhysicalNode M J) : (physicalSource source node).length =
      (physicalSourceInterval source.length node).hi - (physicalSourceInterval source.length node).lo := by
  simp only [physicalSource, substring, List.length_drop, List.length_take,
    Nat.min_eq_left (physicalSourceInterval source.length node).valid]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRefinement
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
The complete physical refinement recurrence. Current-index recursive requests
go only to physical children. The selection interface records literal wide
list membership, and carries no approximation or probability assumption.
-/

namespace EditApproximation





theorem physicalRefinement_at_leaf {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J)
    (hleaf : (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1) (t : ℕ) (q : TargetInterval target.length) :
    physicalRefinement source target U N P F A T delta choices node t q =
      stateEditCost (physicalSource source node) target q := by
  rw [physicalRefinement]
  have hlength : (physicalSource source node).length ≤ 1 := (physicalSource_length_eq source node).trans_le hleaf
  split_ifs <;>
    simp only [stageInitial, physicalInitialTable, ite_eq_left hlength,
      shortSourceCost_eq_edit _ _ hlength] <;> rfl

theorem physicalRefinement_succ {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (hleaf : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1) (t : ℕ) (q : TargetInterval target.length) :
    let children : PhysicalChildTables M target.length := fun i =>
      physicalRefinement source target U N P F A T delta choices (physicalChild node hbelow i)
    physicalRefinement source target U N P F A T delta choices node (t + 1) q =
      rationalWideStep (physicalSourceInterval source.length node)
        (stageRepresentatives source target U N P F A node) P
        (fun r => stageInitial source target U N P F A (node, r)) (128 * F) delta
        (fun is => children is.1 t is.2) (fun is => children is.1 (t + 1) is.2)
        (choices.groups node children (t + 1)) (choices.online node children (t + 1) q) q := by
  rw [physicalRefinement]
  rw [dite_eq_left hbelow, ite_eq_right hleaf]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRefinementInvariants
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deterministic Bellman invariants of the complete physical recurrence. -/

namespace EditApproximation

theorem stageWarmup_at_terminal {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (t : ℕ) (node : PhysicalNode M J)
    (hterminal : ¬ node.1.val < J ∨ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1) (q : TargetInterval target.length) :
    stageWarmup source target U N P F A t (node, q) =
      stageInitial source target U N P F A (node, q) := by
  cases t with
  | zero => rfl
  | succ t =>
    change rationalPhysicalBellman source target P (128 * F) _ _ _ (node, q) = _
    unfold rationalPhysicalBellman
    dsimp only
    rcases hterminal with hlast | hleaf
    · rw [dite_eq_right hlast]
    · split_ifs <;> rfl

theorem physicalRefinement_at_terminal {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J)
    (hterminal : ¬ node.1.val < J ∨ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1) (t : ℕ) (q : TargetInterval target.length) :
    physicalRefinement source target U N P F A T delta choices node t q =
      stageInitial source target U N P F A (node, q) := by
  rw [physicalRefinement]
  rcases hterminal with hlast | hleaf
  · rw [dite_eq_right hlast]
  · split_ifs <;> rfl

theorem physicalRefinement_zero {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J) (q : TargetInterval target.length) :
    physicalRefinement source target U N P F A T delta choices node 0 q =
      stageWarmup source target U N P F A T (node, q) := by
  by_cases hbelow : node.1.val < J
  · by_cases hleaf : (physicalSourceInterval source.length node).hi -
        (physicalSourceInterval source.length node).lo ≤ 1
    · rw [physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inr hleaf),
        stageWarmup_at_terminal _ _ _ _ _ _ _ _ node (Or.inr hleaf)]
    · rw [physicalRefinement, dite_eq_left hbelow, ite_eq_right hleaf]
  · rw [physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inl hbelow),
      stageWarmup_at_terminal _ _ _ _ _ _ _ _ node (Or.inl hbelow)]

/-- The full recurrence is postfixed for the current-child Bellman operator,
and each next value is at most the previous-child Bellman value. Selected
actions require only their literal wide-list membership certificates. -/
theorem physicalRefinement_bellman_invariants {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (node : PhysicalNode M J) :
    let value := fun t (s : PhysicalEntry M J target.length) =>
      physicalRefinement source target U N P F A T delta choices s.1 t s.2
    let bellman := rationalPhysicalBellman source target P (128 * F)
      (stageInitial source target U N P F A) (stageRepresentatives source target U N P F A)
    ∀ t q, bellman (value t) (node, q) ≤ value t (node, q) ∧
      value (t + 1) (node, q) ≤ bellman (value t) (node, q) := by
  dsimp only
  by_cases hbelow : node.1.val < J
  · by_cases hleaf : (physicalSourceInterval source.length node).hi -
        (physicalSourceInterval source.length node).lo ≤ 1
    · intro t q
      rw [physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inr hleaf),
        physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inr hleaf)]
      simp only [rationalPhysicalBellman, dite_eq_left hbelow, ite_eq_left hleaf]
      exact ⟨le_rfl, le_rfl⟩
    · let children : PhysicalChildTables M target.length := fun i =>
        physicalRefinement source target U N P F A T delta choices (physicalChild node hbelow i)
      have hchildren : ∀ t, (fun is : Fin M × TargetInterval target.length =>
          children is.1 (t + 1) is.2) ≤ fun is => children is.1 t is.2 := by
        intro t is
        have ih := physicalRefinement_bellman_invariants source target U N P F A T delta choices
          (physicalChild node hbelow is.1) t is.2
        exact ih.2.trans ih.1
      have hsandwich (t : ℕ) (q : TargetInterval target.length) :=
        rationalWideStep_bellman_sandwich (physicalSourceInterval source.length node)
          (stageRepresentatives source target U N P F A node) P
          (fun r => stageInitial source target U N P F A (node, r)) (128 * F) delta
          (fun is => children is.1 t is.2) (fun is => children is.1 (t + 1) is.2)
          (hchildren t) (choices.groups node children (t + 1)) (choices.online node children (t + 1) q)
          (choices.groups_mem node children (t + 1)) (choices.online_mem node children (t + 1) q) q
      intro t q
      constructor
      · cases t with
        | zero =>
          simp_rw [physicalRefinement_zero]
          exact stageWarmup_postfixed source target U N P F A T (node, q)
        | succ t =>
          rw [physicalRefinement_succ _ _ _ _ _ _ _ _ _ _ node hbelow hleaf]
          simpa only [rationalPhysicalBellman, dite_eq_left hbelow, ite_eq_right hleaf]
            using (hsandwich t q).1
      · rw [physicalRefinement_succ _ _ _ _ _ _ _ _ _ _ node hbelow hleaf]
        simpa only [rationalPhysicalBellman, dite_eq_left hbelow, ite_eq_right hleaf]
          using (hsandwich t q).2
  · intro t q
    rw [physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inl hbelow),
      physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inl hbelow)]
    simp only [rationalPhysicalBellman, dite_eq_right hbelow]
    exact ⟨le_rfl, le_rfl⟩
termination_by J - node.1.val
decreasing_by
  unfold physicalChild
  dsimp only
  omega

theorem physicalRefinement_nonincreasing {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (node : PhysicalNode M J)
    (t : ℕ) (q : TargetInterval target.length) :
    physicalRefinement source target U N P F A T delta choices node (t + 1) q ≤
      physicalRefinement source target U N P F A T delta choices node t q := by
  have h := physicalRefinement_bellman_invariants source target U N P F A T delta choices node t q
  exact h.2.trans h.1

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalGenericRegret
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The generic regret bound for the actual complete physical recurrence. -/

namespace EditApproximation

open Finset

section Node

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A))
  (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (hleaf : ¬ (physicalSourceInterval source.length node).hi -
    (physicalSourceInterval source.length node).lo ≤ 1)
  (q : TargetInterval target.length)
  (hc : 0 < stateEditCost (physicalSource source node) target q)

local notation "parent" => physicalSourceInterval source.length node
local notation "b" => 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
local notation "r" => roundInterval (seedGridSpacing b P) q
local notation "action" => comparisonChildren source target hM P hP parent q hc
local notation "mass" => fun i s => (stageWarmupMass source target U N P F A T (physicalChild node hbelow i, s) : ℝ)
local notation "W" => comparisonActionMass action mass
local notation "value" => fun t (s : PhysicalEntry M J target.length) =>
  (physicalRefinement source target U N P F A T delta choices (Prod.fst s) t (Prod.snd s) : ℝ)
local notation "regret" => fun t =>
  max (stateEditCost (physicalSource source node) target q : ℝ) (value (t + 1) (node, q)) -
    (128 * (F : ℝ)) * targetEndpointDistance q r -
    physicalComparisonClipped source target U N P F A T delta choices node hbelow action (t + 1)

include hsize hF hA hseed hT in
 theorem physicalComparison_mass_upper (hMP : 4 * (M : ℝ) / P ≤ 1) :
    W ≤ 4 * F * stateEditCost (physicalSource source node) target q := by
  have hcost := comparisonChildren_cost_bound source target hM P hP parent q hc
  change (∑ i, (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (action i) : ℝ)) ≤
    (1 + 4 * (M : ℝ) / P) * stateEditCost (physicalSource source node) target q at hcost
  have hsum : W ≤ 2 * (F : ℝ) * ∑ i,
      (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (action i) : ℝ) := by
    change (∑ i, mass i (action i)) ≤ _
    rw [mul_sum]
    apply sum_le_sum
    intro i _
    have h := stageWarmup_invariants source target hM U N P F A hsize hP hF hA hseed T hT
      (physicalChild node hbelow i, action i)
    have hQ := h.2.2.1.trans h.2.2.2
    simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using (Rat.cast_le (K := ℝ)).mpr hQ
  have hfactor := mul_le_mul_of_nonneg_left hcost (show (0 : ℝ) ≤ 2 * F by positivity)
  have hcost0 : (0 : ℝ) ≤ stateEditCost (physicalSource source node) target q := Nat.cast_nonneg _
  have hfactor2 := mul_le_mul_of_nonneg_right hMP hcost0
  have hfactor3 := mul_le_mul_of_nonneg_left hfactor2 (show (0 : ℝ) ≤ 2 * F by positivity)
  nlinarith only [hsum, hfactor, hfactor3]

include hsize hF hA hseed hT hleaf in
 theorem physicalNode_near_length_gap_regret
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hMP : 4 * (M : ℝ) / P ≤ 1)
    (hnonempty : wideActionList M parent r b P ≠ []) (tau : ℚ) (htau : 0 ≤ tau)
    (hprediction : 1 - tau < |rationalStateGap (physicalSource source node) target r /
      rationalWideActionMinimum parent r b P hnonempty
        (physicalBandChildMassTable source target U N P F A T node hbelow)|)
    (ratio : ℝ)
    (hdiscrepancy : W - wideActionMinimum parent r b P hnonempty mass ≤
      ratio * stateEditCost (physicalSource source node) target q) (S : ℕ) :
    (∑ t ∈ range S, regret t) ≤
      (ratio + 4 * (tau : ℝ) * F) * stateEditCost (physicalSource source node) target q := by
  let Z := wideActionMinimum parent r b P hnonempty mass
  have hspec := comparisonChildren_spec source target hM P hP parent q hc
  have ha : (1 : ℝ) ≤ refinementFactor A F := by
    simpa only [Rat.cast_one] using (Rat.cast_le (K := ℝ)).mpr (refinementFactor_spec A F (by omega)).1
  have hlower := wideActionMinimum_lower source target hM parent r b P hnonempty
    (refinementFactor A F : ℝ) ha mass
    (stageWarmupMass_child_lower source target hM U N P F A hsize hP hF hA hseed T hT node hbelow)
  have hpositive := (stageComparison_positive_movement source target hM U N P F A hsize hP hF hA hseed
    T hT node q hc hscale).1
  have hcostPos : (0 : ℝ) < stateEditCost (physicalSource source node) target r := by exact_mod_cast hpositive
  have hZ : 0 < Z := (div_pos hcostPos (by linarith only [ha])).trans_le ((le_max_left _ _).trans hlower)
  have hZW : Z ≤ W := by
    have h := wideActionMinimum_le_member parent r hnonempty mass action hspec.1
    have hzero : endpointActionConnection r action = 0 := hspec.2.1
    simpa only [Z, endpointActionValue, hzero, Nat.cast_zero, zero_add, comparisonActionMass] using h
  have hpred : 1 - (tau : ℝ) < |stateLengthGap (physicalSource source node) target r| / Z := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hprediction
    simp only [Rat.cast_sub, Rat.cast_one, Rat.cast_abs, Rat.cast_div, rationalStateGap_cast,
      rationalWideActionMinimum_cast, abs_div] at h
    change 1 - (tau : ℝ) < |stateLengthGap (physicalSource source node) target r| / |Z| at h
    rwa [abs_of_pos hZ] at h
  have hnear := near_length_gap_regret_bound W Z (stateLengthGap (physicalSource source node) target r)
    (tau : ℝ) ratio F (stateEditCost (physicalSource source node) target q) hZ hZW
    ((Rat.cast_nonneg (K := ℝ)).mpr htau) hpred hdiscrepancy
    (physicalComparison_mass_upper source target hM U N P F A hsize hP hF hA hseed T hT node hbelow q hc hMP)
  exact (physicalNode_generic_regret source target hM U N P F A hsize hP hF hA hseed T hT delta choices
    node hbelow hleaf q hc S).trans hnear

end Node

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_StageTerminal
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Warmup masses and refinement values equal the true cost at stopped states. -/

namespace EditApproximation

theorem physicalRefinement_at_stopped {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (hM : 0 < M) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (hT : 0 < T) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (node : PhysicalNode M J)
    (t : ℕ) (q : TargetInterval target.length)
    (hstop : comparisonStopped source target (physicalSourceInterval source.length node) q) :
    physicalRefinement source target U N P F A T delta choices node t q =
      stateEditCost (physicalSource source node) target q := by
  rcases hstop with hleaf | hcost
  · exact physicalRefinement_at_leaf source target U N P F A T delta choices node hleaf t q
  · rw [physicalRefinement_zero_cost source target hM U N P F A hsize hP hF hA hseed
      T hT delta choices node t q hcost]
    rw [show stateEditCost (physicalSource source node) target q = 0 from hcost, Nat.cast_zero]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSubtree
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparison paths below an arbitrary physical node retain their original
global table labels. No refinement program or random law is changed. -/

namespace EditApproximation

theorem physicalSubtreeNode_child {M J : ℕ} (root : PhysicalNode M J)
    (d : ℕ) (path : TreeLayer M d) (hd : root.1.val + d < J) (i : Fin M) :
    physicalChild (physicalSubtreeNode root d path hd.le) hd i =
      physicalSubtreeNode root (d + 1) (path, i) (by omega) := rfl

theorem comparisonSubtree_active_source {α : Type*} (source target : List α)
    {M J : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (root : PhysicalNode M J) (rootQ : TargetInterval target.length)
    (d : ℕ) (path : TreeLayer M d) (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (heq : comparisonFrontier source target hM P hP
      (some (physicalSourceInterval source.length root, rootQ)) d path = some (parent, q))
    (hactive : ¬ comparisonStopped source target parent q) :
    parent = sourceIntervalAt M source.length (root.1.val + d) (treeLayerAppend root.2 d path) := by
  induction d generalizing parent q with
  | zero =>
    exact (congrArg Prod.fst (Option.some.inj heq)).symm
  | succ d ih =>
    obtain ⟨previousParent, previousQ, hprevious, hpreviousActive, hchild⟩ :=
      comparisonStep_active_parent source target hM P hP _ path.2 parent q heq hactive
    rw [ih path.1 previousParent previousQ hprevious hpreviousActive] at hchild
    exact hchild

theorem comparisonSubtreeLift_root {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P) (table : PhysicalEntry M J target.length → ℝ)
    (hterminal : ∀ node q, comparisonStopped source target (physicalSourceInterval source.length node) q →
      table (node, q) = stateEditCost (physicalSource source node) target q)
    (root : PhysicalNode M J) (rootQ : TargetInterval target.length) :
    comparisonSubtreeLift source target hM P hP table root rootQ 0 PUnit.unit = table (root, rootQ) := by
  classical
  unfold comparisonSubtreeLift
  rw [dite_eq_left (by omega : root.1.val + 0 ≤ J), physicalSubtreeNode_zero]
  exact stoppedComparisonValue_physical source target table hterminal root rootQ

theorem comparisonSubtreeLift_step_active {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P) (table : PhysicalEntry M J target.length → ℝ)
    (hterminal : ∀ node q, comparisonStopped source target (physicalSourceInterval source.length node) q →
      table (node, q) = stateEditCost (physicalSource source node) target q)
    (root : PhysicalNode M J) (rootQ : TargetInterval target.length)
    (d : ℕ) (path : TreeLayer M d) (hd : root.1.val + d < J) (q : TargetInterval target.length)
    (hfrontier : comparisonFrontier source target hM P hP
      (some (physicalSourceInterval source.length root, rootQ)) d path =
        some (physicalSourceInterval source.length (physicalSubtreeNode root d path hd.le), q))
    (hactive : ¬ comparisonStopped source target
      (physicalSourceInterval source.length (physicalSubtreeNode root d path hd.le)) q) (i : Fin M) :
    let node := physicalSubtreeNode root d path hd.le
    let hc : 0 < stateEditCost (physicalSource source node) target q := by
      change 0 < stateEditCost (substring source (physicalSourceInterval source.length node).lo
        (physicalSourceInterval source.length node).hi) target q
      dsimp only [node]
      unfold comparisonStopped at hactive
      omega
    comparisonSubtreeLift source target hM P hP table root rootQ (d + 1) (path, i) =
      table (physicalChild node hd i,
        comparisonChildren source target hM P hP (physicalSourceInterval source.length node) q hc i) := by
  classical
  dsimp only
  unfold comparisonSubtreeLift
  rw [dite_eq_left (by omega : root.1.val + (d + 1) ≤ J)]
  change stoppedComparisonValue source target _
    (comparisonStep source target hM P hP
      (comparisonFrontier source target hM P hP _ d path) i) = _
  rw [hfrontier]
  simp only [comparisonStep, dite_eq_right hactive]
  rw [← physicalSubtreeNode_child root d path hd i]
  exact stoppedComparisonValue_physical source target table hterminal _ _

theorem comparisonSubtreeLift_terminal {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P) (table : PhysicalEntry M J target.length → ℝ)
    (root : PhysicalNode M J) (rootQ : TargetInterval target.length) (K : ℕ)
    (hheight : root.1.val + K = J) (hcapacity : source.length ≤ M ^ J) (path : TreeLayer M K) :
    comparisonSubtreeLift source target hM P hP table root rootQ K path =
      comparisonStateCost source target (comparisonFrontier source target hM P hP
        (some (physicalSourceInterval source.length root, rootQ)) K path) := by
  classical
  unfold comparisonSubtreeLift
  generalize heq : comparisonFrontier source target hM P hP
    (some (physicalSourceInterval source.length root, rootQ)) K path = state
  cases state with
  | none => rfl
  | some state =>
    rcases state with ⟨parent, q⟩
    have hstop : comparisonStopped source target parent q := by
      by_contra hactive
      have hp := comparisonSubtree_active_source source target hM P hP root rootQ K path parent q heq hactive
      have hcapacity' : source.length ≤ M ^ (root.1.val + K) := by rw [hheight]; exact hcapacity
      have hwidth := sourceIntervalAt_leaf_width M source.length (root.1.val + K) hM hcapacity'
        (treeLayerAppend root.2 K path)
      rw [← hp] at hwidth
      exact hactive (Or.inl hwidth)
    simp only [stoppedComparisonValue, ite_eq_left hstop, comparisonStateCost]

theorem comparisonSubtreeLift_mono {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (table table' : PhysicalEntry M J target.length → ℝ) (hle : table ≤ table')
    (root : PhysicalNode M J) (rootQ : TargetInterval target.length) (d : ℕ) (path : TreeLayer M d) :
    comparisonSubtreeLift source target hM P hP table root rootQ d path ≤
      comparisonSubtreeLift source target hM P hP table' root rootQ d path := by
  classical
  unfold comparisonSubtreeLift stoppedComparisonValue
  generalize comparisonFrontier source target hM P hP
    (some (physicalSourceInterval source.length root, rootQ)) d path = state
  cases state with
  | none => exact le_rfl
  | some state =>
    rcases state with ⟨parent, q⟩
    dsimp only
    split_ifs
    · exact le_rfl
    · exact hle _
    · exact le_rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSubtreeRegret
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.physicalMedianUpdateTable_value _root_.OAI.EditApproximation.physicalNodeCodeWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.treeLayerCodeWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual clipped refinement telescope below any original physical label. -/

namespace EditApproximation

open Finset

section Refinement

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A)) (root : PhysicalNode M J) (rootQ : TargetInterval target.length)

local notation "lifted" => subtreeClippedLift source target hM U N P F A hP T delta choices root rootQ
local notation "frontier" => comparisonFrontier source target hM P hP
  (some (physicalSourceInterval source.length root, rootQ))

 theorem subtreeClippedLift_antitone (d : ℕ) (path : TreeLayer M d) : Antitone (fun t => lifted t d path) := by
  apply antitone_nat_of_succ_le
  intro t
  apply comparisonSubtreeLift_mono
  intro state
  apply max_le_max_left
  exact Rat.cast_le.mpr (physicalRefinement_nonincreasing source target U N P F A T delta choices state.1 t state.2)

include hsize hF hA hseed hT in
 theorem subtreeClippedLift_root (t : ℕ) : lifted t 0 PUnit.unit =
    max (stateEditCost (physicalSource source root) target rootQ : ℝ)
      (physicalRefinement source target U N P F A T delta choices
        root t rootQ : ℝ) := by
  have h := comparisonSubtreeLift_root source target hM P hP
    (physicalClippedTable source target U N P F A T delta choices t)
    (fun node q hstop => by
      have heq := physicalRefinement_at_stopped source target hM U N P F A hsize hP hF hA hseed
        T hT delta choices node t q hstop
      simp only [physicalClippedTable, heq, Rat.cast_natCast, max_self]) root rootQ
  simpa only [subtreeClippedLift, physicalClippedTable] using h

 theorem subtreeClippedLift_terminal (t K : ℕ) (hheight : root.1.val + K = J) (hcapacity : source.length ≤ M ^ J) (path : TreeLayer M K) :
    lifted t K path = comparisonStateCost source target (frontier K path) :=
  comparisonSubtreeLift_terminal source target hM P hP _ root rootQ K hheight hcapacity path

include hsize hF hA hseed hT in
 theorem subtree_regret_time (K : ℕ) (hheight : root.1.val + K = J) (S : ℕ) (hcapacity : source.length ≤ M ^ J)
    (hsmall : (K : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) :
    (S : ℝ) * max (stateEditCost (physicalSource source root) target rootQ : ℝ)
      (physicalRefinement source target U N P F A T delta choices
        root S rootQ : ℝ) ≤
      (S : ℝ) * ((1 + (8 * (M : ℝ) + 512 * F) * K / P) * stateEditCost (physicalSource source root) target rootQ) +
        ∑ t ∈ range S, ∑ d ∈ range K, ∑ path : TreeLayer M d,
          (lifted (t + 1) d path - (128 * (F : ℝ)) * comparisonMovement source target P (frontier d path) -
            ∑ i : Fin M, lifted (t + 1) (d + 1) (path, i)) := by
  let D : ℝ := stateEditCost (physicalSource source root) target rootQ
  let charge := fun d (path : TreeLayer M d) => (128 * (F : ℝ)) * comparisonMovement source target P (frontier d path)
  let terminal := (1 + 8 * (M : ℝ) * K / P) * D
  have hrootCost : comparisonStateCost source target
      (some (physicalSourceInterval source.length root, rootQ)) = D := by
    rfl
  have hterminal (t : ℕ) (_ht : t < S) : (∑ path : TreeLayer M K, lifted (t + 1) K path) ≤ terminal := by
    simp_rw [subtreeClippedLift_terminal source target hM U N P F A hP T delta choices root rootQ (t + 1) K hheight hcapacity]
    have h := comparison_frontier_cost_slack source target hM P hP
      (some (physicalSourceInterval source.length root, rootQ)) K hsmall
    rw [hrootCost] at h
    exact h
  have htime := tree_regret_time_bound M K S lifted charge terminal
    (fun t ht => subtreeClippedLift_antitone source target hM U N P F A hP T delta choices root rootQ
      0 PUnit.unit (by omega)) hterminal
  rw [subtreeClippedLift_root source target hM U N P F A hsize hP hF hA hseed T hT delta choices root rootQ S] at htime
  have hmovement := comparison_total_movement_bound source target hM P hP
    (some (physicalSourceInterval source.length root, rootQ)) K hsmall
  rw [hrootCost] at hmovement
  have hcharge : (∑ d ∈ range K, ∑ path : TreeLayer M d, charge d path) ≤ 512 * F * K * D / P := by
    dsimp only [charge]
    simp only [← mul_sum]
    have h := mul_le_mul_of_nonneg_left hmovement
      (show (0 : ℝ) ≤ 128 * F from mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hterm : terminal + (∑ d ∈ range K, ∑ path : TreeLayer M d, charge d path) ≤
      (1 + (8 * (M : ℝ) + 512 * F) * K / P) * D := by
    calc
      _ ≤ terminal + 512 * F * K * D / P := add_le_add_right hcharge terminal
      _ = _ := by dsimp only [terminal] <;> ring
  exact htime.trans (add_le_add_left (mul_le_mul_of_nonneg_left hterm (Nat.cast_nonneg S)) _)

end Refinement

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSubtreeExpectation
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite expectation of the actual clipped refinement telescope. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

section Expectation

variable {α Ω : Type*} [DecidableEq α] [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {M J : ℕ} (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : Ω → PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A)) (root : PhysicalNode M J) (K : ℕ) (hheight : root.1.val + K = J) (rootQ : TargetInterval target.length)
  (μ : Measure Ω) [IsProbabilityMeasure μ]

local notation "D" => (stateEditCost (physicalSource source root) target rootQ : ℝ)
local notation "lifted" => fun ω => subtreeClippedLift source target hM U N P F A hP T delta (choices ω) root rootQ
local notation "frontier" => comparisonFrontier source target hM P hP
  (some (physicalSourceInterval source.length root, rootQ))

include hsize hF hA hseed hT hheight in
 theorem subtree_expected_excess (S : ℕ) (hS : 0 < S)
    (hcapacity : source.length ≤ M ^ J) (hsmall : (K : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2)
    (budget : (d : ℕ) → TreeLayer M d → ℝ)
    (hnode : ∀ d < K, ∀ path : TreeLayer M d,
      (∫ ω, (∑ t ∈ range S,
        (lifted ω (t + 1) d path - (128 * (F : ℝ)) * comparisonMovement source target P (frontier d path) -
          ∑ i : Fin M, lifted ω (t + 1) (d + 1) (path, i))) ∂μ) ≤ budget d path) :
    (∫ ω, max ((physicalRefinement source target U N P F A T delta (choices ω) root S rootQ : ℝ) - D) 0 ∂μ) ≤
      ((8 * (M : ℝ) + 512 * F) * K / P) * D +
        (∑ d ∈ range K, ∑ path : TreeLayer M d, budget d path) / S := by
  let charge := fun d (path : TreeLayer M d) => (128 * (F : ℝ)) * comparisonMovement source target P (frontier d path)
  let regret := fun ω t d (path : TreeLayer M d) =>
    lifted ω (t + 1) d path - charge d path - ∑ i : Fin M, lifted ω (t + 1) (d + 1) (path, i)
  let coefficient : ℝ := (8 * (M : ℝ) + 512 * F) * K / P
  have hpoint (ω : Ω) := subtree_regret_time source target hM U N P F A hsize hP hF hA hseed
    T hT delta (choices ω) root rootQ K hheight S hcapacity hsmall
  have hmean := integral_mono (μ := μ) (.of_finite) (.of_finite) hpoint
  have hregret : (∫ ω, (∑ t ∈ range S, ∑ d ∈ range K, ∑ path : TreeLayer M d, regret ω t d path) ∂μ) ≤
      ∑ d ∈ range K, ∑ path : TreeLayer M d, budget d path := by
    have hswap (ω : Ω) : (∑ t ∈ range S, ∑ d ∈ range K, ∑ path : TreeLayer M d, regret ω t d path) =
        ∑ d ∈ range K, ∑ path : TreeLayer M d, ∑ t ∈ range S, regret ω t d path := by
      rw [sum_comm]
      apply sum_congr rfl
      intro d _
      rw [sum_comm]
    simp_rw [hswap]
    rw [integral_finsetSum _ (by intro d hd; exact .of_finite)]
    apply sum_le_sum
    intro d hd
    rw [integral_finsetSum _ (by intro path hp; exact .of_finite)]
    exact sum_le_sum fun path _ => hnode d (mem_range.mp hd) path
  have hroot : (∫ ω, max D
      (physicalRefinement source target U N P F A T delta (choices ω) root S rootQ : ℝ) ∂μ) =
      (∫ ω, max ((physicalRefinement source target U N P F A T delta (choices ω) root S rootQ : ℝ) - D) 0 ∂μ) + D := by
    have heq (ω : Ω) : max D
        (physicalRefinement source target U N P F A T delta (choices ω) root S rootQ : ℝ) =
        max ((physicalRefinement source target U N P F A T delta (choices ω) root S rootQ : ℝ) - D) 0 + D := by
      rw [← max_add_add_right, sub_add_cancel, zero_add, max_comm]
    simp_rw [heq]
    rw [integral_add (.of_finite) (integrable_const _), integral_const, probReal_univ, one_smul]
  change (∫ ω, (S : ℝ) * max D
      (physicalRefinement source target U N P F A T delta (choices ω) root S rootQ : ℝ) ∂μ) ≤
    (∫ ω, (S : ℝ) * ((1 + coefficient) * D) +
      (∑ t ∈ range S, ∑ d ∈ range K, ∑ path : TreeLayer M d, regret ω t d path) ∂μ) at hmean
  rw [integral_const_mul, integral_add (integrable_const _) (.of_finite),
    integral_const, probReal_univ, one_smul, hroot] at hmean
  have hSR : (0 : ℝ) < S := by exact_mod_cast hS
  apply (sub_le_iff_le_add').mp
  apply (le_div_iff₀ hSR).2
  nlinarith only [hmean, hregret]

end Expectation

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_StageComparisonCharges
attribute [-instance] _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Curvature and discrepancy are computed from the actual comparison-tree warmup masses. -/

namespace EditApproximation

open Finset

section Stage

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (rootQ : TargetInterval target.length)

theorem treeLayer_sigma_sum (M J : ℕ) (f : (d : ℕ) → TreeLayer M d → ℝ) :
    (∑ v : (Σ d : Fin J, TreeLayer M d.val), f v.1.val v.2) =
      ∑ d ∈ range J, ∑ path : TreeLayer M d, f d path := by
  rw [Fintype.sum_sigma]
  exact Fin.sum_univ_eq_sum_range (fun d => ∑ path : TreeLayer M d, f d path) J

end Stage

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalTreeGeneric
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generic cumulative regret at actual comparison-tree slots, including stopped slots. -/

namespace EditApproximation

open Finset

section Tree

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A)) (rootQ : TargetInterval target.length)

include hM hsize hP hF hA hseed hT in
 theorem physicalClippedTable_at_stopped (node : PhysicalNode M J) (q : TargetInterval target.length)
    (hstop : comparisonStopped source target (physicalSourceInterval source.length node) q) (t : ℕ) :
    physicalClippedTable source target U N P F A T delta choices t (node, q) =
      stateEditCost (physicalSource source node) target q := by
  have h := physicalRefinement_at_stopped source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices node t q hstop
  simp only [physicalClippedTable, h, Rat.cast_natCast, max_self]

end Tree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSubtreeGeneric
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generic cumulative regret at actual comparison-tree slots, including stopped slots. -/

namespace EditApproximation

open Finset

section Tree

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A)) (root : PhysicalNode M J) (K : ℕ) (hheight : root.1.val + K = J) (rootQ : TargetInterval target.length)

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (physicalSourceInterval source.length root, rootQ))
local notation "lifted" => subtreeClippedLift source target hM U N P F A hP T delta choices root rootQ

 theorem subtreeComparisonTreeRegret_none (t : ℕ) (d : Fin K) (path : TreeLayer M d.val)
    (heq : frontier d.val path = none) :
    subtreeComparisonTreeRegret source target hM U N P F A hP T delta choices root K rootQ t d path = 0 := by
  have hnext (i : Fin M) : frontier (d.val + 1) (path, i) = none := by
    change comparisonStep source target hM P hP (frontier d.val path) i = none
    rw [heq]
    rfl
  simp only [subtreeComparisonTreeRegret, subtreeClippedLift, comparisonSubtreeLift, heq, hnext,
    stoppedComparisonValue, comparisonMovement, mul_zero, sub_self, sum_const_zero]

 theorem subtreeComparisonTreeRegret_stopped (t : ℕ) (d : Fin K) (path : TreeLayer M d.val)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (heq : frontier d.val path = some (parent, q)) (hstop : comparisonStopped source target parent q) :
    subtreeComparisonTreeRegret source target hM U N P F A hP T delta choices root K rootQ t d path = 0 := by
  classical
  have hpoint (i : Fin M) : lifted (t + 1) (d.val + 1) (path, i) =
      if i = ⟨0, hM⟩ then (stateEditCost (substring source parent.lo parent.hi) target q : ℝ) else 0 := by
    unfold subtreeClippedLift comparisonSubtreeLift
    change stoppedComparisonValue source target _
      (comparisonStep source target hM P hP (frontier d.val path) i) = _
    rw [heq]
    simp only [comparisonStep, dite_eq_left hstop]
    split_ifs <;> simp only [stoppedComparisonValue, ite_eq_left hstop]
  unfold subtreeComparisonTreeRegret
  simp_rw [hpoint]
  simp only [subtreeClippedLift, comparisonSubtreeLift, heq, stoppedComparisonValue, ite_eq_left hstop,
    comparisonMovement, mul_zero, sub_zero, sum_ite_eq', mem_univ, ite_true, if_true, sub_self]

include hsize hF hA hseed hT in
 theorem subtreeComparisonTreeRegret_active (t : ℕ) (d : Fin K) (path : TreeLayer M d.val)
    (q : TargetInterval target.length)
    (heq : frontier d.val path = some
      (physicalSourceInterval source.length (physicalSubtreeNode root d.val path (by omega)), q))
    (hactive : ¬ comparisonStopped source target
      (physicalSourceInterval source.length (physicalSubtreeNode root d.val path (by omega))) q) :
    let node := physicalSubtreeNode root d.val path (by omega)
    let hbelow : node.1.val < J := by dsimp only [node, physicalSubtreeNode]; omega
    let hc : 0 < stateEditCost (physicalSource source node) target q := by
      change 0 < stateEditCost (substring source (physicalSourceInterval source.length node).lo
        (physicalSourceInterval source.length node).hi) target q
      dsimp only [node]
      unfold comparisonStopped at hactive
      omega
    let r := roundInterval (seedGridSpacing (2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)) P) q
    subtreeComparisonTreeRegret source target hM U N P F A hP T delta choices root K rootQ t d path =
      max (stateEditCost (physicalSource source node) target q : ℝ)
        (physicalRefinement source target U N P F A T delta choices node (t + 1) q : ℝ) -
          (128 * (F : ℝ)) * targetEndpointDistance q r -
          physicalComparisonClipped source target U N P F A T delta choices node hbelow
            (comparisonChildren source target hM P hP (physicalSourceInterval source.length node) q hc) (t + 1) := by
  classical
  dsimp only
  have hnext (i : Fin M) := comparisonSubtreeLift_step_active source target hM P hP
    (physicalClippedTable source target U N P F A T delta choices (t + 1))
    (fun label s hstop => physicalClippedTable_at_stopped source target hM U N P F A hsize hP hF hA hseed
      T hT delta choices label s hstop (t + 1)) root rootQ d.val path (by omega) q heq hactive i
  have hcurrent : comparisonSubtreeLift source target hM P hP
      (physicalClippedTable source target U N P F A T delta choices (t + 1)) root rootQ d.val path =
      physicalClippedTable source target U N P F A T delta choices (t + 1)
        (physicalSubtreeNode root d.val path (by omega), q) := by
    unfold comparisonSubtreeLift
    rw [heq]
    simp only [stoppedComparisonValue, ite_eq_right hactive]
    rw [dite_eq_left (by omega : root.1.val + d.val ≤ J)]
  have hmovement : comparisonMovement source target P (frontier d.val path) =
      targetEndpointDistance q (roundInterval (seedGridSpacing
        (2 ^ Nat.log 2 (stateEditCost (physicalSource source (physicalSubtreeNode root d.val path (by omega))) target q)) P) q) := by
    rw [heq]
    simp only [comparisonMovement, ite_eq_right hactive]
    rfl
  unfold subtreeComparisonTreeRegret subtreeClippedLift
  rw [hcurrent, hmovement]
  simp_rw [hnext]
  rfl

end Tree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_StageComparisonPrediction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual comparison charges and rational velocity predictor at a physical slot. -/

namespace EditApproximation

open Finset

theorem nonbad_charge_bounds (scale ratio K G : ℝ) (hratio : 0 < ratio)
    (hnotbad : ¬ (scale < ratio * K ∨ scale < ratio * G)) :
    K ≤ scale / ratio ∧ G ≤ scale / ratio := by
  have h := not_or.mp hnotbad
  constructor
  · apply (le_div_iff₀ hratio).2
    simpa only [mul_comm] using le_of_not_gt h.1
  · apply (le_div_iff₀ hratio).2
    simpa only [mul_comm] using le_of_not_gt h.2

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSubtreePrediction
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual comparison charges and rational velocity predictor at a physical slot. -/

namespace EditApproximation

open Finset

section Stage

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hP : 66 ≤ P) (T : ℕ) (root : PhysicalNode M J) (K : ℕ)
  (hheight : root.1.val + K = J) (rootQ : TargetInterval target.length)

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (physicalSourceInterval source.length root, rootQ))

 theorem subtreeComparisonPrediction_active (d : Fin K) (path : TreeLayer M d.val)
    (q : TargetInterval target.length)
    (heq : frontier d.val path = some (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path), q))
    (hactive : ¬ comparisonStopped source target (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)) q)
    (hn : wideActionList M (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path))
      (roundInterval (seedGridSpacing (2 ^ Nat.log 2 (stateEditCost
        (substring source (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).lo
          (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).hi) target q)) P) q)
      (2 ^ Nat.log 2 (stateEditCost (substring source (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).lo
        (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).hi) target q)) P ≠ []) :
    subtreeComparisonPrediction source target hM U N P F A hP T root K hheight rootQ d path =
      rationalStateGap (substring source (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).lo
        (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).hi) target
        (roundInterval (seedGridSpacing (2 ^ Nat.log 2 (stateEditCost
          (substring source (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).lo
            (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).hi) target q)) P) q) /
      rationalWideActionMinimum (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path))
        (roundInterval (seedGridSpacing (2 ^ Nat.log 2 (stateEditCost
          (substring source (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).lo
            (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).hi) target q)) P) q)
        (2 ^ Nat.log 2 (stateEditCost (substring source (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).lo
          (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).hi) target q)) P hn
        (physicalBandChildMassTable source target U N P F A T
          (physicalSubtreeNode root d.val path (by omega) : PhysicalNode M J) (by dsimp only [physicalSubtreeNode]; omega)) := by
  unfold subtreeComparisonPrediction
  rw [heq]
  simp only [dite_eq_right hactive]

 theorem subtreeComparisonCharges_active (d : Fin K) (path : TreeLayer M d.val)
    (q : TargetInterval target.length)
    (heq : frontier d.val path = some (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path), q))
    (hactive : ¬ comparisonStopped source target (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)) q)
    (hc : 0 < stateEditCost (substring source (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).lo
      (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).hi) target q)
    (hn : wideActionList M (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path))
      (roundInterval (seedGridSpacing (2 ^ Nat.log 2 (stateEditCost
        (substring source (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).lo
          (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).hi) target q)) P) q)
      (2 ^ Nat.log 2 (stateEditCost (substring source (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).lo
        (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).hi) target q)) P ≠ []) :
    let parent := sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)
    let node : PhysicalNode M J := physicalSubtreeNode root d.val path (by omega)
    let r := roundInterval (seedGridSpacing (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)) P) q
    let action := comparisonChildren source target hM P hP parent q hc
    let child := fun i s => (physicalBandChildMassTable source target U N P F A T node (by dsimp only [node, physicalSubtreeNode]; omega) i s : ℝ)
    subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ d path =
      (comparisonActionCurvature source target parent r action child,
        comparisonActionMass action child - wideActionMinimum parent r
          (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)) P hn child) := by
  unfold subtreeComparisonCharges
  rw [heq]
  simp only [dite_eq_right hactive]
  rfl

end Stage

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSubtreeNear
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.physicalMedianUpdateTable_value _root_.OAI.EditApproximation.physicalNodeCodeWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.treeLayerCodeWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual non-bad nodes with near-unit length-gap prediction have small regret. -/

namespace EditApproximation

open Finset

section Tree

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A)) (root : PhysicalNode M J) (K : ℕ) (hheight : root.1.val + K = J) (rootQ : TargetInterval target.length)

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (physicalSourceInterval source.length root, rootQ))
local notation "charges" => subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ
local notation "prediction" => subtreeComparisonPrediction source target hM U N P F A hP T root K hheight rootQ

include hsize hF hA hseed hT in
 theorem subtreeComparisonTreeRegret_near (ratio : ℝ) (hratio : 0 < ratio)
    (tau : ℚ) (htau : 0 ≤ tau)
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hMP : 4 * (M : ℝ) / P ≤ 1)
    (S : ℕ) (d : Fin K) (path : TreeLayer M d.val)
    (hnotbad : ¬ (comparisonActiveScale source target (frontier d.val path) < ratio * (charges d path).1 ∨
      comparisonActiveScale source target (frontier d.val path) < ratio * (charges d path).2))
    (hnear : 1 - tau < |prediction d path|) :
    (∑ t ∈ range S, subtreeComparisonTreeRegret source target hM U N P F A hP T delta choices root K rootQ t d path) ≤
      (1 / ratio + 4 * (tau : ℝ) * F) * comparisonActiveCost source target (frontier d.val path) := by
  classical
  generalize heq : frontier d.val path = state at hnotbad ⊢
  cases state with
  | none =>
    simp only [subtreeComparisonTreeRegret_none source target hM U N P F A hP T delta choices root K rootQ
      _ d path heq, sum_const_zero, comparisonActiveCost, mul_zero, le_refl]
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hstop : comparisonStopped source target parent q
    · simp only [subtreeComparisonTreeRegret_stopped source target hM U N P F A hP T delta choices root K rootQ
        _ d path parent q heq hstop, sum_const_zero, comparisonActiveCost, ite_eq_left hstop, mul_zero, le_refl]
    · have hp := comparisonSubtree_active_source source target hM P hP root rootQ d.val path parent q heq hstop
      let node : PhysicalNode M J := physicalSubtreeNode root d.val path (by omega)
      have hp' : parent = physicalSourceInterval source.length node := hp
      subst parent
      change ¬ comparisonStopped source target (physicalSourceInterval source.length node) q at hstop
      have hc : 0 < stateEditCost (physicalSource source node) target q := by
        change 0 < stateEditCost (substring source (physicalSourceInterval source.length node).lo
          (physicalSourceInterval source.length node).hi) target q
        change ¬ ((physicalSourceInterval source.length node).hi - (physicalSourceInterval source.length node).lo ≤ 1 ∨
          stateEditCost (substring source (physicalSourceInterval source.length node).lo
            (physicalSourceInterval source.length node).hi) target q = 0) at hstop
        omega
      let b : ℕ := 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
      let r := roundInterval (seedGridSpacing b P) q
      let action := comparisonChildren source target hM P hP (physicalSourceInterval source.length node) q hc
      let child := physicalBandChildMassTable source target U N P F A T node (by dsimp only [node, physicalSubtreeNode]; omega)
      have hspec := comparisonChildren_spec source target hM P hP (physicalSourceInterval source.length node) q hc
      have hn : wideActionList M (physicalSourceInterval source.length node) r b P ≠ [] := by
        intro hnil
        have hmem := hspec.1
        change action ∈ wideActionList M (physicalSourceInterval source.length node) r b P at hmem
        rw [hnil] at hmem
        exact List.not_mem_nil hmem
      have hcharges := subtreeComparisonCharges_active source target hM U N P F A hP T root K hheight rootQ d path q heq hstop hc hn
      have hprediction := subtreeComparisonPrediction_active source target hM U N P F A hP T root K hheight rootQ d path q heq hstop hn
      have hG := (nonbad_charge_bounds _ ratio _ _ hratio hnotbad).2
      change (charges d path).2 ≤ comparisonActiveScale source target
        (some (physicalSourceInterval source.length node, q)) / ratio at hG
      have hscaleEq : comparisonActiveScale source target
          (some (physicalSourceInterval source.length node, q)) = (b : ℝ) := by
        simp only [comparisonActiveScale, ite_eq_right hstop]
        rfl
      rw [hscaleEq, hcharges] at hG
      have hb : (b : ℝ) ≤ stateEditCost (physicalSource source node) target q := by
        exact_mod_cast (cost_dyadicScale _ _ hc le_rfl).2.1
      have hGcost : comparisonActionMass action (fun i s => (child i s : ℝ)) -
          wideActionMinimum (physicalSourceInterval source.length node) r b P hn (fun i s => (child i s : ℝ)) ≤
          (1 / ratio) * stateEditCost (physicalSource source node) target q := by
        have h := hG.trans (div_le_div_of_nonneg_right hb hratio.le)
        simpa only [one_div_mul_eq_div, action, child, r, b, node,
          physicalSource, physicalSourceInterval, physicalSubtreeNode] using h
      rw [hprediction] at hnear
      have hleaf : ¬ (physicalSourceInterval source.length node).hi -
          (physicalSourceInterval source.length node).lo ≤ 1 := fun h => hstop (Or.inl h)
      have h := physicalNode_near_length_gap_regret source target hM U N P F A hsize hP hF hA hseed T hT
        delta choices node (by dsimp only [node, physicalSubtreeNode]; omega) hleaf q hc hscale hMP hn tau htau hnear (1 / ratio) hGcost S
      have hpoint (t : ℕ) : subtreeComparisonTreeRegret source target hM U N P F A hP T delta choices root K rootQ t d path = _ :=
        subtreeComparisonTreeRegret_active source target hM U N P F A hsize hP hF hA hseed
          T hT delta choices root K hheight rootQ t d path q heq hstop
      simp_rw [hpoint]
      have hstop' : ¬ comparisonStopped source target (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)) q := hstop
      simpa only [comparisonActiveCost, ite_eq_right hstop', physicalSource, physicalSourceInterval, node, physicalSubtreeNode] using h

include hsize hF hA hseed hT in
 theorem subtreeComparisonNearRegret_bound (ratio : ℝ) (hratio : 0 < ratio)
    (tau : ℚ) (htau : 0 ≤ tau)
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hMP : 4 * (M : ℝ) / P ≤ 1)
    (hsmall : (K : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) (S : ℕ) :
    (∑ v : (Σ d : Fin K, TreeLayer M d.val) with
      (¬ (comparisonActiveScale source target (frontier v.1.val v.2) < ratio * (charges v.1 v.2).1 ∨
        comparisonActiveScale source target (frontier v.1.val v.2) < ratio * (charges v.1 v.2).2)) ∧
      1 - tau < |prediction v.1 v.2|,
      ∑ t ∈ range S, subtreeComparisonTreeRegret source target hM U N P F A hP T delta choices root K rootQ t v.1 v.2) ≤
      2 * (K : ℝ) * (1 / ratio + 4 * (tau : ℝ) * F) *
        comparisonStateCost source target (some (physicalSourceInterval source.length root, rootQ)) := by
  classical
  let coefficient : ℝ := 1 / ratio + 4 * (tau : ℝ) * F
  have hcoef : 0 ≤ coefficient := add_nonneg (div_nonneg zero_le_one hratio.le)
    (mul_nonneg (mul_nonneg (by norm_num) ((Rat.cast_nonneg (K := ℝ)).mpr htau)) (Nat.cast_nonneg _))
  have hcost : (∑ v : (Σ d : Fin K, TreeLayer M d.val), comparisonActiveCost source target (frontier v.1.val v.2)) ≤
      2 * K * comparisonStateCost source target (some (physicalSourceInterval source.length root, rootQ)) := by
    have heq := treeLayer_sigma_sum M K (fun (d : ℕ) (path : TreeLayer M d) =>
      comparisonActiveCost source target (frontier d path))
    exact heq.le.trans (comparison_total_active_cost_bound source target hM P hP
      (some (physicalSourceInterval source.length root, rootQ)) K hsmall)
  apply (sum_le_sum (fun v hv => subtreeComparisonTreeRegret_near source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices root K hheight rootQ ratio hratio tau htau hscale hMP S v.1 v.2
      (mem_filter.mp hv).2.1 (mem_filter.mp hv).2.2)).trans
  rw [← mul_sum]
  have hsub : (∑ v : (Σ d : Fin K, TreeLayer M d.val) with
      (¬ (comparisonActiveScale source target (frontier v.1.val v.2) < ratio * (charges v.1 v.2).1 ∨
        comparisonActiveScale source target (frontier v.1.val v.2) < ratio * (charges v.1 v.2).2)) ∧
      1 - tau < |prediction v.1 v.2|,
      comparisonActiveCost source target (frontier v.1.val v.2)) ≤
      ∑ v : (Σ d : Fin K, TreeLayer M d.val), comparisonActiveCost source target (frontier v.1.val v.2) := by
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun v _ _ => (comparisonActiveCost_bounds source target _).1)
  have h := mul_le_mul_of_nonneg_left (hsub.trans hcost) hcoef
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Tree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalTreeBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the three actual comparison-node classes in the expected telescope. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

theorem finite_three_region_budget {ι : Type*} [Fintype ι]
    (cost regret : ι → ℝ) (bad near : ι → Prop) [DecidablePred bad] [DecidablePred near]
    (badBudget nearBudget coefficient costBudget : ℝ)
    (hbad : (∑ i with bad i, regret i) ≤ badBudget)
    (hnear : (∑ i with ¬ bad i ∧ near i, regret i) ≤ nearBudget)
    (hgood : ∀ i, ¬ bad i → ¬ near i → regret i ≤ coefficient * cost i)
    (hcoef : 0 ≤ coefficient) (hcost : ∀ i, 0 ≤ cost i)
    (htotal : (∑ i, cost i) ≤ costBudget) :
    (∑ i, regret i) ≤ badBudget + nearBudget + coefficient * costBudget := by
  classical
  have hsplit : (∑ i, regret i) = (∑ i with bad i, regret i) +
      (∑ i with ¬ bad i ∧ near i, regret i) +
      (∑ i with ¬ bad i ∧ ¬ near i, regret i) := by
    simp only [sum_filter]
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    by_cases hb : bad i <;> by_cases hn : near i <;> simp only [hb, hn, not_true_eq_false,
      not_false_eq_true, and_false, and_true, ite_true, if_true, ite_false, if_false, add_zero, zero_add]
  have hgoodSum : (∑ i with ¬ bad i ∧ ¬ near i, regret i) ≤ coefficient * costBudget := by
    apply (sum_le_sum (fun i hi => hgood i (mem_filter.mp hi).2.1 (mem_filter.mp hi).2.2)).trans
    rw [← mul_sum]
    apply mul_le_mul_of_nonneg_left _ hcoef
    apply le_trans _ htotal
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => hcost i)
  rw [hsplit]
  linarith only [hbad, hnear, hgoodSum]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSubtreeBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

section Tree

variable {α Ω : Type*} [DecidableEq α] [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {M J : ℕ} (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : Ω → PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A)) (root : PhysicalNode M J) (K : ℕ) (hheight : root.1.val + K = J) (rootQ : TargetInterval target.length)
  (μ : Measure Ω) [IsProbabilityMeasure μ]

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (physicalSourceInterval source.length root, rootQ))
local notation "charges" => subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ
local notation "prediction" => subtreeComparisonPrediction source target hM U N P F A hP T root K hheight rootQ
local notation "D" => comparisonStateCost source target
  (some (physicalSourceInterval source.length root, rootQ))

include hsize hF hA hseed hT in
 theorem subtree_comparison_expected_regret_sum (ratio : ℝ) (hratio : 0 < ratio)
    (tau : ℚ) (htau : 0 ≤ tau)
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hMP : 4 * (M : ℝ) / P ≤ 1)
    (hcapacity : source.length ≤ M ^ J) (hsmall : (K : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2)
    (S : ℕ) (coefficient : ℝ) (hcoef : 0 ≤ coefficient)
    (hgood : ∀ (d : Fin K) (path : TreeLayer M d.val),
      ¬ (comparisonActiveScale source target (frontier d.val path) < ratio * (charges d path).1 ∨
        comparisonActiveScale source target (frontier d.val path) < ratio * (charges d path).2) →
      |prediction d path| ≤ 1 - tau →
      (∫ ω, (∑ t ∈ range S, subtreeComparisonTreeRegret source target hM U N P F A hP T delta
        (choices ω) root K rootQ t d path) ∂μ) ≤ coefficient * comparisonActiveCost source target (frontier d.val path)) :
    (∑ v : (Σ d : Fin K, TreeLayer M d.val),
      ∫ ω, (∑ t ∈ range S, subtreeComparisonTreeRegret source target hM U N P F A hP T delta
        (choices ω) root K rootQ t v.1 v.2) ∂μ) ≤
      (40000 * ratio * (F : ℝ) ^ 2 * (1 + (K : ℝ) / P + (K : ℝ) / T) +
        2 * K * (1 / ratio + 4 * (tau : ℝ) * F + coefficient)) * D := by
  classical
  let cost := fun (v : Σ d : Fin K, TreeLayer M d.val) => comparisonActiveCost source target (frontier v.1.val v.2)
  let regret := fun (v : Σ d : Fin K, TreeLayer M d.val) =>
    ∫ ω, (∑ t ∈ range S, subtreeComparisonTreeRegret source target hM U N P F A hP T delta
      (choices ω) root K rootQ t v.1 v.2) ∂μ
  let bad := fun (v : Σ d : Fin K, TreeLayer M d.val) =>
    comparisonActiveScale source target (frontier v.1.val v.2) < ratio * (charges v.1 v.2).1 ∨
      comparisonActiveScale source target (frontier v.1.val v.2) < ratio * (charges v.1 v.2).2
  let near := fun (v : Σ d : Fin K, TreeLayer M d.val) => 1 - tau < |prediction v.1 v.2|
  have hbad : (∑ v with bad v, regret v) ≤
      40000 * ratio * (F : ℝ) ^ 2 * (1 + (K : ℝ) / P + (K : ℝ) / T) * D := by
    rw [← integral_finsetSum _ (by intro v hv; exact .of_finite)]
    have h := integral_mono (μ := μ) (.of_finite) (integrable_const _) (fun ω =>
      subtreeComparisonBadRegret_bound source target hM U N P F A hsize hP hF hA hseed
        T hT delta (choices ω) root K hheight rootQ ratio hratio.le hscale hMP hcapacity hsmall S)
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hnear : (∑ v with ¬ bad v ∧ near v, regret v) ≤
      2 * K * (1 / ratio + 4 * (tau : ℝ) * F) * D := by
    rw [← integral_finsetSum _ (by intro v hv; exact .of_finite)]
    have h := integral_mono (μ := μ) (.of_finite) (integrable_const _) (fun ω =>
      subtreeComparisonNearRegret_bound source target hM U N P F A hsize hP hF hA hseed
        T hT delta (choices ω) root K hheight rootQ ratio hratio tau htau hscale hMP hsmall S)
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hcost : (∑ v, cost v) ≤ 2 * K * D := by
    have heq := treeLayer_sigma_sum M K (fun (d : ℕ) (path : TreeLayer M d) =>
      comparisonActiveCost source target (frontier d path))
    exact heq.le.trans (comparison_total_active_cost_bound source target hM P hP
      (some (physicalSourceInterval source.length root, rootQ)) K hsmall)
  have h := finite_three_region_budget cost regret bad near _ _ coefficient (2 * K * D)
    hbad hnear (fun v hb hn => hgood v.1 v.2 hb (le_of_not_gt hn)) hcoef
    (fun v => (comparisonActiveCost_bounds source target _).1) hcost
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

include hsize hF hA hseed hT in
 theorem subtree_expected_excess_of_good_nodes_oai (ratio : ℝ) (hratio : 0 < ratio)
    (tau : ℚ) (htau : 0 ≤ tau)
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hMP : 4 * (M : ℝ) / P ≤ 1)
    (hcapacity : source.length ≤ M ^ J) (hsmall : (K : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2)
    (S : ℕ) (hS : 0 < S) (coefficient : ℝ) (hcoef : 0 ≤ coefficient)
    (hgood : ∀ (d : Fin K) (path : TreeLayer M d.val),
      ¬ (comparisonActiveScale source target (frontier d.val path) < ratio * (charges d path).1 ∨
        comparisonActiveScale source target (frontier d.val path) < ratio * (charges d path).2) →
      |prediction d path| ≤ 1 - tau →
      (∫ ω, (∑ t ∈ range S, subtreeComparisonTreeRegret source target hM U N P F A hP T delta
        (choices ω) root K rootQ t d path) ∂μ) ≤ coefficient * comparisonActiveCost source target (frontier d.val path)) :
    (∫ ω, max ((physicalRefinement source target U N P F A T delta (choices ω)
        root S rootQ : ℝ) -
      stateEditCost (physicalSource source root) target rootQ) 0 ∂μ) ≤
      ((8 * (M : ℝ) + 512 * F) * K / P +
        (40000 * ratio * (F : ℝ) ^ 2 * (1 + (K : ℝ) / P + (K : ℝ) / T) +
          2 * K * (1 / ratio + 4 * (tau : ℝ) * F + coefficient)) / S) *
        stateEditCost (physicalSource source root) target rootQ := by
  classical
  let budget := fun (d : ℕ) (path : TreeLayer M d) => if hd : d < K then
    ∫ ω, (∑ t ∈ range S, subtreeComparisonTreeRegret source target hM U N P F A hP T delta
      (choices ω) root K rootQ t ⟨d, hd⟩ path) ∂μ else 0
  have hnode (d : ℕ) (hd : d < K) (path : TreeLayer M d) :
      (∫ ω, (∑ t ∈ range S,
        (subtreeClippedLift source target hM U N P F A hP T delta (choices ω) root rootQ (t + 1) d path -
          (128 * (F : ℝ)) * comparisonMovement source target P (frontier d path) -
          ∑ i : Fin M, subtreeClippedLift source target hM U N P F A hP T delta
            (choices ω) root rootQ (t + 1) (d + 1) (path, i))) ∂μ) ≤ budget d path := by
    simp only [budget, dite_eq_left hd, subtreeComparisonTreeRegret, le_refl]
  have htelescope := subtree_expected_excess source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices root K hheight rootQ μ S hS hcapacity hsmall budget hnode
  have hsum := subtree_comparison_expected_regret_sum source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices root K hheight rootQ μ ratio hratio tau htau hscale hMP hcapacity hsmall S coefficient hcoef hgood
  have heq : (∑ d ∈ range K, ∑ path : TreeLayer M d, budget d path) =
      ∑ v : (Σ d : Fin K, TreeLayer M d.val),
        ∫ ω, (∑ t ∈ range S, subtreeComparisonTreeRegret source target hM U N P F A hP T delta
          (choices ω) root K rootQ t v.1 v.2) ∂μ := by
    rw [← treeLayer_sigma_sum M K budget]
    apply sum_congr rfl
    intro v _
    simp only [budget, dite_eq_left v.1.isLt]
  rw [heq] at htelescope
  have hroot : D = (stateEditCost (physicalSource source root) target rootQ : ℝ) := by
    rfl
  rw [hroot] at hsum
  have hdiv := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg (α := ℝ) S)
  calc
    _ ≤ _ := htelescope
    _ ≤ ((8 * (M : ℝ) + 512 * F) * K / P) * stateEditCost (physicalSource source root) target rootQ +
        ((40000 * ratio * (F : ℝ) ^ 2 * (1 + (K : ℝ) / P + (K : ℝ) / T) +
          2 * K * (1 / ratio + 4 * (tau : ℝ) * F + coefficient)) *
            stateEditCost (physicalSource source root) target rootQ) / S := add_le_add_right hdiv _
    _ = _ := by ring

end Tree

end EditApproximation

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.EditApproximation.subtree_expected_excess_of_good_nodes_oai.{u_1, u_2} := @OAI.EditApproximation.subtree_expected_excess_of_good_nodes_oai.{u_1, u_2}
