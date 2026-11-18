-- Prove2me | solution 1 for OAI.EditApproximation.physicalNode_generic_regret
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:44:59.141238+00:00
-- url     : https://prove2.me/submissions/f537fe33-b7b6-446b-b353-d087948f9696

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
import Theorems.Thm_OAI_EditApproximation_stageWarmup_invariants
import Theorems.Thm_OAI_EditApproximation_stageWarmup_postfixed

section
-- module Solutions.OAIQ361V3_EA.EditDistance_Metric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Unrestricted edit scripts, metric inequalities, and common subsequences
-/

namespace EditDistortion

universe u v

variable {Alpha : Type u} {Beta : Type v} {s : Bool}

namespace Script

theorem eq_of_zero {x y : List Alpha} (h : Script s 0 x y) : x = y := by
  cases h
  rfl

end Script



theorem cost_eq_zero_iff {x y : List Alpha} : cost s x y = 0 ↔ x = y := by
  constructor
  · intro h
    have hc := cost_spec (s := s) x y
    rw [h] at hc
    exact hc.eq_of_zero
  · rintro rfl
    exact cost_refl _

end EditDistortion

end OAI
end

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

theorem finiteMinimum_le_member (fallback : ℝ) (values : List ℝ)
    {value : ℝ} (hvalue : value ∈ values) : finiteMinimum fallback values ≤ value := by
  induction values with
  | nil => simp at hvalue
  | cons v rest ih =>
    rcases List.mem_cons.mp hvalue with rfl | hvalue
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hvalue)

theorem finiteBellman_le_action {Parent Child : Type*} {M : ℕ}
    (fallback : Parent → ℝ) (distance : Parent → Parent → ℝ) (L : ℝ)
    (actions : List (BellmanAction Parent Child M)) (child : Child → ℝ)
    (query : Parent) (action : BellmanAction Parent Child M) (haction : action ∈ actions) :
    finiteBellman fallback distance L actions child query ≤
      bellmanActionValue distance L child query action :=
  finiteMinimum_le_member _ _ (List.mem_map.mpr ⟨action, haction, rfl⟩)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_RationalRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Rational execution of the Bellman and refinement operations

Every finite minimum, cone cost, warmup iteration, and refinement update
is computed in rational arithmetic. The real analysis used elsewhere is
the exact cast of these operations. An absent online candidate returns
the cone minimum, avoiding an extended-real value in the implementation.
-/

namespace EditApproximation





theorem rationalActionValue_cast {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → ℚ) (L : ℚ) (child : Child → ℚ)
    (query : Parent) (action : RationalBellmanAction Parent Child M) :
    (rationalActionValue distance L child query action : ℝ) =
      bellmanActionValue (fun q r => (distance q r : ℝ)) (L : ℝ)
        (fun s => (child s : ℝ)) query action.toReal := by
  simp only [rationalActionValue, bellmanActionValue, RationalBellmanAction.toReal,
    Rat.cast_add, Rat.cast_mul, Rat.cast_sum]

theorem rationalBellman_cast {Parent Child : Type*} {M : ℕ}
    (fallback : Parent → ℚ) (distance : Parent → Parent → ℚ) (L : ℚ)
    (actions : List (RationalBellmanAction Parent Child M)) (child : Child → ℚ) (query : Parent) :
    (rationalBellman fallback distance L actions child query : ℝ) =
      finiteBellman (fun q => (fallback q : ℝ)) (fun q r => (distance q r : ℝ)) (L : ℝ)
        (actions.map RationalBellmanAction.toReal) (fun s => (child s : ℝ)) query := by
  rw [rationalBellman, rationalMinimum_cast]
  unfold finiteBellman
  simp only [List.map_map, Function.comp_def, rationalActionValue_cast]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ActualRepresentatives
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.dyadicScalesWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryScaleDispatchWithWork_value _root_.OAI.EditApproximation.queryScalePresentWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite representative list and the actual rounded comparison representative. -/

namespace EditApproximation

theorem rounded_comparison_representative {α : Type*} (source target : List α)
    (N P F : ℕ) (a : ℚ) (hP : 4 ≤ P) (hF : 0 ≤ (F : ℚ)) (ha : 0 < a)
    (initial : TargetInterval target.length → ℚ)
    (hlower : ∀ r, (stateEditCost source target r : ℚ) / a ≤ initial r)
    (hupper : ∀ r, initial r ≤ 2 * F * stateEditCost source target r)
    (q : TargetInterval target.length) (hc : 0 < stateEditCost source target q)
    (hN : stateEditCost source target q ≤ N) :
    let b := 2 ^ Nat.log 2 (stateEditCost source target q)
    (b, roundInterval (seedGridSpacing b P) q) ∈ representativeList N P F a initial := by
  dsimp only
  let b := 2 ^ Nat.log 2 (stateEditCost source target q)
  let r := roundInterval (seedGridSpacing b P) q
  have hscale := cost_dyadicScale _ N hc hN
  have hscaleLower : (b : ℚ) ≤ stateEditCost source target q := by exact_mod_cast hscale.2.1
  have hscaleUpper : (stateEditCost source target q : ℚ) < 2 * b := by exact_mod_cast hscale.2.2
  have he := rounded_seedGrid_error b P (by omega) q
  have he0 : (0 : ℚ) ≤ targetEndpointDistance q r := Nat.cast_nonneg _
  have hPr : (4 : ℚ) ≤ P := by exact_mod_cast hP
  have hsmall : (targetEndpointDistance q r : ℚ) ≤ b / 2 := by nlinarith only [he, he0, hPr]
  have hdist := abs_le.mp (stateEditCost_distance_abs source target q r)
  have hcrlo : (b : ℚ) / 4 ≤ stateEditCost source target r := by linarith only [hdist.1, hdist.2, hsmall, hscaleLower]
  have hcrhi : (stateEditCost source target r : ℚ) ≤ 4 * b := by
    have hb0 : (0 : ℚ) ≤ b := Nat.cast_nonneg _
    linarith only [hdist.1, hdist.2, hsmall, hscaleUpper, hb0]
  apply representativeList_mem a initial r hscale.1 (roundInterval_on_grid _ q)
  · have hdiv := div_le_div_of_nonneg_right hcrlo ha.le
    have hid : (b : ℚ) / 4 / a = b / (4 * a) := by ring
    rw [hid] at hdiv
    exact hdiv.trans (hlower r)
  · have hmul := mul_le_mul_of_nonneg_left hcrhi (mul_nonneg (by norm_num : (0 : ℚ) ≤ 2) hF)
    exact (hupper r).trans (by nlinarith only [hmul])

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SharedActions
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact connection cancellation for shared-endpoint finite actions. -/

namespace EditApproximation

theorem zero_connection_target_eq {α : Type*} (target : List α) {M : ℕ}
    (q : TargetInterval target.length) (states : Fin M → TargetInterval target.length)
    (hconn : endpointActionConnection q states = 0) :
    targetConcatenation target (List.ofFn states) = substring target q.lo q.hi := by
  have h := target_connection_bound target (List.ofFn states) q
  change EditDistortion.edit _ _ ≤ endpointActionConnection q states at h
  rw [hconn] at h
  exact (EditDistortion.cost_eq_zero_iff (s := true)).mp (Nat.eq_zero_of_le_zero h)

theorem zero_connection_gap_sum {α : Type*} (source target : List α) {M : ℕ}
    (hM : 0 < M) (parent : TargetInterval source.length)
    (q : TargetInterval target.length) (states : Fin M → TargetInterval target.length)
    (hconn : endpointActionConnection q states = 0) :
    (∑ i, stateLengthGap
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (states i)) =
        stateLengthGap (substring source parent.lo parent.hi) target q := by
  let piece := fun i : Fin M =>
    substring source (sourceChild parent i).lo (sourceChild parent i).hi
  have hsource := congrArg List.length (sourceChild_partition source hM parent)
  simp only [List.length_flatten, List.map_ofFn, List.sum_ofFn, Function.comp_def] at hsource
  have htarget := congrArg List.length (zero_connection_target_eq target q states hconn)
  simp only [targetConcatenation, List.length_flatten, List.map_ofFn,
    List.sum_ofFn, Function.comp_def] at htarget
  have hsourceR : (∑ i, ((piece i).length : ℝ)) =
      (substring source parent.lo parent.hi).length := by exact_mod_cast hsource
  have htargetR : (∑ i, ((substring target (states i).lo (states i).hi).length : ℝ)) =
      (substring target q.lo q.hi).length := by exact_mod_cast htarget
  simp only [stateLengthGap_actual, signedLengthGap, Finset.sum_sub_distrib]
  rw [htargetR, hsourceR]

theorem zero_connection_cost_sum_lower {α : Type*} (source target : List α) {M : ℕ}
    (hM : 0 < M) (parent : TargetInterval source.length)
    (q : TargetInterval target.length) (states : Fin M → TargetInterval target.length)
    (hconn : endpointActionConnection q states = 0) :
    (stateEditCost (substring source parent.lo parent.hi) target q : ℝ) ≤
      ∑ i, (stateEditCost
        (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (states i) : ℝ) := by
  have h := actual_endpoint_action_lower source target hM parent q states 1 le_rfl
    (fun i s => (stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s : ℝ))
    (by intro i; simp only [div_one, le_refl])
    (fun i => stateEditCost_length_lower _ _ _)
  have hlower := (le_max_left _ _).trans h
  simpa only [div_one, endpointActionValue, hconn, Nat.cast_zero, zero_add] using hlower

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Regret
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
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

theorem clipped_bellman_bound {ι : Type*} (children : Finset ι)
    (cost value charge : ℝ) (childCost childValue : ι → ℝ)
    (hcost : cost ≤ charge + ∑ i ∈ children, childCost i)
    (hvalue : value ≤ charge + ∑ i ∈ children, childValue i) :
    clipped cost value ≤ charge + ∑ i ∈ children, clipped (childCost i) (childValue i) := by
  apply max_le
  · exact hcost.trans (add_le_add (le_refl charge)
      (sum_le_sum fun i _ => le_max_left _ _))
  · exact hvalue.trans (add_le_add (le_refl charge)
      (sum_le_sum fun i _ => le_max_right _ _))

/-- Clipping preserves the useful endpoint decrease bound even when the
initial estimate itself lies below the true cost. -/
theorem clipped_endpoint_decrease (cost initial final mass gap : ℝ)
    (hmono : final ≤ initial) (hinit : initial ≤ mass)
    (hgapCost : |gap| ≤ cost) (hgapMass : |gap| ≤ mass) :
    clipped cost initial - clipped cost final ≤ mass - |gap| := by
  by_cases h : initial ≤ cost
  · simp only [clipped, max_eq_left h, max_eq_left (hmono.trans h), sub_self]
    exact sub_nonneg.mpr hgapMass
  · have hmax : clipped cost initial = initial := max_eq_right (le_of_not_ge h)
    have hfinal : |gap| ≤ clipped cost final := hgapCost.trans (le_max_left _ _)
    rw [hmax]
    exact sub_le_sub hinit hfinal

/-- Finite-time telescoping of the clipped parent Bellman inequalities.
The summation uses indices `t + 1`, corresponding to manuscript indices
`1, …, S`. -/
theorem generic_regret_telescope {ι : Type*} (children : Finset ι)
    (S : ℕ) (cost charge : ℝ) (childCost : ι → ℝ)
    (parent : ℕ → ℝ) (child : ℕ → ι → ℝ)
    (hsplit : cost ≤ charge + ∑ i ∈ children, childCost i)
    (hbellman : ∀ t < S, parent (t + 1) ≤ charge + ∑ i ∈ children, child t i) :
    ∑ t ∈ range S,
        (clipped cost (parent (t + 1)) - charge -
          ∑ i ∈ children, clipped (childCost i) (child (t + 1) i)) ≤
      ∑ i ∈ children,
        (clipped (childCost i) (child 0 i) - clipped (childCost i) (child S i)) := by
  let total : ℕ → ℝ := fun t => ∑ i ∈ children, clipped (childCost i) (child t i)
  have hstep (t : ℕ) (ht : t < S) :
      clipped cost (parent (t + 1)) - charge - total (t + 1) ≤
        total t - total (t + 1) := by
    have hb := clipped_bellman_bound children cost (parent (t + 1)) charge
      childCost (child t) hsplit (hbellman t ht)
    change clipped cost (parent (t + 1)) ≤ charge + total t at hb
    linarith
  have htel : ∑ t ∈ range S, (total t - total (t + 1)) = total 0 - total S := by
    clear hbellman hstep
    induction S with
    | zero => simp
    | succ S ih =>
      rw [sum_range_succ, ih]
      ring
  calc
    _ ≤ ∑ t ∈ range S, (total t - total (t + 1)) := by
      exact sum_le_sum fun t ht => hstep t (mem_range.mp ht)
    _ = total 0 - total S := htel
    _ = _ := by simp only [total, sum_sub_distrib]

/-- The endpoint terms in generic regret are bounded by the warmup masses
minus the absolute length gaps. -/
theorem generic_regret_mass_bound {ι : Type*} (children : Finset ι)
    (S : ℕ) (cost charge : ℝ) (childCost mass gap : ι → ℝ)
    (parent : ℕ → ℝ) (child : ℕ → ι → ℝ)
    (hsplit : cost ≤ charge + ∑ i ∈ children, childCost i)
    (hbellman : ∀ t < S, parent (t + 1) ≤ charge + ∑ i ∈ children, child t i)
    (hmono : ∀ i ∈ children, child S i ≤ child 0 i)
    (hinit : ∀ i ∈ children, child 0 i ≤ mass i)
    (hgapCost : ∀ i ∈ children, |gap i| ≤ childCost i)
    (hgapMass : ∀ i ∈ children, |gap i| ≤ mass i) :
    ∑ t ∈ range S,
        (clipped cost (parent (t + 1)) - charge -
          ∑ i ∈ children, clipped (childCost i) (child (t + 1) i)) ≤
      ∑ i ∈ children, (mass i - |gap i|) := by
  apply (generic_regret_telescope children S cost charge childCost parent child
    hsplit hbellman).trans
  exact sum_le_sum fun i hi => clipped_endpoint_decrease (childCost i)
    (child 0 i) (child S i) (mass i) (gap i)
    (hmono i hi) (hinit i hi) (hgapCost i hi) (hgapMass i hi)

/-- Since child length gaps add to the parent's gap, their absolute values
give the final bound in manuscript Equation `eq:generic-regret`. -/
theorem sum_mass_sub_abs_le {ι : Type*} (children : Finset ι)
    (mass gap : ι → ℝ) :
    ∑ i ∈ children, (mass i - |gap i|) ≤
      (∑ i ∈ children, mass i) - |∑ i ∈ children, gap i| := by
  rw [sum_sub_distrib]
  exact sub_le_sub_left (abs_sum_le_sum_abs _ _) _

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ComparisonTree
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.scheduledSeedDrawFintype
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

theorem comparisonChildren_lower {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (hc : 0 < stateEditCost (substring source parent.lo parent.hi) target q) :
    let b := 2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)
    let r := roundInterval (seedGridSpacing b P) q
    (stateEditCost (substring source parent.lo parent.hi) target q : ℝ) ≤
      (∑ i, (stateEditCost (substring source (sourceChild parent i).lo (sourceChild parent i).hi)
        target (comparisonChildren source target hM P hP parent q hc i) : ℝ)) +
          targetEndpointDistance q r := by
  dsimp only
  let r := roundInterval (seedGridSpacing
    (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)) P) q
  have hlower := zero_connection_cost_sum_lower source target hM parent r
    (comparisonChildren source target hM P hP parent q hc)
    (comparisonChildren_spec source target hM P hP parent q hc).2.1
  have hspatial : (stateEditCost (substring source parent.lo parent.hi) target q : ℝ) ≤
      stateEditCost (substring source parent.lo parent.hi) target r + targetEndpointDistance q r := by
    exact_mod_cast stateEditCost_spatial (substring source parent.lo parent.hi) target q r
  linarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalWarmup
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Warmup on physical node labels

The Bellman operator requests only physical children. Distinct child labels
are retained even at repeated cuts. Nodes at the last physical level, and
source intervals of width at most one, retain their initial value.
-/

namespace EditApproximation









theorem physicalBellman_le_action {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (value : PhysicalEntry M J target.length → ℝ) (node : PhysicalNode M J)
    (hbelow : node.1.val < J) (hleaf : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1)
    (q r : TargetInterval target.length) (b : ℕ)
    (hrep : (b, r) ∈ representatives node)
    (states : Fin M → TargetInterval target.length)
    (hstates : states ∈ wideActionList M (physicalSourceInterval source.length node) r b P) :
    physicalBellman source target P L initial representatives value (node, q) ≤
      L * targetEndpointDistance q r + endpointActionConnection r states +
        ∑ i, value (physicalChild node hbelow i, states i) := by
  classical
  unfold physicalBellman
  dsimp only
  rw [dite_eq_left hbelow, ite_eq_right hleaf]
  let action : BellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M :=
    ⟨r, endpointActionConnection r states, fun i => (i, states i)⟩
  have haction : action ∈ actualWideActions (physicalSourceInterval source.length node)
      (representatives node) P := by
    apply List.mem_flatMap.mpr
    refine ⟨(b, r), hrep, ?_⟩
    exact List.mem_map.mpr ⟨states, hstates, rfl⟩
  exact finiteBellman_le_action (fun s => initial (node, s))
    (fun s t => targetEndpointDistance s t) L
    (actualWideActions (physicalSourceInterval source.length node) (representatives node) P)
    (fun is => value (physicalChild node hbelow is.1, is.2)) q action haction

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRationalWarmup
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Rational execution of the physical wide-action warmup, with exact real casts. -/

namespace EditApproximation

open Finset



theorem rationalActualWideActions_toReal {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ) :
    (rationalActualWideActions (M := M) parent representatives P).map RationalBellmanAction.toReal =
      actualWideActions (M := M) parent representatives P := by
  simp only [rationalActualWideActions, actualWideActions, List.map_flatMap,
    List.map_map, Function.comp_def, RationalBellmanAction.toReal, Rat.cast_natCast]

theorem rationalPhysicalBellman_cast {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℚ) (initial : PhysicalEntry M J target.length → ℚ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (value : PhysicalEntry M J target.length → ℚ) (state : PhysicalEntry M J target.length) :
    (rationalPhysicalBellman source target P L initial representatives value state : ℝ) =
      physicalBellman source target P (L : ℝ) (fun s => (initial s : ℝ)) representatives
        (fun s => (value s : ℝ)) state := by
  classical
  unfold rationalPhysicalBellman physicalBellman
  dsimp only
  split_ifs
  · rfl
  · rw [rationalBellman_cast, rationalActualWideActions_toReal]
    simp only [actualWideBellman, Rat.cast_natCast]
  · rfl

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalInitial
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The actual initial table uses exact empty/singleton leaves and local cones elsewhere. -/

namespace EditApproximation

open EditDistortion



theorem physicalInitialTable_bounds {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A a : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A) (ha : 1 ≤ a) (hfactor : A ≤ a * F)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (state : PhysicalEntry M J target.length) :
    max ((stateEditCost (physicalSource source state.1) target state.2 : ℚ) / a)
        |rationalStateGap (physicalSource source state.1) target state.2| ≤
      physicalInitialTable source target U N P F A a state ∧
    physicalInitialTable source target U N P F A a state ≤
      2 * F * stateEditCost (physicalSource source state.1) target state.2 := by
  unfold physicalInitialTable
  dsimp only
  split_ifs with hleaf
  · rw [shortSourceCost_eq_edit _ _ hleaf]
    change max ((stateEditCost _ _ _ : ℚ) / a) |rationalStateGap _ _ _| ≤
        stateEditCost _ _ _ ∧ (stateEditCost _ _ _ : ℚ) ≤ 2 * F * stateEditCost _ _ _
    have hc : (0 : ℚ) ≤ stateEditCost (physicalSource source state.1) target state.2 := Nat.cast_nonneg _
    have hFQ : (1 : ℚ) ≤ F := by exact_mod_cast hF
    have hgap := stateEditCost_length_lower (physicalSource source state.1) target state.2
    rw [← rationalStateGap_cast] at hgap
    constructor
    · apply max_le
      · apply (div_le_iff₀ (by linarith : 0 < a)).2
        nlinarith
      · exact_mod_cast hgap
    · nlinarith
  · rw [localInitialConeTable_eq_global _ _ _ N P F A a hP hF hA ha hfactor
      (fun q => physical_state_cost_le source target N hsize (state.1, q))
      (fun q => hseed (state.1, q))]
    exact globalInitialConeTable_bounds _ _ _ N P F A a hP hF hA ha hfactor
      (fun q => physical_state_cost_le source target N hsize (state.1, q))
      (fun q => hseed (state.1, q)) state.2

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_StageComparison
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual stage masses and representatives supply the comparison-node warmup hypotheses. -/

namespace EditApproximation

theorem stageRounded_representative_mem {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (node : PhysicalNode M J) (q : TargetInterval target.length)
    (hc : 0 < stateEditCost (physicalSource source node) target q) :
    let b := 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
    (b, roundInterval (seedGridSpacing b P) q) ∈ stageRepresentatives source target U N P F A node := by
  have hfactor := refinementFactor_spec A F (by omega)
  have hbounds := physicalInitialTable_bounds source target U N P F A (refinementFactor A F)
    hsize hP hF hA hfactor.1 hfactor.2 hseed
  exact rounded_comparison_representative (physicalSource source node) target N P F
    (refinementFactor A F) (by omega) (Nat.cast_nonneg _) (by linarith only [hfactor.1])
    (fun r => stageInitial source target U N P F A (node, r))
    (fun r => (le_max_left _ _).trans (hbounds (node, r)).1)
    (fun r => (hbounds (node, r)).2) q hc (physical_state_cost_le source target N hsize (node, q))

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

include hsize hF hA hseed hT hleaf in
 theorem physicalNode_generic_regret_oai (S : ℕ) :
    (∑ t ∈ range S, regret t) ≤ W - |stateLengthGap (physicalSource source node) target r| := by
  have hspec := comparisonChildren_spec source target hM P hP parent q hc
  have hzero : endpointActionConnection r action = 0 := hspec.2.1
  have hrep := stageRounded_representative_mem source target U N P F A hsize hP hF hA hseed node q hc
  have hL : (1 : ℝ) ≤ 128 * F := by
    have hFR : (1 : ℝ) ≤ F := by exact_mod_cast hF
    linarith only [hFR]
  have hsplit : (stateEditCost (physicalSource source node) target q : ℝ) ≤
      (128 * (F : ℝ)) * targetEndpointDistance q r +
        ∑ i, (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (action i) : ℝ) := by
    have h := comparisonChildren_lower source target hM P hP parent q hc
    have he := mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg (α := ℝ) (targetEndpointDistance q r))
    change (stateEditCost (physicalSource source node) target q : ℝ) ≤
      (∑ i, (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (action i) : ℝ)) +
        targetEndpointDistance q r at h
    simp only [one_mul] at he
    linarith only [h, he]
  have hbellman (t : ℕ) (_ht : t < S) :
      value (t + 1) (node, q) ≤ (128 * (F : ℝ)) * targetEndpointDistance q r +
        ∑ i, value t (physicalChild node hbelow i, action i) := by
    have hQ := (physicalRefinement_bellman_invariants source target U N P F A T delta choices node t q).2
    have hR := (Rat.cast_le (K := ℝ)).mpr hQ
    rw [rationalPhysicalBellman_cast] at hR
    have h := physicalBellman_le_action source target P ((128 * F : ℚ) : ℝ)
      (fun s => (stageInitial source target U N P F A s : ℝ))
      (stageRepresentatives source target U N P F A) (value t) node hbelow hleaf q r b hrep action hspec.1
    rw [hzero, Nat.cast_zero, add_zero] at h
    simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using hR.trans h
  have hmono (i : Fin M) (_hi : i ∈ (univ : Finset (Fin M))) :
      value S (physicalChild node hbelow i, action i) ≤ value 0 (physicalChild node hbelow i, action i) := by
    apply Rat.cast_le.mpr
    have hantitone : Antitone (fun t => physicalRefinement source target U N P F A T delta choices
        (physicalChild node hbelow i) t (action i)) :=
      antitone_nat_of_succ_le (fun t => physicalRefinement_nonincreasing source target U N P F A T delta choices
        (physicalChild node hbelow i) t (action i))
    exact hantitone (Nat.zero_le S)
  have hinv (i : Fin M) := stageWarmup_invariants source target hM U N P F A hsize hP hF hA hseed
    T hT (physicalChild node hbelow i, action i)
  have hinit (i : Fin M) (_hi : i ∈ (univ : Finset (Fin M))) :
      value 0 (physicalChild node hbelow i, action i) ≤ mass i (action i) := by
    dsimp only
    rw [physicalRefinement_zero]
    exact Rat.cast_le.mpr (hinv i).2.1
  have hgapMass (i : Fin M) (_hi : i ∈ (univ : Finset (Fin M))) :
      |stateLengthGap (physicalSource source (physicalChild node hbelow i)) target (action i)| ≤ mass i (action i) :=
    ((le_max_right _ _).trans (hinv i).1).trans (Rat.cast_le.mpr (hinv i).2.1)
  have h := generic_regret_mass_bound univ S
    (stateEditCost (physicalSource source node) target q : ℝ)
    ((128 * (F : ℝ)) * targetEndpointDistance q r)
    (fun i => (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (action i) : ℝ))
    (fun i => mass i (action i))
    (fun i => stateLengthGap (physicalSource source (physicalChild node hbelow i)) target (action i))
    (fun t => value t (node, q)) (fun t i => value t (physicalChild node hbelow i, action i))
    hsplit hbellman hmono hinit
    (fun i _ => stateEditCost_length_lower _ _ _) hgapMass
  apply h.trans
  have hsum := sum_mass_sub_abs_le univ (fun i => mass i (action i))
    (fun i => stateLengthGap (physicalSource source (physicalChild node hbelow i)) target (action i))
  have hgapSum : (∑ i, stateLengthGap (physicalSource source (physicalChild node hbelow i)) target (action i)) =
      stateLengthGap (physicalSource source node) target r :=
    zero_connection_gap_sum source target hM parent r action hzero
  rw [hgapSum] at hsum
  exact hsum

end Node

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.physicalNode_generic_regret_oai.{u_1} := @OAI.EditApproximation.physicalNode_generic_regret_oai.{u_1}
