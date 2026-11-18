-- Prove2me | solution 1 for OAI.EditApproximation.subtreeComparisonCharges_local
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:47:25.45661+00:00
-- url     : https://prove2.me/submissions/78854a31-3652-4e85-935d-25928e323ab1

import Mathlib
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_rationalPhysicalWarmupAverage_cast
import Theorems.Thm_OAI_EditApproximation_rationalPhysicalWarmup_cast
import Theorems.Thm_OAI_EditApproximation_stageComparison_positive_movement
import Theorems.Thm_OAI_EditApproximation_stageWarmupMass_at_stopped
import Theorems.Thm_OAI_EditApproximation_stageWarmupMass_child_lower
import Theorems.Thm_OAI_EditApproximation_stageWarmup_invariants

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

theorem finiteBellman_le_action {Parent Child : Type*} {M : ℕ}
    (fallback : Parent → ℝ) (distance : Parent → Parent → ℝ) (L : ℝ)
    (actions : List (BellmanAction Parent Child M)) (child : Child → ℝ)
    (query : Parent) (action : BellmanAction Parent Child M) (haction : action ∈ actions) :
    finiteBellman fallback distance L actions child query ≤
      bellmanActionValue distance L child query action :=
  finiteMinimum_le_member _ _ (List.mem_map.mpr ⟨action, haction, rfl⟩)

/-- Averaging the actual one-step action inequality gives the warmup
mass slack, with the exact endpoint correction before its simplification
to the nonnegative initial-cone charge. -/
theorem warmup_average_action_bound {State ι : Type*} [Fintype ι]
    (operator : (State → ℝ) → State → ℝ) (initial : State → ℝ)
    (T : ℕ) (hT : 0 < T) (parent : State) (child : ι → State) (charge : ℝ)
    (haction : ∀ t < T, warmup operator initial (t + 1) parent ≤
      charge + ∑ i, warmup operator initial t (child i)) :
    warmupAverage operator initial T parent -
        (initial parent - warmup operator initial T parent) / T ≤
      charge + ∑ i, warmupAverage operator initial T (child i) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have htelAll : ∀ K : ℕ, (∑ t ∈ range K, warmup operator initial t parent) -
      (∑ t ∈ range K, warmup operator initial (t + 1) parent) =
        initial parent - warmup operator initial K parent := by
    intro K
    induction K with
    | zero => simp [warmup]
    | succ K ih =>
      rw [sum_range_succ, sum_range_succ]
      linarith
  have htel := htelAll T
  have hsum := sum_le_sum (s := range T) fun t ht => haction t (mem_range.mp ht)
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, sum_comm] at hsum
  unfold warmupAverage
  rw [← sub_div, ← sum_div]
  apply (div_le_iff₀ hTr).2
  have hright : (charge + (∑ i, ∑ t ∈ range T,
      warmup operator initial t (child i)) / T) * T =
        (T : ℝ) * charge + ∑ i, ∑ t ∈ range T, warmup operator initial t (child i) := by
    field_simp
  rw [hright, ← htel]
  linarith

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

theorem physicalWarmup_average_action_bound {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (T : ℕ) (hT : 0 < T) (node : PhysicalNode M J)
    (hbelow : node.1.val < J) (hleaf : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1)
    (q r : TargetInterval target.length) (b : ℕ)
    (hrep : (b, r) ∈ representatives node)
    (states : Fin M → TargetInterval target.length)
    (hstates : states ∈ wideActionList M (physicalSourceInterval source.length node) r b P) :
    physicalWarmupAverage source target P L initial representatives T (node, q) -
        (initial (node, q) - physicalWarmup source target P L initial representatives T (node, q)) / T ≤
      L * targetEndpointDistance q r + endpointActionConnection r states +
        ∑ i, physicalWarmupAverage source target P L initial representatives T
          (physicalChild node hbelow i, states i) := by
  apply warmup_average_action_bound _ _ T hT (node, q)
    (fun i => (physicalChild node hbelow i, states i))
    (L * targetEndpointDistance q r + endpointActionConnection r states)
  intro t _
  exact physicalBellman_le_action source target P L initial representatives _ node hbelow hleaf q r b hrep states hstates

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Curvature
attribute [-instance] _root_.OAI.EditApproximation.physicalFamilyRange_neZero
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cost-weighted curvature

Finite weighted variance and the local energy telescope from Section 6
of the edit-distance manuscript. Zero child masses are allowed, with the
length-gap invariant forcing their length gaps to vanish.
-/

namespace EditApproximation

open Finset

theorem weighted_variance_identity {ι : Type*} (children : Finset ι)
    (mass gap : ι → ℝ)
    (hzero : ∀ i ∈ children, mass i = 0 → gap i = 0)
    (hW : 0 < ∑ i ∈ children, mass i) :
    (∑ i ∈ children, gap i ^ 2 / mass i) -
        (∑ i ∈ children, gap i) ^ 2 / (∑ i ∈ children, mass i) =
      ∑ i ∈ children,
        (gap i - ((∑ j ∈ children, gap j) / (∑ j ∈ children, mass j)) * mass i) ^ 2 /
          mass i := by
  let v := (∑ i ∈ children, gap i) / (∑ i ∈ children, mass i)
  have hterm (i : ι) (hi : i ∈ children) :
      (gap i - v * mass i) ^ 2 / mass i =
        gap i ^ 2 / mass i - 2 * v * gap i + v ^ 2 * mass i := by
    by_cases hz : mass i = 0
    · simp only [hz, hzero i hi hz, mul_zero, zero_pow (by omega : 2 ≠ 0),
        zero_div, sub_self, zero_add]
    · field_simp
      ring
  have hsum := sum_congr rfl hterm
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum] at hsum
  rw [hsum]
  dsimp [v]
  field_simp
  ring

theorem curvature_nonneg {ι : Type*} (children : Finset ι)
    (mass gap : ι → ℝ)
    (hmass : ∀ i ∈ children, 0 ≤ mass i)
    (hzero : ∀ i ∈ children, mass i = 0 → gap i = 0)
    (hW : 0 < ∑ i ∈ children, mass i) :
    0 ≤ (∑ i ∈ children, gap i ^ 2 / mass i) -
      (∑ i ∈ children, gap i) ^ 2 / (∑ i ∈ children, mass i) := by
  rw [weighted_variance_identity children mass gap hzero hW]
  exact sum_nonneg fun i hi => div_nonneg (sq_nonneg _) (hmass i hi)

/-- The parent/rounded-parent energy discrepancy is controlled by endpoint
movement and the negative part of the parent-minus-child mass discrepancy. -/
theorem local_energy_discrepancy {parentMass childMass parentGap roundedGap movement : ℝ}
    (hp : 0 < parentMass) (hc : 0 < childMass)
    (hparent : |parentGap| ≤ parentMass)
    (hchild : |roundedGap| ≤ childMass)
    (hmove : |parentGap - roundedGap| ≤ movement)
    (hsmall : movement ≤ parentMass) :
    parentGap ^ 2 / parentMass - roundedGap ^ 2 / childMass ≤
      3 * movement + 2 * max (childMass - parentMass) 0 := by
  have he : 0 ≤ movement := (abs_nonneg _).trans hmove
  have hrounded : |roundedGap| ≤ 2 * parentMass := by
    have ht := abs_add_le parentGap (roundedGap - parentGap)
    have hdiff : |roundedGap - parentGap| ≤ movement := by
      simpa only [abs_sub_comm] using hmove
    have hid : parentGap + (roundedGap - parentGap) = roundedGap := by ring
    rw [hid] at ht
    linarith
  have hsum : |parentGap + roundedGap| ≤ 3 * parentMass :=
    (abs_add_le _ _).trans (by linarith)
  have hnum : parentGap ^ 2 - roundedGap ^ 2 ≤ 3 * movement * parentMass := by
    have hfactor : parentGap ^ 2 - roundedGap ^ 2 =
        (parentGap - roundedGap) * (parentGap + roundedGap) := by ring
    rw [hfactor]
    apply (le_abs_self _).trans
    rw [abs_mul]
    have hmul := mul_le_mul hmove hsum (abs_nonneg _) he
    nlinarith
  have hfirst : (parentGap ^ 2 - roundedGap ^ 2) / parentMass ≤ 3 * movement :=
    (div_le_iff₀ hp).2 hnum
  have hsecond : roundedGap ^ 2 * (childMass - parentMass) / (parentMass * childMass) ≤
      2 * max (childMass - parentMass) 0 := by
    by_cases hle : childMass ≤ parentMass
    · have hnumle : roundedGap ^ 2 * (childMass - parentMass) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)
      have hdivle := div_nonpos_of_nonpos_of_nonneg hnumle (mul_pos hp hc).le
      exact hdivle.trans (by positivity)
    · have hdiff : 0 ≤ childMass - parentMass := by linarith
      have hsq : roundedGap ^ 2 ≤ 2 * parentMass * childMass := by
        have hmul := mul_le_mul hrounded hchild (abs_nonneg _) (by positivity)
        simpa only [← pow_two, sq_abs] using hmul
      rw [max_eq_left hdiff]
      apply (div_le_iff₀ (mul_pos hp hc)).2
      have hmul := mul_le_mul_of_nonneg_right hsq hdiff
      nlinarith
  have hid : parentGap ^ 2 / parentMass - roundedGap ^ 2 / childMass =
      (parentGap ^ 2 - roundedGap ^ 2) / parentMass +
        roundedGap ^ 2 * (childMass - parentMass) / (parentMass * childMass) := by
    field_simp
    ring
  rw [hid]
  linarith

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedComparisonBand
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The comparison band uses the computed numerical parameters, with its error budget proved. -/

namespace EditApproximation

open Finset

theorem comparisonActionCurvature_nonneg {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (parent : TargetInterval source.length)
    (r : TargetInterval target.length) (comparison : Fin M → TargetInterval target.length)
    (child : Fin M → TargetInterval target.length → ℝ)
    (hgap : ∀ i, |stateLengthGap
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i)| ≤
        child i (comparison i))
    (hzero : endpointActionConnection r comparison = 0)
    (hW : 0 < comparisonActionMass comparison child) :
    0 ≤ comparisonActionCurvature source target parent r comparison child := by
  let mass := fun i => child i (comparison i)
  let gap := fun i => stateLengthGap
    (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i)
  have hmass (i : Fin M) : 0 ≤ mass i := (abs_nonneg _).trans (hgap i)
  have hzeroMass (i : Fin M) (hi : mass i = 0) : gap i = 0 := by
    have h := hgap i
    change |gap i| ≤ mass i at h
    rw [hi] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  have hsum := zero_connection_gap_sum source target hM parent r comparison hzero
  have h := curvature_nonneg univ mass gap (fun i _ => hmass i) (fun i _ => hzeroMass i) hW
  dsimp only [mass, gap] at h
  rw [hsum] at h
  exact h

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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSubtreeMass
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual original-table warmup masses below an arbitrary physical node. -/

namespace EditApproximation

open Finset

section Warmup

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (root : PhysicalNode M J) (rootQ : TargetInterval target.length)

local notation "mass" => subtreeComparisonMass source target hM U N P F A hP T root rootQ
local notation "energy" => subtreeComparisonEnergy source target hM U N P F A hP T root rootQ
local notation "frontier" => comparisonFrontier source target hM P hP
  (some (physicalSourceInterval source.length root, rootQ))

 theorem subtreeComparisonMass_step_stopped (d : ℕ) (path : TreeLayer M d)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (heq : frontier d path = some (parent, q)) (hstop : comparisonStopped source target parent q) :
    (∑ i : Fin M, mass (d + 1) (path, i)) = mass d path := by
  classical
  unfold subtreeComparisonMass comparisonSubtreeLift
  have hpoint (i : Fin M) :
      stoppedComparisonValue source target
        (if hd : root.1.val + (d + 1) ≤ J then fun q => (stageWarmupMass source target U N P F A T
          (physicalSubtreeNode root (d + 1) (path, i) hd, q) : ℝ) else fun _ => 0)
        (frontier (d + 1) (path, i)) =
      if i = ⟨0, hM⟩ then (stateEditCost (substring source parent.lo parent.hi) target q : ℝ) else 0 := by
    change stoppedComparisonValue source target _
      (comparisonStep source target hM P hP (frontier d path) i) = _
    rw [heq]
    simp only [comparisonStep, dite_eq_left hstop]
    split_ifs <;> simp only [stoppedComparisonValue, ite_eq_left hstop]
  simp_rw [hpoint]
  rw [heq]
  simp only [sum_ite_eq', mem_univ, ite_true, if_true, stoppedComparisonValue, ite_eq_left hstop]

 theorem subtreeComparisonEnergy_step_stopped (d : ℕ) (path : TreeLayer M d)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (heq : frontier d path = some (parent, q)) (hstop : comparisonStopped source target parent q) :
    (∑ i : Fin M, energy (d + 1) (path, i)) = energy d path := by
  classical
  unfold subtreeComparisonEnergy subtreeComparisonMass comparisonSubtreeLift
  have hpoint (i : Fin M) :
      (comparisonStateGap source target (frontier (d + 1) (path, i))) ^ 2 /
        stoppedComparisonValue source target
          (if hd : root.1.val + (d + 1) ≤ J then fun q => (stageWarmupMass source target U N P F A T
            (physicalSubtreeNode root (d + 1) (path, i) hd, q) : ℝ) else fun _ => 0)
          (frontier (d + 1) (path, i)) =
      if i = ⟨0, hM⟩ then (stateLengthGap (substring source parent.lo parent.hi) target q) ^ 2 /
        stateEditCost (substring source parent.lo parent.hi) target q else 0 := by
    change (comparisonStateGap source target (comparisonStep source target hM P hP (frontier d path) i)) ^ 2 /
      stoppedComparisonValue source target _ (comparisonStep source target hM P hP (frontier d path) i) = _
    rw [heq]
    simp only [comparisonStep, dite_eq_left hstop]
    split_ifs <;> simp only [comparisonStateGap, stoppedComparisonValue, ite_eq_left hstop,
      zero_pow (by decide : 2 ≠ 0), zero_div]
  simp_rw [hpoint]
  rw [heq]
  simp only [sum_ite_eq', mem_univ, ite_true, if_true, comparisonStateGap, stoppedComparisonValue, ite_eq_left hstop]

 theorem subtreeComparison_step_none (d : ℕ) (path : TreeLayer M d) (heq : frontier d path = none) :
    mass d path = 0 ∧ (∑ i : Fin M, mass (d + 1) (path, i)) = 0 ∧
      energy d path = 0 ∧ (∑ i : Fin M, energy (d + 1) (path, i)) = 0 := by
  have hnext (i : Fin M) : frontier (d + 1) (path, i) = none := by
    change comparisonStep source target hM P hP (frontier d path) i = none
    rw [heq]
    rfl
  simp only [subtreeComparisonEnergy, subtreeComparisonMass, comparisonSubtreeLift, heq, hnext,
    comparisonStateGap, stoppedComparisonValue, zero_pow (by decide : 2 ≠ 0), zero_div,
    sum_const_zero, and_self]

include hsize hF hA hseed hT in
 theorem subtreeComparisonMass_step_active (d : ℕ) (path : TreeLayer M d)
    (hd : root.1.val + d < J) (q : TargetInterval target.length)
    (heq : frontier d path = some (physicalSourceInterval source.length (physicalSubtreeNode root d path hd.le), q))
    (hactive : ¬ comparisonStopped source target
      (physicalSourceInterval source.length (physicalSubtreeNode root d path hd.le)) q)
    (i : Fin M) :
    let node := physicalSubtreeNode root d path hd.le
    let hc : 0 < stateEditCost (physicalSource source node) target q := by
      change 0 < stateEditCost (substring source (physicalSourceInterval source.length node).lo
        (physicalSourceInterval source.length node).hi) target q
      dsimp only [node]
      unfold comparisonStopped at hactive
      omega
    mass (d + 1) (path, i) = stageWarmupMass source target U N P F A T
      (physicalChild node hd i, comparisonChildren source target hM P hP
        (physicalSourceInterval source.length node) q hc i) := by
  exact comparisonSubtreeLift_step_active source target hM P hP _
    (fun node q hstop => by
      exact_mod_cast stageWarmupMass_at_stopped source target hM U N P F A hsize hP hF hA hseed
        T hT node q hstop) root rootQ d path hd q heq hactive i

include hsize hF hA hseed hT in
 theorem subtreeComparisonEnergy_step_active (d : ℕ) (path : TreeLayer M d)
    (hd : root.1.val + d < J) (q : TargetInterval target.length)
    (heq : frontier d path = some (physicalSourceInterval source.length (physicalSubtreeNode root d path hd.le), q))
    (hactive : ¬ comparisonStopped source target
      (physicalSourceInterval source.length (physicalSubtreeNode root d path hd.le)) q)
    (i : Fin M) :
    let node := physicalSubtreeNode root d path hd.le
    let hc : 0 < stateEditCost (physicalSource source node) target q := by
      change 0 < stateEditCost (substring source (physicalSourceInterval source.length node).lo
        (physicalSourceInterval source.length node).hi) target q
      dsimp only [node]
      unfold comparisonStopped at hactive
      omega
    let childQ := comparisonChildren source target hM P hP (physicalSourceInterval source.length node) q hc i
    energy (d + 1) (path, i) =
      (stateLengthGap (physicalSource source (physicalChild node hd i)) target childQ) ^ 2 /
        (stageWarmupMass source target U N P F A T (physicalChild node hd i, childQ) : ℝ) := by
  dsimp only
  unfold subtreeComparisonEnergy
  rw [subtreeComparisonMass_step_active source target hM U N P F A hsize hP hF hA hseed T hT root rootQ
    d path hd q heq hactive i]
  change (comparisonStateGap source target (comparisonStep source target hM P hP
    (frontier d path) i)) ^ 2 / _ = _
  rw [heq]
  simp only [comparisonStep, dite_eq_right hactive, comparisonStateGap]
  rfl

end Warmup

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalWarmupSlack
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging the actual physical wide Bellman recurrence bounds its exact Z slack. -/

namespace EditApproximation

open Finset

theorem physicalWarmup_average_wide_slack {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (T : ℕ) (hT : 0 < T) (node : PhysicalNode M J)
    (hbelow : node.1.val < J) (hleaf : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1)
    (q r : TargetInterval target.length) (b : ℕ)
    (hrep : (b, r) ∈ representatives node)
    (hnonempty : wideActionList M (physicalSourceInterval source.length node) r b P ≠ [])
    (hfinal : 0 ≤ physicalWarmup source target P L initial representatives T (node, q)) :
    physicalWarmupAverage source target P L initial representatives T (node, q) -
      wideActionMinimum (physicalSourceInterval source.length node) r b P hnonempty
        (fun i s => physicalWarmupAverage source target P L initial representatives T
          (physicalChild node hbelow i, s)) ≤
      L * targetEndpointDistance q r + initial (node, q) / T := by
  let child := fun i s => physicalWarmupAverage source target P L initial representatives T
    (physicalChild node hbelow i, s)
  let parent := physicalWarmupAverage source target P L initial representatives T (node, q)
  have hTr : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hcorrection : (initial (node, q) -
      physicalWarmup source target P L initial representatives T (node, q)) / T ≤
      initial (node, q) / T :=
    div_le_div_of_nonneg_right (sub_le_self _ hfinal) hTr
  have haction (states : Fin M → TargetInterval target.length)
      (hstates : states ∈ wideActionList M (physicalSourceInterval source.length node) r b P) :
      parent - L * targetEndpointDistance q r - initial (node, q) / T ≤
        endpointActionValue r states child := by
    have h := physicalWarmup_average_action_bound source target P L initial representatives
      T hT node hbelow hleaf q r b hrep states hstates
    dsimp only [parent, child, endpointActionValue]
    linarith only [h, hcorrection]
  have hlower : parent - L * targetEndpointDistance q r - initial (node, q) / T ≤
      wideActionMinimum (physicalSourceInterval source.length node) r b P hnonempty child := by
    apply (le_finiteMinimum_iff _ _ _).2
    constructor
    · exact haction _ (List.head_mem hnonempty)
    · intro value hvalue
      obtain ⟨states, hstates, rfl⟩ := List.mem_map.mp hvalue
      exact haction states hstates
  change parent - wideActionMinimum _ _ _ _ hnonempty child ≤ _
  linarith only [hlower]

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

theorem stageWarmup_comparison_slack {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (hM : 0 < M)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (hT : 0 < T) (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (hleaf : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1)
    (q : TargetInterval target.length)
    (hc : 0 < stateEditCost (physicalSource source node) target q) :
    let parent := physicalSourceInterval source.length node
    let b := 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
    let r := roundInterval (seedGridSpacing b P) q
    ∀ hnonempty : wideActionList M parent r b P ≠ [],
      (stageWarmupMass source target U N P F A T (node, q) : ℝ) -
        wideActionMinimum parent r b P hnonempty
          (fun i s => (stageWarmupMass source target U N P F A T (physicalChild node hbelow i, s) : ℝ)) ≤
      (128 * (F : ℝ)) * targetEndpointDistance q r + (stageInitial source target U N P F A (node, q) : ℝ) / T := by
  dsimp only
  intro hnonempty
  have hrep := stageRounded_representative_mem source target U N P F A hsize hP hF hA hseed node q hc
  have hinvariants := stageWarmup_invariants source target hM U N P F A hsize hP hF hA hseed T hT (node, q)
  have hfinal : 0 ≤ (stageWarmup source target U N P F A T (node, q) : ℝ) :=
    (abs_nonneg _).trans ((le_max_right _ _).trans hinvariants.1)
  simp only [stageWarmup, rationalPhysicalWarmup_cast] at hfinal
  have h := physicalWarmup_average_wide_slack source target P ((128 * F : ℚ) : ℝ)
    (fun s => (stageInitial source target U N P F A s : ℝ))
    (stageRepresentatives source target U N P F A) T hT node hbelow hleaf q _ _ hrep hnonempty hfinal
  simp only [stageWarmupMass, rationalPhysicalWarmupAverage_cast]
  simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using h

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_StageComparisonEnergy
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual averaged warmup supplies the local mass and energy charges. -/

namespace EditApproximation

open Finset

theorem stateLengthGap_difference {α : Type*} (source target : List α)
    (q r : TargetInterval target.length) :
    |stateLengthGap source target q - stateLengthGap source target r| ≤
      (targetEndpointDistance q r : ℝ) := by
  have hid : stateLengthGap source target q - stateLengthGap source target r =
      ((q.hi : ℝ) - r.hi) - ((q.lo : ℝ) - r.lo) := by
    unfold stateLengthGap
    ring
  rw [hid]
  have h := abs_sub ((q.hi : ℝ) - r.hi) ((q.lo : ℝ) - r.lo)
  rw [natural_distance_cast, natural_distance_cast] at h
  simpa only [targetEndpointDistance, Nat.cast_add, add_comm] using h

section Stage

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (q : TargetInterval target.length)
  (hc : 0 < stateEditCost (physicalSource source node) target q)

include hsize hF hA hseed hT in
/-- No local energy or discrepancy hypothesis is assumed: these are the
charges of the input-determined comparison children and the actual warmup. -/
theorem stageComparison_energy
    (hleaf : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1)
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) :
    let parent := physicalSourceInterval source.length node
    let b := 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
    let r := roundInterval (seedGridSpacing b P) q
    let action := comparisonChildren source target hM P hP parent q hc
    let child := fun i s => (stageWarmupMass source target U N P F A T (physicalChild node hbelow i, s) : ℝ)
    let mp := (stageWarmupMass source target U N P F A T (node, q) : ℝ)
    let W := comparisonActionMass action child
    let K := comparisonActionCurvature source target parent r action child
    let energy := (stateLengthGap (physicalSource source node) target q) ^ 2 / mp
    ∃ hnonempty : wideActionList M parent r b P ≠ [],
      let Z := wideActionMinimum parent r b P hnonempty child
      0 ≤ K ∧ 0 ≤ W - Z ∧
      mp - W + (W - Z) ≤
        (128 * (F : ℝ)) * targetEndpointDistance q r +
          (stageInitial source target U N P F A (node, q) : ℝ) / T ∧
      K ≤ ((∑ i, (stateLengthGap (physicalSource source (physicalChild node hbelow i)) target
          (action i)) ^ 2 / child i (action i)) - energy) +
        3 * targetEndpointDistance q r + 2 * max (-(mp - W)) 0 := by
  dsimp only
  let parent := physicalSourceInterval source.length node
  let b := 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
  let r := roundInterval (seedGridSpacing b P) q
  let action := comparisonChildren source target hM P hP parent q hc
  let child := fun i s => (stageWarmupMass source target U N P F A T (physicalChild node hbelow i, s) : ℝ)
  let mp := (stageWarmupMass source target U N P F A T (node, q) : ℝ)
  let W := comparisonActionMass action child
  let K := comparisonActionCurvature source target parent r action child
  have hspec := comparisonChildren_spec source target hM P hP parent q hc
  have hzero : endpointActionConnection r action = 0 := hspec.2.1
  have hnonempty : wideActionList M parent r b P ≠ [] := by
    intro heq
    have hmem := hspec.1
    change action ∈ wideActionList M parent r b P at hmem
    rw [heq] at hmem
    exact List.not_mem_nil hmem
  let Z := wideActionMinimum parent r b P hnonempty child
  have ha : (1 : ℝ) ≤ refinementFactor A F := by
    simpa only [Rat.cast_one] using (Rat.cast_le (K := ℝ)).mpr (refinementFactor_spec A F (by omega)).1
  have hlower := stageWarmupMass_child_lower source target hM U N P F A hsize hP hF hA hseed T hT node hbelow
  have hZlower := wideActionMinimum_lower source target hM parent r b P hnonempty
    (refinementFactor A F : ℝ) ha child hlower
  have hpositive := stageComparison_positive_movement source target hM U N P F A hsize hP hF hA hseed
    T hT node q hc hscale
  have hcr : (0 : ℝ) < stateEditCost (physicalSource source node) target r := by exact_mod_cast hpositive.1
  have hZpos : 0 < Z := (div_pos hcr (by linarith only [ha])).trans_le ((le_max_left _ _).trans hZlower)
  have hZW : Z ≤ W := by
    have h := wideActionMinimum_le_member parent r hnonempty child action hspec.1
    simpa only [Z, W, comparisonActionMass, endpointActionValue, hzero, Nat.cast_zero, zero_add] using h
  have hWpos : 0 < W := hZpos.trans_le hZW
  have hgap (i : Fin M) : |stateLengthGap (physicalSource source (physicalChild node hbelow i)) target
      (action i)| ≤ child i (action i) := (le_max_right _ _).trans (hlower i (action i))
  have hK := comparisonActionCurvature_nonneg source target hM parent r action child hgap hspec.2.1 hWpos
  have hinv := stageWarmup_invariants source target hM U N P F A hsize hP hF hA hseed T hT (node, q)
  have hparentGap : |stateLengthGap (physicalSource source node) target q| ≤ mp :=
    ((le_max_right _ _).trans hinv.1).trans (Rat.cast_le.mpr hinv.2.1)
  have hmp : 0 < mp := by
    have hcR : (0 : ℝ) < stateEditCost (physicalSource source node) target q := by exact_mod_cast hc
    have h := ((le_max_left _ _).trans hinv.1).trans (Rat.cast_le.mpr hinv.2.1)
    exact (div_pos hcR (by linarith only [ha])).trans_le h
  have hroundedGap : |stateLengthGap (physicalSource source node) target r| ≤ W :=
    ((le_max_right _ _).trans hZlower).trans hZW
  have henergy := local_energy_discrepancy hmp hWpos hparentGap hroundedGap
    (stateLengthGap_difference (physicalSource source node) target q r) hpositive.2
  have hslack := stageWarmup_comparison_slack source target hM U N P F A hsize hP hF hA hseed
    T hT node hbelow hleaf q hc hnonempty
  refine ⟨hnonempty, hK, sub_nonneg.mpr hZW, ?_, ?_⟩
  · change mp - W + (W - Z) ≤ _
    change mp - Z ≤ _ at hslack
    linarith only [hslack]
  · let Echild := ∑ i, (stateLengthGap (physicalSource source (physicalChild node hbelow i)) target
        (action i)) ^ 2 / child i (action i)
    change Echild - (stateLengthGap (physicalSource source node) target r) ^ 2 / W ≤
      (Echild - (stateLengthGap (physicalSource source node) target q) ^ 2 / mp) +
        3 * (targetEndpointDistance q r : ℝ) + 2 * max (-(mp - W)) 0
    have hid : -(mp - W) = W - mp := by ring
    rw [hid]
    linarith only [henergy]

end Stage

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSubtreeCharges
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
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
  (T : ℕ) (hT : 0 < T) (root : PhysicalNode M J) (K : ℕ)
  (hheight : root.1.val + K = J) (rootQ : TargetInterval target.length)

local notation "mass" => subtreeComparisonMass source target hM U N P F A hP T root rootQ
local notation "energy" => subtreeComparisonEnergy source target hM U N P F A hP T root rootQ
local notation "frontier" => comparisonFrontier source target hM P hP
  (some (physicalSourceInterval source.length root, rootQ))

include hsize hF hA hseed hT in
 theorem subtreeComparisonCharges_local_oai (hscale : 2 * (refinementFactor A F : ℝ) ≤ P)
    (d : Fin K) (path : TreeLayer M d.val) :
    let charges := subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ d path
    let R := mass d.val path - ∑ i : Fin M, mass (d.val + 1) (path, i)
    let E := (∑ i : Fin M, energy (d.val + 1) (path, i)) - energy d.val path
    let movement := comparisonMovement source target P (frontier d.val path)
    let cost := comparisonActiveCost source target (frontier d.val path)
    0 ≤ charges.1 ∧ 0 ≤ charges.2 ∧
      R + charges.2 ≤ (128 * (F : ℝ)) * movement + (2 * F / (T : ℝ)) * cost ∧
      charges.1 ≤ E + 3 * movement + 2 * max (-R) 0 := by
  classical
  dsimp only
  generalize heq : frontier d.val path = state
  cases state with
  | none =>
    have hzero := subtreeComparison_step_none source target hM U N P F A hP T root rootQ d.val path heq
    have hcharges : subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ d path = (0, 0) := by
      unfold subtreeComparisonCharges
      rw [heq]
    rw [hcharges, hzero.1, hzero.2.1, hzero.2.2.1, hzero.2.2.2]
    simp only [comparisonMovement, comparisonActiveCost, sub_self, neg_zero, max_self,
      mul_zero, add_zero, le_refl, and_self]
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hstop : comparisonStopped source target parent q
    · have hm := subtreeComparisonMass_step_stopped source target hM U N P F A hP T root rootQ d.val path parent q heq hstop
      have he := subtreeComparisonEnergy_step_stopped source target hM U N P F A hP T root rootQ d.val path parent q heq hstop
      have hcharges : subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ d path = (0, 0) := by
        unfold subtreeComparisonCharges
        rw [heq]
        simp only [dite_eq_left hstop]
      rw [hcharges, hm, he]
      simp only [comparisonMovement, comparisonActiveCost, ite_eq_left hstop, sub_self, neg_zero,
        max_self, mul_zero, add_zero, le_refl, and_self]
    · have hp := comparisonSubtree_active_source source target hM P hP root rootQ d.val path parent q heq hstop
      subst parent
      let node : PhysicalNode M J := physicalSubtreeNode root d.val path (by omega)
      have hbelow : node.1.val < J := by dsimp only [node, physicalSubtreeNode]; omega
      have hc : 0 < stateEditCost (physicalSource source node) target q := by
        change 0 < stateEditCost (substring source (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).lo
          (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).hi) target q
        unfold comparisonStopped at hstop
        omega
      have hleaf : ¬ (physicalSourceInterval source.length node).hi -
          (physicalSourceInterval source.length node).lo ≤ 1 := fun h => hstop (Or.inl h)
      let b := 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
      let r := roundInterval (seedGridSpacing b P) q
      let action := comparisonChildren source target hM P hP (physicalSourceInterval source.length node) q hc
      let child := fun i s => (stageWarmupMass source target U N P F A T (physicalChild node hbelow i, s) : ℝ)
      let mp := (stageWarmupMass source target U N P F A T (node, q) : ℝ)
      let W := comparisonActionMass action child
      let curvature := comparisonActionCurvature source target (physicalSourceInterval source.length node) r action child
      obtain ⟨hnonempty, hK, hG, hslack, henergy⟩ :=
        stageComparison_energy source target hM U N P F A hsize hP hF hA hseed T hT node hbelow q hc hleaf hscale
      let Z := wideActionMinimum (physicalSourceInterval source.length node) r b P hnonempty child
      have hcharges : subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ d path = (curvature, W - Z) := by
        unfold subtreeComparisonCharges
        rw [heq]
        dsimp only
        rw [dite_eq_right hstop]
        rfl
      have hparent : mass d.val path = mp := by
        unfold subtreeComparisonMass comparisonSubtreeLift
        rw [dite_eq_left (by omega : root.1.val + d.val ≤ J), heq]
        simp only [stoppedComparisonValue, ite_eq_right hstop]
        rfl
      have hchild (i : Fin M) : mass (d.val + 1) (path, i) = child i (action i) :=
        subtreeComparisonMass_step_active source target hM U N P F A hsize hP hF hA hseed T hT root rootQ
          d.val path (by omega) q heq hstop i
      have hparentEnergy : energy d.val path = (stateLengthGap (physicalSource source node) target q) ^ 2 / mp := by
        unfold subtreeComparisonEnergy
        rw [heq, hparent]
        rfl
      have hchildEnergy (i : Fin M) : energy (d.val + 1) (path, i) =
          (stateLengthGap (physicalSource source (physicalChild node hbelow i)) target (action i)) ^ 2 /
            child i (action i) :=
        subtreeComparisonEnergy_step_active source target hM U N P F A hsize hP hF hA hseed T hT root rootQ
          d.val path (by omega) q heq hstop i
      rw [hcharges, hparent, hparentEnergy]
      simp_rw [hchild, hchildEnergy]
      simp only [comparisonMovement, comparisonActiveCost, ite_eq_right hstop]
      change 0 ≤ curvature ∧ 0 ≤ W - Z ∧
        mp - W + (W - Z) ≤ (128 * (F : ℝ)) * targetEndpointDistance q r +
          (2 * F / (T : ℝ)) * stateEditCost (physicalSource source node) target q ∧
        curvature ≤ ((∑ i, (stateLengthGap (physicalSource source (physicalChild node hbelow i)) target
          (action i)) ^ 2 / child i (action i)) -
            (stateLengthGap (physicalSource source node) target q) ^ 2 / mp) +
              3 * targetEndpointDistance q r + 2 * max (-(mp - W)) 0
      have hu := (stageWarmup_invariants source target hM U N P F A hsize hP hF hA hseed T hT (node, q)).2.2.2
      have huR : (stageInitial source target U N P F A (node, q) : ℝ) ≤
          2 * F * stateEditCost (physicalSource source node) target q := by exact_mod_cast hu
      have hdiv := div_le_div_of_nonneg_right huR (Nat.cast_nonneg (α := ℝ) T)
      have hid : (2 * (F : ℝ) * stateEditCost (physicalSource source node) target q) / T =
          (2 * F / (T : ℝ)) * stateEditCost (physicalSource source node) target q := by ring
      rw [hid] at hdiv
      exact ⟨hK, hG, hslack.trans (add_le_add_right hdiv _), henergy⟩

end Stage

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.subtreeComparisonCharges_local_oai.{u_1} := @OAI.EditApproximation.subtreeComparisonCharges_local_oai.{u_1}
