-- Prove2me | solution 1 for OAI.EditApproximation.physicalNode_firstCrossing_regret
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:45:31.155681+00:00
-- url     : https://prove2.me/submissions/135cc49b-9fd1-472c-855b-02dc36dffa26

import Mathlib
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_physicalRefinement_stage_bounds
import Theorems.Thm_OAI_EditApproximation_rationalPhysicalWarmup_cast
import Theorems.Thm_OAI_EditApproximation_stageWarmup_postfixed

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

theorem finiteBellman_spatial {Parent Child : Type*} {M : ℕ}
    (fallback : Parent → ℝ) (distance : Parent → Parent → ℝ) (L : ℝ)
    (actions : List (BellmanAction Parent Child M)) (child : Child → ℝ)
    (hL : 0 ≤ L) (query query' : Parent)
    (hfallback : fallback query ≤ fallback query' + L * distance query query')
    (htriangle : ∀ center, distance query center ≤ distance query' center + distance query query') :
    finiteBellman fallback distance L actions child query ≤
      finiteBellman fallback distance L actions child query' + L * distance query query' := by
  apply finiteMinimum_map_spatial _ _ _ _ _ _ hfallback
  intro action _
  have hdist := mul_le_mul_of_nonneg_left (htriangle action.center) hL
  dsimp [bellmanActionValue]
  linarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Cones
attribute [-instance] _root_.OAI.EditApproximation.physicalFamilyRange_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scalar steps of the refinement update

These are the min/max and first-crossing calculations in Sections 5 and 7
of *An Almost-Linear Approximation Scheme for Edit Distance* (2026).
They are internal lemmas, not the main algorithmic theorem.
-/

namespace EditApproximation

/-- Prefix step of Proposition `prop:node-regret`: if the group estimate
succeeds, any excess over the sampled action is paid by its decrement. -/
theorem refinementUpdate_prefix {δ κ cone online action oldAction b c error : ℝ}
    (hδ : 0 < δ) (hκ : 0 ≤ κ) (hc0 : 0 ≤ c) (hb : b ≤ c)
    (hc : c ≤ action) (hmonotone : action ≤ oldAction)
    (honline : online ≤ action) (hbellman : cone ≤ oldAction)
    (hgroup : cone ≤ (1 + δ) * action + error * b)
    (herror : error * b ≤ κ * δ * b) :
    max c (refinementUpdate δ cone online) ≤
      action + κ * (oldAction - action) := by
  apply max_le (by nlinarith) _
  by_cases hu : refinementUpdate δ cone online ≤ action
  · nlinarith
  · have hact : action < refinementUpdate δ cone online := lt_of_not_ge hu
    have hdiv : action < cone / (1 + δ) := by
      have hmax : action < max (cone / (1 + δ)) online :=
        hact.trans_le (min_le_right _ _)
      exact (lt_max_iff.mp hmax).resolve_right (not_lt_of_ge honline)
    have hcone : (1 + δ) * action < cone := by
      have := (lt_div_iff₀ (by positivity : 0 < 1 + δ)).1 hdiv
      nlinarith
    have hdecrement : δ * b < oldAction - action := by
      nlinarith
    have hcone0 : 0 ≤ cone :=
      (mul_nonneg (by positivity : 0 ≤ 1 + δ) (hc0.trans hc)).trans hcone.le
    have hdivle : cone / (1 + δ) ≤ cone := by
      apply (div_le_iff₀ (by positivity : 0 < 1 + δ)).2
      nlinarith
    have heq : refinementUpdate δ cone online = cone / (1 + δ) := by
      rw [refinementUpdate, max_eq_left (honline.trans hdiv.le)]
      exact min_eq_right hdivle
    rw [heq]
    apply (div_le_iff₀ (by positivity : 0 < 1 + δ)).2
    have hpay : κ * δ * b ≤ κ * (oldAction - action) :=
      by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hdecrement.le hκ
    have hslack : 0 ≤ δ * (κ * (oldAction - action)) :=
      mul_nonneg hδ.le (mul_nonneg hκ (sub_nonneg.mpr hmonotone))
    nlinarith

/-- The crossing iteration is paid once; later Bellman bounds use the
same action and make the clipped regret nonpositive. -/
theorem refinementUpdate_crossing {δ cone online action c : ℝ}
    (hδ : 0 ≤ δ) (hc : 0 ≤ c) (haction : action < c)
    (hgroup : cone ≤ (1 + δ) * action + δ * c) :
    max c (refinementUpdate δ cone online) ≤ c + 2 * δ * c := by
  have hup : refinementUpdate δ cone online ≤ cone := min_le_left _ _
  have hmul := mul_le_mul_of_nonneg_left haction.le (by positivity : 0 ≤ 1 + δ)
  apply max_le <;> nlinarith

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



theorem rationalRefinementUpdate_cast (δ cone online : ℚ) :
    (rationalRefinementUpdate δ cone (some online) : ℝ) =
      refinementUpdate (δ : ℝ) (cone : ℝ) (online : ℝ) := by
  simp only [rationalRefinementUpdate, refinementUpdate, Rat.cast_min, Rat.cast_max,
    Rat.cast_div, Rat.cast_add, Rat.cast_one]

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PrefixCosts
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite prefix costs used by the predicted bands

A prefix is a restriction of an enumerated wide action. The last jump is
evaluated at the proposed real shift. Taking the minimum over the actual
finite list, with its first member duplicated as the fallback, gives the
exact prefix minimum and its 1-Lipschitz property.
-/

namespace EditApproximation

open Finset

theorem realConnectionBudget_finish_lipschitz {n : ℕ} (start : ℝ)
    (states : List (TargetInterval n)) (finish finish' : ℝ) :
    |realConnectionBudget start states finish - realConnectionBudget start states finish'| ≤
      |finish - finish'| := by
  induction states generalizing start with
  | nil =>
    have h := abs_abs_sub_abs_le_abs_sub (start - finish) (start - finish')
    have heq : start - finish - (start - finish') = -(finish - finish') := by ring
    simpa only [realConnectionBudget, heq, abs_neg] using h
  | cons state rest ih =>
    have heq : realConnectionBudget start (state :: rest) finish -
        realConnectionBudget start (state :: rest) finish' =
        realConnectionBudget state.hi rest finish - realConnectionBudget state.hi rest finish' := by
      simp only [realConnectionBudget]
      ring
    rw [heq]
    exact ih state.hi

theorem widePrefixCost_lipschitz {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (states : Fin M → TargetInterval ny)
    (child : Fin M → TargetInterval ny → ℝ) (j : ℕ) (p p' : ℝ) :
    |widePrefixCost parent r states child j p - widePrefixCost parent r states child j p'| ≤
      |p - p'| := by
  have h := realConnectionBudget_finish_lipschitz (r.lo : ℝ) ((List.ofFn states).take j)
    ((balancedCut parent.lo (parent.hi - parent.lo) M j : ℝ) + p)
    ((balancedCut parent.lo (parent.hi - parent.lo) M j : ℝ) + p')
  have heq : ((balancedCut parent.lo (parent.hi - parent.lo) M j : ℝ) + p) -
      ((balancedCut parent.lo (parent.hi - parent.lo) M j : ℝ) + p') = p - p' := by ring
  simpa only [widePrefixCost, add_sub_add_right_eq_sub, heq] using h

theorem widePrefixMinimum_lipschitz {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (actions : List (Fin M → TargetInterval ny)) (hnonempty : actions ≠ [])
    (child : Fin M → TargetInterval ny → ℝ) (j : ℕ) (p p' : ℝ) :
    |widePrefixMinimum parent r actions hnonempty child j p -
      widePrefixMinimum parent r actions hnonempty child j p'| ≤ |p - p'| := by
  have hforward (p p' : ℝ) : widePrefixMinimum parent r actions hnonempty child j p ≤
      widePrefixMinimum parent r actions hnonempty child j p' + |p - p'| := by
    apply finiteMinimum_map_spatial
    · have h := widePrefixCost_lipschitz parent r (actions.head hnonempty) child j p p'
      linarith [(abs_le.mp h).2]
    · intro action ha
      have h := widePrefixCost_lipschitz parent r action child j p p'
      linarith [(abs_le.mp h).2]
  exact abs_le.mpr ⟨by have h := hforward p' p; rw [abs_sub_comm p' p] at h; linarith,
    by linarith [hforward p p']⟩

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

theorem connectionPrefixBoundary_ofFn {n M : ℕ} (states : Fin M → TargetInterval n)
    (finish : ℕ) (j : Fin M) :
    connectionPrefixBoundary (List.ofFn states) finish j.val = (states j).lo := by
  simp only [connectionPrefixBoundary, List.head?_drop, List.getElem?_ofFn,
    dite_eq_left j.isLt, Option.map_some, Option.getD_some]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Bands
attribute [-instance] _root_.OAI.EditApproximation.physicalFamilyRange_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Predicted-band geometry

The prefix-cost predictor is 1-Lipschitz, while its velocity has a strict
margin below one. This gives narrow bands without a convexity assumption
on the set of allowed endpoints (Sections 5 and 6 of the manuscript).
-/

namespace EditApproximation

theorem predicted_band_diameter {prefixCost : ℝ → ℝ}
    {origin velocity margin width p q : ℝ}
    (hmargin : 0 < margin) (hvelocity : |velocity| ≤ 1 - margin)
    (hLipschitz : |prefixCost p - prefixCost q| ≤ |p - q|)
    (hp : inPredictedBand prefixCost origin velocity margin width p)
    (hq : inPredictedBand prefixCost origin velocity margin width q) :
    |p - q| ≤ 2 * width := by
  have hid : p - q =
      (p - origin - velocity * prefixCost p) - (q - origin - velocity * prefixCost q) +
        velocity * (prefixCost p - prefixCost q) := by ring
  have htri := (abs_add_le
    ((p - origin - velocity * prefixCost p) - (q - origin - velocity * prefixCost q))
    (velocity * (prefixCost p - prefixCost q))).trans
      (add_le_add (abs_sub _ _) le_rfl)
  rw [← hid, abs_mul] at htri
  have hprod := mul_le_mul hvelocity hLipschitz (abs_nonneg _)
    ((abs_nonneg velocity).trans hvelocity)
  change |p - origin - velocity * prefixCost p| ≤ margin * width at hp
  change |q - origin - velocity * prefixCost q| ≤ margin * width at hq
  have hscaled : margin * |p - q| ≤ margin * (2 * width) := by nlinarith
  exact le_of_mul_le_mul_left hscaled hmargin

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_RationalPrefix
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Rational execution and exact real casts of the finite band predictor. -/

namespace EditApproximation

open Finset



theorem rationalConnectionBudget_cast {n : ℕ} (start finish : ℚ) (states : List (TargetInterval n)) :
    (rationalConnectionBudget start states finish : ℝ) = realConnectionBudget start states finish := by
  induction states generalizing start with
  | nil => simp only [rationalConnectionBudget, realConnectionBudget, Rat.cast_abs, Rat.cast_sub]
  | cons state rest ih =>
    simp only [rationalConnectionBudget, realConnectionBudget, Rat.cast_add, Rat.cast_abs,
      Rat.cast_sub, Rat.cast_natCast, ih]



theorem rationalWidePrefixCost_cast {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (states : Fin M → TargetInterval ny)
    (child : Fin M → TargetInterval ny → ℚ) (j : ℕ) (p : ℚ) :
    (rationalWidePrefixCost parent r states child j p : ℝ) =
      widePrefixCost parent r states (fun i s => (child i s : ℝ)) j p := by
  simp only [rationalWidePrefixCost, widePrefixCost, Rat.cast_add, Rat.cast_sum,
    rationalConnectionBudget_cast, Rat.cast_natCast]
  congr 1
  apply sum_congr rfl
  intro i hi
  split_ifs <;> simp



theorem rationalWidePrefixMinimum_cast {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (actions : List (Fin M → TargetInterval ny)) (hnonempty : actions ≠ [])
    (child : Fin M → TargetInterval ny → ℚ) (j : ℕ) (p : ℚ) :
    (rationalWidePrefixMinimum parent r actions hnonempty child j p : ℝ) =
      widePrefixMinimum parent r actions hnonempty (fun i s => (child i s : ℝ)) j p := by
  rw [rationalWidePrefixMinimum, rationalMinimum_cast]
  simp only [widePrefixMinimum, rationalWidePrefixCost_cast, List.map_map, Function.comp_def]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedBands
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The literal finite predicted band

The band is a rationally decidable filter of the enumerated wide actions.
Its internal-cut diameter follows from the actual finite prefix predictor,
without assuming a predictor Lipschitz contract.
-/

namespace EditApproximation









theorem computedBand_cut_diameter {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (tau theta velocity : ℚ) (htau : 0 < tau)
    (child : Fin M → TargetInterval ny → ℚ) (states states' : Fin M → TargetInterval ny)
    (hstates : states ∈ computedBandActions parent r b P tau theta velocity child)
    (hstates' : states' ∈ computedBandActions parent r b P tau theta velocity child)
    (j : Fin M) (hj : 0 < j.val) :
    (Nat.dist (states j).lo (states' j).lo : ℝ) ≤ 2 * (theta : ℝ) * b / M := by
  obtain ⟨hnonempty, hmem, hvelocity, hpredicate⟩ :=
    computedBandActions_mem parent r b P tau theta velocity child states hstates
  obtain ⟨hnonempty', hmem', hvelocity', hpredicate'⟩ :=
    computedBandActions_mem parent r b P tau theta velocity child states' hstates'
  let predictor := fun p : ℝ => widePrefixMinimum parent r (wideActionList M parent r b P)
    hnonempty (fun i s => (child i s : ℝ)) j.val p
  have hvelocityR : |(velocity : ℝ)| ≤ 1 - (tau : ℝ) := by exact_mod_cast hvelocity
  have htauR : (0 : ℝ) < tau := by exact_mod_cast htau
  have hband (s : Fin M → TargetInterval ny)
      (hs : bandActionPredicate parent r b tau theta velocity (wideActionList M parent r b P) hnonempty child s) :
      inPredictedBand predictor ((r.lo : ℝ) - parent.lo) velocity tau
        ((theta : ℝ) * b / M) (bandCutShift parent s j) := by
    have h := hs.2.2 j hj
    have hR : ((|bandCutShift parent s j - ((r.lo : ℚ) - parent.lo) - velocity *
          rationalWidePrefixMinimum parent r (wideActionList M parent r b P) hnonempty child j.val
            (bandCutShift parent s j)| : ℚ) : ℝ) ≤ ((tau * theta * b / M : ℚ) : ℝ) :=
      Rat.cast_le.mpr h
    simp only [Rat.cast_abs, Rat.cast_sub, Rat.cast_natCast, Rat.cast_mul, Rat.cast_div,
      rationalWidePrefixMinimum_cast] at hR
    simpa only [inPredictedBand, predictor, mul_assoc, mul_div_assoc] using hR
  have hdiam := predicted_band_diameter htauR hvelocityR
    (widePrefixMinimum_lipschitz parent r (wideActionList M parent r b P) hnonempty
      (fun i s => (child i s : ℝ)) j.val _ _)
    (hband states hpredicate) (hband states' hpredicate')
  have hpoint : ((bandCutShift parent states j : ℚ) : ℝ) -
      ((bandCutShift parent states' j : ℚ) : ℝ) = (states j).lo - ((states' j).lo : ℝ) := by
    simp only [bandCutShift, Rat.cast_sub, Rat.cast_natCast]
    ring
  rw [hpoint, natural_distance_cast] at hdiam
  simpa only [mul_div_assoc, mul_assoc] using hdiam

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandGuards
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Literal band endpoint geometry and rounding guards

The full child endpoint diameter follows from the computed internal cuts
and zero connection, including the two outside endpoints.
-/

namespace EditApproximation

open Finset

theorem connectionBudget_zero_head {n : ℕ} (states : List (TargetInterval n))
    (start finish : ℕ) (hzero : connectionBudget start states finish = 0) :
    (states.head?.map TargetInterval.lo).getD start = start := by
  cases states with
  | nil => rfl
  | cons state rest =>
    have hdistance : Nat.dist start state.lo = 0 := by
      change Nat.dist start state.lo + connectionBudget state.hi rest finish = 0 at hzero
      omega
    exact (Nat.eq_of_dist_eq_zero hdistance).symm

/-- Each actual right endpoint is the next actual left endpoint, or the
parent's end when this is the last child. -/
theorem connectionBudget_zero_right {n : ℕ} (states : List (TargetInterval n))
    (start finish : ℕ) (hzero : connectionBudget start states finish = 0)
    (i : ℕ) (hi : i < states.length) :
    states[i].hi = connectionPrefixBoundary states finish (i + 1) := by
  induction states generalizing start i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons state rest ih =>
    have htail : connectionBudget state.hi rest finish = 0 := by
      change Nat.dist start state.lo + connectionBudget state.hi rest finish = 0 at hzero
      omega
    cases i with
    | zero =>
      cases rest with
      | nil =>
        exact Nat.eq_of_dist_eq_zero htail
      | cons next rest =>
        have hdistance : Nat.dist state.hi next.lo = 0 := by
          change Nat.dist state.hi next.lo + connectionBudget next.hi rest finish = 0 at htail
          omega
        exact Nat.eq_of_dist_eq_zero hdistance
    | succ i =>
      have hprev := ih state.hi htail i (by simp only [List.length_cons] at hi; omega)
      simpa only [List.getElem_cons_succ, connectionPrefixBoundary, List.drop_succ_cons] using hprev

theorem zero_connection_left_endpoint {n M : ℕ} (r : TargetInterval n)
    (states : Fin M → TargetInterval n) (hzero : endpointActionConnection r states = 0)
    (i : Fin M) (hi : i.val = 0) : (states i).lo = r.lo := by
  have hhead := connectionBudget_zero_head (List.ofFn states) r.lo r.hi hzero
  have hM : 0 < M := by have := i.isLt; omega
  simp only [List.head?_eq_getElem?, List.getElem?_ofFn, dite_eq_left hM,
    Option.map_some, Option.getD_some] at hhead
  have hequal : (⟨0, hM⟩ : Fin M) = i := Fin.ext hi.symm
  rw [hequal] at hhead
  exact hhead

theorem zero_connection_right_endpoint {n M : ℕ} (r : TargetInterval n)
    (states : Fin M → TargetInterval n) (hzero : endpointActionConnection r states = 0)
    (i : Fin M) :
    (states i).hi = connectionPrefixBoundary (List.ofFn states) r.hi (i.val + 1) := by
  have h := connectionBudget_zero_right (List.ofFn states) r.lo r.hi hzero i.val
    (by simp only [List.length_ofFn]; exact i.isLt)
  rw [List.getElem_ofFn] at h
  exact h

/-- Full endpoint distance, including first/last endpoints, for every two
members of the literal computed band. -/
theorem computedBand_child_endpoint_diameter {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (tau theta velocity : ℚ) (htau : 0 < tau) (htheta : 0 ≤ theta)
    (child : Fin M → TargetInterval ny → ℚ)
    (states states' : Fin M → TargetInterval ny)
    (hstates : states ∈ computedBandActions parent r b P tau theta velocity child)
    (hstates' : states' ∈ computedBandActions parent r b P tau theta velocity child)
    (i : Fin M) :
    (targetEndpointDistance (states i) (states' i) : ℝ) ≤ 4 * (theta : ℝ) * b / M := by
  have hthetaR : (0 : ℝ) ≤ theta := by exact_mod_cast htheta
  have hthetaBound : 0 ≤ 2 * (theta : ℝ) * b / M := by positivity
  obtain ⟨hnonempty, hwide, hv, hpredicate⟩ := computedBandActions_mem parent r b P tau theta velocity child states hstates
  obtain ⟨hnonempty', hwide', hv', hpredicate'⟩ := computedBandActions_mem parent r b P tau theta velocity child states' hstates'
  have hlo : (Nat.dist (states i).lo (states' i).lo : ℝ) ≤ 2 * (theta : ℝ) * b / M := by
    by_cases hi : 0 < i.val
    · exact computedBand_cut_diameter parent r b P tau theta velocity htau child states states' hstates hstates' i hi
    · have hi0 : i.val = 0 := by omega
      rw [zero_connection_left_endpoint r states hpredicate.1 i hi0,
        zero_connection_left_endpoint r states' hpredicate'.1 i hi0, Nat.dist_self, Nat.cast_zero]
      exact hthetaBound
  have hhi : (Nat.dist (states i).hi (states' i).hi : ℝ) ≤ 2 * (theta : ℝ) * b / M := by
    rw [zero_connection_right_endpoint r states hpredicate.1 i,
      zero_connection_right_endpoint r states' hpredicate'.1 i]
    by_cases hnext : i.val + 1 < M
    · rw [connectionPrefixBoundary_ofFn states r.hi ⟨i.val + 1, hnext⟩,
        connectionPrefixBoundary_ofFn states' r.hi ⟨i.val + 1, hnext⟩]
      exact computedBand_cut_diameter parent r b P tau theta velocity htau child states states' hstates hstates'
        ⟨i.val + 1, hnext⟩ (by change 0 < i.val + 1; omega)
    · have hdrop : M ≤ i.val + 1 := by omega
      simp only [connectionPrefixBoundary, List.drop_eq_nil_iff.mpr
        (show (List.ofFn states).length ≤ i.val + 1 by simpa only [List.length_ofFn] using hdrop),
        List.drop_eq_nil_iff.mpr
        (show (List.ofFn states').length ≤ i.val + 1 by simpa only [List.length_ofFn] using hdrop),
        List.head?_nil, Option.map_none, Option.getD_none, Nat.dist_self, Nat.cast_zero]
      exact hthetaBound
  unfold targetEndpointDistance
  push_cast
  convert add_le_add hlo hhi using 1
  all_goals try with_reducible_and_instances rfl
  ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandEnvelopes
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Actual dyadic child envelopes

The maximum scans the actual finite band. The dyadic ceiling uses the
computable integer upper logarithm of a positive rational, including values
below one.
-/

namespace EditApproximation

open Finset



theorem le_rationalMaximum_member (fallback : ℚ) (values : List ℚ) (value : ℚ)
    (hvalue : value ∈ values) : value ≤ rationalMaximum fallback values := by
  induction values with
  | nil => simp only [List.not_mem_nil] at hvalue
  | cons head rest ih =>
    rcases List.mem_cons.mp hvalue with rfl | hrest
    · exact le_max_left _ _
    · exact (ih hrest).trans (le_max_right _ _)



/-- Zero is a harmless duplicated fallback under the initial table lower
invariant. The positive b/M floor ensures that the ceiling input is positive. -/


theorem bandChildEnvelope_lower {ny M : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (i : Fin M) :
    (b : ℚ) / M ≤ bandChildEnvelope b band initial i ∧
      ∀ action ∈ band, initial i (action i) ≤ bandChildEnvelope b band initial i := by
  have hceil := Int.self_le_zpow_clog (R := ℚ) (by decide : 1 < 2)
    (max ((b : ℚ) / M) (rationalMaximum 0 (band.map fun action => initial i (action i))))
  refine ⟨(le_max_left _ _).trans hceil, ?_⟩
  intro action ha
  exact (le_rationalMaximum_member 0 _ _ (List.mem_map.mpr ⟨action, ha, rfl⟩)).trans
    ((le_max_right _ _).trans hceil)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandRounding
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Integer rounding spacings from the dyadic band envelopes

Taking the nonnegative part of the dyadic product exponent computes the
integer spacing max(1, theta*h). The resulting spacing preserves the wide
grid by actual divisibility of powers of two.
-/

namespace EditApproximation

open Finset





/-- Actual division rounding moves each endpoint by at most the scaled
child envelope, including the special spacing-one case. -/
theorem gridRound_scaled_error (spacing position : ℕ) (scaled : ℚ)
    (hspacing : (spacing : ℚ) = max 1 scaled) (hscaled : 0 ≤ scaled) :
    (Nat.dist position (gridRound spacing position) : ℚ) ≤ scaled := by
  have hpos : 0 < spacing := by
    have hone : (1 : ℚ) ≤ spacing := by rw [hspacing]; exact le_max_left _ _
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) hone)
  by_cases hone : spacing = 1
  · simp only [hone, gridRound_one, Nat.dist_self, Nat.cast_zero]
    exact hscaled
  · have htwo : 1 < spacing := by omega
    have htwoR : (1 : ℚ) < spacing := by exact_mod_cast htwo
    have hscale : 1 < scaled := by
      by_contra hnot
      have hle : scaled ≤ 1 := le_of_not_gt hnot
      rw [max_eq_left hle] at hspacing
      linarith only [hspacing, htwoR]
    have hequal : (spacing : ℚ) = scaled := hspacing.trans (max_eq_right hscale.le)
    have herr : (Nat.dist position (gridRound spacing position) : ℚ) < spacing := by
      exact_mod_cast gridRound_error_lt spacing position hpos
    exact herr.le.trans_eq hequal

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandActionGuards
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Actual rounded band actions pass the finite guards

Each child uses its own envelope-derived integer spacing. The action is
rounded with literal integer division; wide-grid, radius and imbalance
claims are proved for these returned states.
-/

namespace EditApproximation

open Finset





theorem bandChildEnvelope_pos {ny M : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (i : Fin M) :
    0 < bandChildEnvelope b band initial i := by
  unfold bandChildEnvelope rationalDyadicCeiling
  positivity

theorem roundedBandAction_endpoint_error {ny M : ℕ} (thetaExponent b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (action : Fin M → TargetInterval ny) (i : Fin M) :
    (Nat.dist (action i).lo (roundedBandAction thetaExponent b band initial action i).lo : ℚ) ≤
        (2 : ℚ) ^ (-(thetaExponent : ℤ)) * bandChildEnvelope b band initial i ∧
      (Nat.dist (action i).hi (roundedBandAction thetaExponent b band initial action i).hi : ℚ) ≤
        (2 : ℚ) ^ (-(thetaExponent : ℤ)) * bandChildEnvelope b band initial i := by
  have hscaled : 0 ≤ (2 : ℚ) ^ (-(thetaExponent : ℤ)) * bandChildEnvelope b band initial i :=
    mul_nonneg (zpow_pos (by norm_num : (0 : ℚ) < 2) _).le (bandChildEnvelope_pos b band initial i).le
  exact ⟨gridRound_scaled_error _ _ _ (bandRoundSpacing_exact thetaExponent b band initial i) hscaled,
    gridRound_scaled_error _ _ _ (bandRoundSpacing_exact thetaExponent b band initial i) hscaled⟩

theorem roundedBandAction_distance {ny M : ℕ} (thetaExponent b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (action : Fin M → TargetInterval ny) (i : Fin M) :
    (targetEndpointDistance (action i) (roundedBandAction thetaExponent b band initial action i) : ℚ) ≤
      2 * (2 : ℚ) ^ (-(thetaExponent : ℤ)) * bandChildEnvelope b band initial i := by
  have h := roundedBandAction_endpoint_error thetaExponent b band initial action i
  unfold targetEndpointDistance
  push_cast
  convert add_le_add h.1 h.2 using 1
  all_goals try with_reducible_and_instances rfl
  ring

/-- Moving the two endpoints of each interval charges at most their total
movement, including the outside connections. -/
theorem connectionBudget_pair_perturbation {n : ℕ}
    (pairs : List (TargetInterval n × TargetInterval n)) (beforeStart afterStart finish : ℕ) :
    connectionBudget afterStart (pairs.map Prod.snd) finish ≤
      connectionBudget beforeStart (pairs.map Prod.fst) finish + Nat.dist afterStart beforeStart +
        (pairs.map fun pair => targetEndpointDistance pair.1 pair.2).sum := by
  induction pairs generalizing beforeStart afterStart with
  | nil =>
    simp only [List.map_nil, List.sum_nil, connectionBudget, Nat.add_zero]
    have h := Nat.dist.triangle_inequality afterStart beforeStart finish
    omega
  | cons pair rest ih =>
    rcases pair with ⟨before, after⟩
    have htail := ih before.hi after.hi
    have hfirst := Nat.dist.triangle_inequality afterStart beforeStart before.lo
    have hsecond := Nat.dist.triangle_inequality afterStart before.lo after.lo
    rw [Nat.dist_comm after.hi before.hi] at htail
    simp only [List.map_cons, List.sum_cons, connectionBudget, targetEndpointDistance] at htail ⊢
    omega

theorem endpointActionConnection_perturbation {n M : ℕ} (r : TargetInterval n)
    (before after : Fin M → TargetInterval n) :
    endpointActionConnection r after ≤ endpointActionConnection r before +
      ∑ i, targetEndpointDistance (before i) (after i) := by
  have h := connectionBudget_pair_perturbation
    (List.ofFn fun i : Fin M => (before i, after i)) r.lo r.lo r.hi
  simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_def, Nat.dist_self, Nat.add_zero,
    endpointActionConnection] using h

/-- The returned rounded action pays at most `2 θ ∑ hᵢ` in actual
connection cost when its unrounded band action has zero connection. -/
theorem roundedBandAction_connection {n M : ℕ} (r : TargetInterval n)
    (thetaExponent b : ℕ) (band : List (Fin M → TargetInterval n))
    (initial : Fin M → TargetInterval n → ℚ) (action : Fin M → TargetInterval n)
    (hzero : endpointActionConnection r action = 0) :
    (endpointActionConnection r (roundedBandAction thetaExponent b band initial action) : ℚ) ≤
      2 * (2 : ℚ) ^ (-(thetaExponent : ℤ)) * ∑ i, bandChildEnvelope b band initial i := by
  have hnatural := endpointActionConnection_perturbation r action
    (roundedBandAction thetaExponent b band initial action)
  rw [hzero, Nat.zero_add] at hnatural
  have hcast : (endpointActionConnection r
      (roundedBandAction thetaExponent b band initial action) : ℚ) ≤
        ∑ i, (targetEndpointDistance (action i)
          (roundedBandAction thetaExponent b band initial action i) : ℚ) := by
    exact_mod_cast hnatural
  calc
    _ ≤ ∑ i, (targetEndpointDistance (action i)
        (roundedBandAction thetaExponent b band initial action i) : ℚ) := hcast
    _ ≤ ∑ i, 2 * (2 : ℚ) ^ (-(thetaExponent : ℤ)) * bandChildEnvelope b band initial i :=
      sum_le_sum fun i _ => roundedBandAction_distance thetaExponent b band initial action i
    _ = _ := by rw [mul_sum]

theorem canonicalRoundedBandAction_connection {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (thetaExponent b P : ℕ) (tau velocity : ℚ)
    (child initial : Fin M → TargetInterval ny → ℚ)
    (hnonempty : computedBandActions parent r b P tau
      ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child ≠ []) :
    let band := computedBandActions parent r b P tau
      ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child
    (endpointActionConnection r
      (canonicalRoundedBandAction thetaExponent b band hnonempty initial) : ℚ) ≤
      2 * (2 : ℚ) ^ (-(thetaExponent : ℤ)) * ∑ i, bandChildEnvelope b band initial i := by
  have hmem := List.head_mem hnonempty
  obtain ⟨_, _, _, hpredicate⟩ := computedBandActions_mem parent r b P tau
    ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child _ hmem
  exact roundedBandAction_connection r thetaExponent b _ initial _ hpredicate.1

/-- The canonical rounded action is close to every member of its actual
computed band, with distance measured at both child endpoints. -/
theorem canonicalRoundedBandAction_distance {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (thetaExponent b P : ℕ) (tau velocity : ℚ) (htau : 0 < tau)
    (child initial : Fin M → TargetInterval ny → ℚ)
    (hnonempty : computedBandActions parent r b P tau
      ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child ≠ [])
    (action : Fin M → TargetInterval ny)
    (haction : action ∈ computedBandActions parent r b P tau
      ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child) (i : Fin M) :
    let band := computedBandActions parent r b P tau
      ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child
    (targetEndpointDistance (action i)
      (canonicalRoundedBandAction thetaExponent b band hnonempty initial i) : ℚ) ≤
        6 * (2 : ℚ) ^ (-(thetaExponent : ℤ)) * bandChildEnvelope b band initial i := by
  let theta : ℚ := (2 : ℚ) ^ (-(thetaExponent : ℤ))
  let band := computedBandActions parent r b P tau theta velocity child
  let canonical := band.head hnonempty
  let rounded := canonicalRoundedBandAction thetaExponent b band hnonempty initial
  have htheta : 0 ≤ theta := (zpow_pos (by norm_num : (0 : ℚ) < 2) _).le
  have hcanonical : canonical ∈ band := List.head_mem hnonempty
  have hdiameter := computedBand_child_endpoint_diameter parent r b P tau theta velocity
    htau htheta child action canonical haction hcanonical i
  have hdiameterQ : (targetEndpointDistance (action i) (canonical i) : ℚ) ≤ 4 * theta * b / M := by
    exact_mod_cast hdiameter
  have hfloor := (bandChildEnvelope_lower b band initial i).1
  have hscaled := mul_le_mul_of_nonneg_left hfloor (mul_nonneg (by norm_num : (0 : ℚ) ≤ 4) htheta)
  have hdiameterEnvelope : (targetEndpointDistance (action i) (canonical i) : ℚ) ≤
      4 * theta * bandChildEnvelope b band initial i := by
    calc
      _ ≤ 4 * theta * ((b : ℚ) / M) := by convert hdiameterQ using 1 <;> first | rfl | ring
      _ ≤ _ := hscaled
  have hround := roundedBandAction_distance thetaExponent b band initial canonical i
  change (targetEndpointDistance (canonical i) (rounded i) : ℚ) ≤
    2 * theta * bandChildEnvelope b band initial i at hround
  have htriangle : (targetEndpointDistance (action i) (rounded i) : ℚ) ≤
      targetEndpointDistance (action i) (canonical i) + targetEndpointDistance (canonical i) (rounded i) := by
    have hnatural : targetEndpointDistance (action i) (rounded i) ≤
        targetEndpointDistance (action i) (canonical i) + targetEndpointDistance (canonical i) (rounded i) := by
      unfold targetEndpointDistance
      have hlo := Nat.dist.triangle_inequality (action i).lo (canonical i).lo (rounded i).lo
      have hhi := Nat.dist.triangle_inequality (action i).hi (canonical i).hi (rounded i).hi
      omega
    exact_mod_cast hnatural
  change (targetEndpointDistance (action i) (rounded i) : ℚ) ≤
    6 * theta * bandChildEnvelope b band initial i
  linarith only [htriangle, hdiameterEnvelope, hround]

/-- The actual canonical rounded action satisfies the rounded-action
cost inequality uniformly for every actual band member. -/
theorem canonicalRoundedBandAction_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (thetaExponent b P : ℕ) (tau velocity : ℚ) (htau : 0 < tau)
    (child initial value : Fin M → TargetInterval ny → ℚ)
    (hnonempty : computedBandActions parent r b P tau
      ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child ≠ [])
    (action : Fin M → TargetInterval ny)
    (haction : action ∈ computedBandActions parent r b P tau
      ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child)
    (delta L : ℚ) (hL : 0 ≤ L)
    (hspatial : ∀ i s t, value i s ≤ (1 + delta) * value i t + L * targetEndpointDistance s t) :
    let band := computedBandActions parent r b P tau
      ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child
    rationalEndpointActionValue r (canonicalRoundedBandAction thetaExponent b band hnonempty initial) value ≤
      (1 + delta) * (∑ i, value i (action i)) +
        (6 * L + 2) * (2 : ℚ) ^ (-(thetaExponent : ℤ)) * ∑ i, bandChildEnvelope b band initial i := by
  let theta : ℚ := (2 : ℚ) ^ (-(thetaExponent : ℤ))
  let band := computedBandActions parent r b P tau theta velocity child
  let rounded := canonicalRoundedBandAction thetaExponent b band hnonempty initial
  have hchild (i : Fin M) : value i (rounded i) ≤ (1 + delta) * value i (action i) +
      6 * L * theta * bandChildEnvelope b band initial i := by
    have h := hspatial i (rounded i) (action i)
    have hsym : targetEndpointDistance (rounded i) (action i) = targetEndpointDistance (action i) (rounded i) := by
      unfold targetEndpointDistance
      rw [Nat.dist_comm (rounded i).lo, Nat.dist_comm (rounded i).hi]
    rw [hsym] at h
    have hmove := mul_le_mul_of_nonneg_left
      (canonicalRoundedBandAction_distance parent r thetaExponent b P tau velocity htau child initial
        hnonempty action haction i) hL
    nlinarith only [h, hmove]
  have hsum := sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin M))) => hchild i
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hsum
  have hconnection := canonicalRoundedBandAction_connection parent r thetaExponent b P tau velocity child initial hnonempty
  change (endpointActionConnection r rounded : ℚ) + ∑ i, value i (rounded i) ≤ _
  nlinarith only [hsum, hconnection]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GroupSampling
attribute [-instance] _root_.OAI.EditApproximation.physicalFamilyRange_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Shared group sampling

The one-scale estimator in Section 5 is a finite uniform average. Its
concentration follows from the explicitly cited Bernstein input. Choosing
among representatives and extending their costs by cones is deterministic
on the simultaneous approximation event, even when their samples are shared.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

/-- Estimated-cost minimization followed by actual evaluation loses at
most twice the uniform estimation error. There is no probabilistic
independence premise in this selection step. -/
theorem selected_group_cost_le {ι : Type*} (members : Finset ι)
    (cost estimate : ι → ℝ) (selected specified : ι) (error : ℝ)
    (hselected : selected ∈ members) (hspecified : specified ∈ members)
    (haccurate : ∀ i ∈ members, |estimate i - cost i| ≤ error)
    (hmin : estimate selected ≤ estimate specified) :
    cost selected ≤ cost specified + 2 * error := by
  have hs := (abs_le.mp (haccurate selected hselected)).1
  have hr := (abs_le.mp (haccurate specified hspecified)).2
  linarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandGroupSampling
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Executable shared group estimates

All dyadic powers in the prescribed closed range are enumerated, including
negative exponents. A scale is evaluated exactly when its sample count
reaches the child count; otherwise one shared array of uniform labels is
used for every member of the group. The selected member is the first
minimizer in the fixed list order.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory



/-- Actual shared draws are reused for all group members at this scale;
no independence between representatives is imposed. -/


theorem selectGroupMember_cost_le {ι : Type*} (members : List ι) (hnonempty : members ≠ [])
    (cost estimate : ι → ℚ) (specified : ι) (hspecified : specified ∈ members) (error : ℚ)
    (haccurate : ∀ member ∈ members, |estimate member - cost member| ≤ error) :
    cost (selectGroupMember members hnonempty estimate) ≤ cost specified + 2 * error := by
  classical
  have hspec := selectGroupMember_spec members hnonempty estimate
  have hreal := selected_group_cost_le members.toFinset (fun member => (cost member : ℝ))
    (fun member => (estimate member : ℝ)) (selectGroupMember members hnonempty estimate) specified (error : ℝ)
    (by simpa only [List.mem_toFinset] using hspec.1)
    (by simpa only [List.mem_toFinset] using hspecified)
    (fun member hmember => by exact_mod_cast haccurate member (List.mem_toFinset.mp hmember))
    (by exact_mod_cast hspec.2 specified hspecified)
  exact_mod_cast hreal

section ActualUnskippedGroup

variable {α : Type*} {source target : List α} {M b P thetaExponent : ℕ}
  {parent : TargetInterval source.length} {tau F : ℚ}
  {child initial : Fin M → TargetInterval target.length → ℚ}

theorem chooseUnskippedGroup_cost_le (Q : ℕ)
    (value : Fin M → TargetInterval target.length → ℚ)
    (members : List (UnskippedBand source target parent b P thetaExponent tau F child initial))
    (hnonempty : members ≠ [])
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (specified : UnskippedBand source target parent b P thetaExponent tau F child initial)
    (hspecified : specified ∈ members) (error : ℚ)
    (haccurate : ∀ member ∈ members, |dyadicUnskippedGroupEstimate Q value member draw -
      rationalEndpointActionValue member.center member.rounded value| ≤ error) :
    let selected := chooseUnskippedGroup Q value members hnonempty draw
    rationalEndpointActionValue selected.center selected.rounded value ≤
      rationalEndpointActionValue specified.center specified.rounded value + 2 * error :=
  selectGroupMember_cost_le members hnonempty
    (fun member => rationalEndpointActionValue member.center member.rounded value)
    (fun member => dyadicUnskippedGroupEstimate Q value member draw) specified hspecified error haccurate


end ActualUnskippedGroup

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GroupCells
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Whole rational cells are enumerated by bounded ranges of grid indices. -/

namespace EditApproximation



theorem cellTargetStates_diameter {n g : ℕ} {side : ℚ} (cell : ℕ × ℕ) (hg : 0 < g)
    (q r : TargetInterval n) (hq : q ∈ cellTargetStates n g side cell)
    (hr : r ∈ cellTargetStates n g side cell) : (targetEndpointDistance q r : ℚ) ≤ 2 * side := by
  have hq' := (cellTargetStates_mem cell hg q).mp hq
  have hr' := (cellTargetStates_mem cell hg r).mp hr
  have hlo : |(q.lo : ℚ) - r.lo| ≤ side := by
    apply abs_le.mpr
    constructor <;> linarith only [hq'.2.2.1, hq'.2.2.2.1, hr'.2.2.1, hr'.2.2.2.1]
  have hhi : |(q.hi : ℚ) - r.hi| ≤ side := by
    apply abs_le.mpr
    constructor <;> linarith only [hq'.2.2.2.2.1, hq'.2.2.2.2.2, hr'.2.2.2.2.1, hr'.2.2.2.2.2]
  have hcast (a b : ℕ) : |(a : ℚ) - b| = (Nat.dist a b : ℚ) := by
    exact_mod_cast natural_distance_cast a b
  rw [targetEndpointDistance, Nat.cast_add, ← hcast, ← hcast]
  linarith only [hlo, hhi]

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_CellGroupSelection
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal unskipped groups of whole cells and their selected wide actions. -/

namespace EditApproximation

open Finset



namespace UnskippedBand

theorem rounded_cost {α : Type*} {source target : List α} {M b P thetaExponent : ℕ}
    {parent : TargetInterval source.length} {tau F : ℚ}
    {child initial : Fin M → TargetInterval target.length → ℚ}
    (member : UnskippedBand source target parent b P thetaExponent tau F child initial)
    (htau : 0 < tau) (value : Fin M → TargetInterval target.length → ℚ)
    (action : Fin M → TargetInterval target.length) (haction : action ∈ member.actions)
    (delta L : ℚ) (hL : 0 ≤ L)
    (hspatial : ∀ i s t, value i s ≤ (1 + delta) * value i t + L * targetEndpointDistance s t) :
    rationalEndpointActionValue member.center member.rounded value ≤
      (1 + delta) * (∑ i, value i (action i)) +
        (6 * L + 2) * (2 : ℚ) ^ (-(thetaExponent : ℤ)) * ∑ i, member.envelope i := by
  have hnonempty := member.nonempty
  by_cases hempty : wideActionList M parent member.center b P = []
  · simp only [representativeBandActions, dite_eq_left hempty] at hnonempty
    exact False.elim (hnonempty rfl)
  · by_cases hZ : 0 < rationalWideActionMinimum parent member.center b P hempty child
    · have hband : member.actions = computedBandActions parent member.center b P tau
          ((2 : ℚ) ^ (-(thetaExponent : ℤ)))
          (rationalStateGap (substring source parent.lo parent.hi) target member.center /
            rationalWideActionMinimum parent member.center b P hempty child) child := by
        simp only [actions, representativeBandActions, dite_eq_right hempty, ite_eq_left hZ]
      have hne : computedBandActions parent member.center b P tau
          ((2 : ℚ) ^ (-(thetaExponent : ℤ)))
          (rationalStateGap (substring source parent.lo parent.hi) target member.center /
            rationalWideActionMinimum parent member.center b P hempty child) child ≠ [] := by
        rw [← hband]
        exact member.nonempty
      have ha := haction
      rw [hband] at ha
      have hcost := canonicalRoundedBandAction_cost parent member.center thetaExponent b P tau _ htau
        child initial value hne action ha delta L hL hspatial
      have hround := canonicalRounded_congr thetaExponent b _ _ hband member.nonempty hne initial
      change member.rounded = _ at hround
      rw [hround]
      simpa only [envelope, hband] using hcost
    · simp only [representativeBandActions, dite_eq_right hempty, ite_eq_right hZ] at hnonempty
      exact False.elim (hnonempty rfl)

end UnskippedBand



theorem group_rounding_coefficient {F L : ℚ} (hF : 1 ≤ F) (hL : 2 ≤ L) :
    (6 * L + 2) * (64 * F) + 2 * L ≤ 512 * L * F := by
  have hF0 : 0 ≤ F := by linarith only [hF]
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hlarge := mul_le_mul_of_nonneg_right hL (mul_nonneg (by norm_num : (0 : ℚ) ≤ 64) hF0)
  have hcell := mul_le_mul_of_nonneg_left hF (mul_nonneg (by norm_num : (0 : ℚ) ≤ 2) hL0)
  have hprod := mul_nonneg hL0 hF0
  nlinarith only [hlarge, hcell, hprod]

/-- Estimated minimization in an actual whole cell gives the group cone
bound simultaneously for every action of the specified member's band. -/
theorem chooseCellGroup_cone_bound {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F thetaExponent Q : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial value : Fin M → TargetInterval target.length → ℚ) (cell : ℕ × ℕ)
    (hnonempty : cellUnskippedBands source target parent b P F thetaExponent tau a
      parentInitial child initial cell ≠ [])
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (specified : UnskippedBand source target parent b P thetaExponent tau F child initial)
    (hspecified : specified ∈ cellUnskippedBands source target parent b P F thetaExponent tau a
      parentInitial child initial cell)
    (delta L gamma : ℚ) (hF : 1 ≤ F) (hL : 2 ≤ L) (htau : 0 < tau)
    (hspatial : ∀ i s t, value i s ≤ (1 + delta) * value i t + L * targetEndpointDistance s t)
    (haccurate : ∀ member ∈ cellUnskippedBands source target parent b P F thetaExponent tau a
        parentInitial child initial cell,
      |dyadicUnskippedGroupEstimate Q value member draw -
        rationalEndpointActionValue member.center member.rounded value| ≤ gamma * b)
    (action : Fin M → TargetInterval target.length) (haction : action ∈ specified.actions)
    (q : TargetInterval target.length) :
    let selected := chooseUnskippedGroup Q value
      (cellUnskippedBands source target parent b P F thetaExponent tau a parentInitial child initial cell)
      hnonempty draw
    rationalActionValue (fun q r => targetEndpointDistance q r) L (fun is => value is.1 is.2) q
        selected.rationalAction ≤
      L * targetEndpointDistance q specified.center + (1 + delta) * (∑ i, value i (action i)) +
        (2 * gamma + 512 * L * F * (2 : ℚ) ^ (-(thetaExponent : ℤ))) * b := by
  let members := cellUnskippedBands source target parent b P F thetaExponent tau a
    parentInitial child initial cell
  let selected := chooseUnskippedGroup Q value members hnonempty draw
  have hselected : selected ∈ members := (chooseUnskippedGroup_spec Q value members hnonempty draw).1
  have hcost := chooseUnskippedGroup_cost_le Q value members hnonempty draw specified hspecified
    (gamma * b) haccurate
  change rationalEndpointActionValue selected.center selected.rounded value ≤
    rationalEndpointActionValue specified.center specified.rounded value + 2 * (gamma * b) at hcost
  have hrounded := specified.rounded_cost htau value action haction delta L (by linarith only [hL]) hspatial
  have hcenterCell (member : UnskippedBand source target parent b P thetaExponent tau F child initial)
      (hm : member ∈ members) : member.center ∈
        cellTargetStates target.length (seedGridSpacing b P) ((2 : ℚ) ^ (-(thetaExponent : ℤ)) * b) cell := by
    have hc := (unskippedBandList_mem_iff _ member).mp hm
    exact (List.mem_filter.mp hc).1
  have hdiam := cellTargetStates_diameter cell (by unfold seedGridSpacing; omega)
    specified.center selected.center (hcenterCell specified hspecified) (hcenterCell selected hselected)
  have htriangle : (targetEndpointDistance q selected.center : ℚ) ≤
      targetEndpointDistance q specified.center + targetEndpointDistance specified.center selected.center := by
    have h := targetEndpointDistance_triangle q specified.center selected.center
    have h' : (targetEndpointDistance q selected.center : ℚ) ≤
        targetEndpointDistance specified.center selected.center + targetEndpointDistance q specified.center := by
      exact_mod_cast h
    simpa only [add_comm] using h'
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hdist := mul_le_mul_of_nonneg_left (htriangle.trans (add_le_add_right hdiam _)) hL0
  have htheta : 0 ≤ (2 : ℚ) ^ (-(thetaExponent : ℤ)) := (zpow_pos (by norm_num : (0 : ℚ) < 2) _).le
  have hsum := mul_le_mul_of_nonneg_left specified.sum_guard
    (mul_nonneg (by linarith only [hL0] : 0 ≤ 6 * L + 2) htheta)
  change (6 * L + 2) * (2 : ℚ) ^ (-(thetaExponent : ℤ)) * (∑ i, specified.envelope i) ≤
    (6 * L + 2) * (2 : ℚ) ^ (-(thetaExponent : ℤ)) * (64 * F * b) at hsum
  have hcoef := mul_le_mul_of_nonneg_right (group_rounding_coefficient (F := (F : ℚ)) (L := L)
    (by exact_mod_cast hF) hL)
    (mul_nonneg htheta (Nat.cast_nonneg (α := ℚ) b))
  dsimp only [rationalActionValue, UnskippedBand.rationalAction]
  dsimp only [rationalEndpointActionValue] at hcost hrounded
  nlinarith only [hcost, hrounded, hdist, hsum, hcoef]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_FirstCrossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual first crossing of a finite action band

The crossing index is computed from the fixed child tables for analysis.
It is independent of parent sampling. The lemmas separate the prefixPayoff,
the single crossing, and the nonpositive later clipped regrets.
-/

namespace EditApproximation

open Finset

theorem firstCrossing_le {α : Type*} (band : Finset α)
    (S : ℕ) (actionCost : ℕ → α → ℝ) (c : ℝ) :
    firstCrossing band S actionCost c ≤ S := by
  unfold firstCrossing
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · rfl

theorem before_firstCrossing {α : Type*} (band : Finset α)
    (S : ℕ) (actionCost : ℕ → α → ℝ) (c : ℝ)
    {t : ℕ} (ht : t < firstCrossing band S actionCost c)
    {action : α} (ha : action ∈ band) : c ≤ actionCost t action := by
  by_contra hnot
  have htS : t < S := ht.trans_le (firstCrossing_le band S actionCost c)
  have hex : ∃ t, t < S ∧ ∃ action ∈ band, actionCost t action < c :=
    ⟨t, htS, action, ha, lt_of_not_ge hnot⟩
  have hfind : firstCrossing band S actionCost c ≤ t := by
    rw [firstCrossing, dite_eq_left hex]
    exact Nat.find_min' hex ⟨htS, action, ha, lt_of_not_ge hnot⟩
  omega

theorem at_firstCrossing {α : Type*} (band : Finset α)
    (S : ℕ) (actionCost : ℕ → α → ℝ) (c : ℝ)
    (ht : firstCrossing band S actionCost c < S) :
    ∃ action ∈ band, actionCost (firstCrossing band S actionCost c) action < c := by
  by_cases h : ∃ t, t < S ∧ ∃ action ∈ band, actionCost t action < c
  · simpa only [firstCrossing, dite_eq_left h] using (Nat.find_spec h).2
  · have heq : firstCrossing band S actionCost c = S := by
      rw [firstCrossing, dite_eq_right h]
    omega

/-- A finite first-crossing partition charges the crossing only once.
All failure indicators may be correlated with the sampled actions. -/
theorem firstCrossing_sum_bound (S crossing : ℕ) (regret prefixPayoff failure : ℕ → ℝ)
    (crossingCharge failureCharge : ℝ) (hcrossing : crossing ≤ S)
    (hcharge : 0 ≤ crossingCharge) (hfailureCharge : 0 ≤ failureCharge)
    (hfailure : ∀ t < S, 0 ≤ failure t)
    (hprefixPayoff : ∀ t < crossing, regret t ≤ prefixPayoff t + failureCharge * failure t)
    (hcross : crossing < S → regret crossing ≤ crossingCharge + failureCharge * failure crossing)
    (hafter : ∀ t < S, crossing < t → regret t ≤ 0) :
    (∑ t ∈ range S, regret t) ≤
      (∑ t ∈ range crossing, prefixPayoff t) + crossingCharge +
        failureCharge * ∑ t ∈ range S, failure t := by
  have hpoint (t : ℕ) (ht : t ∈ range S) :
      regret t ≤ (if t < crossing then prefixPayoff t else 0) +
        (if t = crossing then crossingCharge else 0) + failureCharge * failure t := by
    have htS := mem_range.mp ht
    by_cases hbefore : t < crossing
    · simp only [hbefore, ite_true, if_true, show t ≠ crossing by omega, ite_false, if_false, add_zero]
      exact hprefixPayoff t hbefore
    · by_cases heq : t = crossing
      · subst t
        simpa only [lt_self_iff_false, ite_false, if_false, ite_true, if_true, zero_add] using hcross htS
      · simp only [hbefore, ite_false, if_false, heq, zero_add]
        exact (hafter t htS (by omega)).trans (mul_nonneg hfailureCharge (hfailure t htS))
  have hsum := sum_le_sum hpoint
  have hpre : (∑ t ∈ range S, if t < crossing then prefixPayoff t else 0) =
      ∑ t ∈ range crossing, prefixPayoff t := by
    rw [← sum_filter]
    congr 1
    ext t
    simp only [mem_filter, mem_range]
    omega
  have hcrossSum : (∑ t ∈ range S, if t = crossing then crossingCharge else 0) ≤ crossingCharge := by
    rw [sum_ite_eq']
    split_ifs
    · rfl
    · exact hcharge
  simp only [sum_add_distrib, ← mul_sum] at hsum
  rw [hpre] at hsum
  linarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_NodeRegret
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Clipped regret of the actual refinement update

This is the deterministic first-crossing transfer in Proposition 7.3.
The hypothesis about group estimates is a pointwise estimate on their
success event; their probability is handled separately. No independence
between a sampled action and that success event is required.
-/

namespace EditApproximation

open Finset

theorem refinement_firstCrossing_regret {β σ : Type*} [Fintype β]
    (band : Finset (β → σ)) (S : ℕ)
    (table : ℕ → β × σ → ℝ) (comparisonClipped : ℕ → ℝ)
    (sample : ℕ → β → σ) (cone online : ℕ → ℝ) (failure : ℕ → Bool)
    (charge c b F δ κ error : ℝ)
    (hc : 0 ≤ c) (hF : 1 ≤ F) (hδ : 0 < δ) (hκ : 0 ≤ κ) (hb : b ≤ c)
    (herror : error * b ≤ κ * δ * b) (herrorCross : error * b ≤ δ * c)
    (hmono : ∀ action ∈ band, Antitone (fun t => bandActionCost charge table t action))
    (hsample : ∀ t < S, sample t ∈ band)
    (hcomparison : ∀ t ≤ S, c ≤ charge + comparisonClipped t)
    (honline : ∀ t < S, online t ≤ bandActionCost charge table (t + 1) (sample t))
    (hbellman : ∀ t < S, ∀ action ∈ band, cone t ≤ bandActionCost charge table t action)
    (hgroup : ∀ t < S, failure t = false → ∀ action ∈ band,
      cone t ≤ (1 + δ) * bandActionCost charge table (t + 1) action + error * b)
    (hupper : ∀ t < S, max c (refinementUpdate δ (cone t) (online t)) ≤ 2 * F * c) :
    let crossing := firstCrossing band S (fun t => bandActionCost charge table (t + 1)) c
    (∑ t ∈ range S,
      (max c (refinementUpdate δ (cone t) (online t)) - charge - comparisonClipped (t + 1))) ≤
      (∑ t ∈ range crossing, sampledPrefixRegret charge κ table comparisonClipped sample t) +
        2 * δ * c + 2 * F * c * ∑ t ∈ range S, (if failure t then (1 : ℝ) else 0) := by
  let actionCost := fun t => bandActionCost charge table (t + 1)
  let crossing := firstCrossing band S actionCost c
  let regret := fun t => max c (refinementUpdate δ (cone t) (online t)) -
    charge - comparisonClipped (t + 1)
  have hcrossing : crossing ≤ S := firstCrossing_le band S actionCost c
  change (∑ t ∈ range S, regret t) ≤
    (∑ t ∈ range crossing, sampledPrefixRegret charge κ table comparisonClipped sample t) +
      2 * δ * c + 2 * F * c * ∑ t ∈ range S, (if failure t then (1 : ℝ) else 0)
  apply firstCrossing_sum_bound S crossing regret
    (sampledPrefixRegret charge κ table comparisonClipped sample)
    (fun t => if failure t then (1 : ℝ) else 0) (2 * δ * c) (2 * F * c)
    hcrossing (by positivity) (by positivity)
  · intro t _
    split_ifs <;> norm_num
  · intro t ht
    have htS : t < S := ht.trans_le hcrossing
    have ha := hsample t htS
    have hcost : c ≤ bandActionCost charge table (t + 1) (sample t) :=
      before_firstCrossing band S actionCost c ht ha
    have hdecrease := hmono (sample t) ha (Nat.le_succ t)
    have hclip : max c (refinementUpdate δ (cone t) (online t)) ≤
        bandActionCost charge table (t + 1) (sample t) +
          κ * (bandActionCost charge table t (sample t) -
            bandActionCost charge table (t + 1) (sample t)) +
          2 * F * c * (if failure t then (1 : ℝ) else 0) := by
      cases hf : failure t with
      | false =>
        simp only [Bool.false_eq_true, ite_false, if_false, mul_zero, add_zero]
        exact refinementUpdate_prefix hδ hκ hc hb hcost hdecrease
          (honline t htS) (hbellman t htS (sample t) ha)
          (hgroup t htS hf (sample t) ha) herror
      | true =>
        simp only [ite_true, if_true, mul_one]
        have hdec0 := mul_nonneg hκ (sub_nonneg.mpr hdecrease)
        linarith [hupper t htS]
    dsimp only [regret, sampledPrefixRegret]
    linarith
  · intro ht
    obtain ⟨action, ha, hcross⟩ := at_firstCrossing band S actionCost c ht
    have hclip : max c (refinementUpdate δ (cone crossing) (online crossing)) ≤
        c + 2 * δ * c + 2 * F * c * (if failure crossing then (1 : ℝ) else 0) := by
      cases hf : failure crossing with
      | false =>
        simp only [Bool.false_eq_true, ite_false, if_false, mul_zero, add_zero]
        apply refinementUpdate_crossing hδ.le hc hcross
        have hestimate := hgroup crossing ht hf action ha
        linarith
      | true =>
        simp only [ite_true, if_true, mul_one]
        have hslack := mul_nonneg hδ.le hc
        linarith [hupper crossing ht]
    dsimp only [regret]
    linarith [hcomparison (crossing + 1) (by omega)]
  · intro t ht hafter
    obtain ⟨action, ha, hcross⟩ := at_firstCrossing band S actionCost c (hafter.trans ht)
    have hcost : bandActionCost charge table t action < c :=
      (hmono action ha (show crossing + 1 ≤ t by omega)).trans_lt hcross
    have hparent : refinementUpdate δ (cone t) (online t) ≤ c :=
      (min_le_left _ _).trans ((hbellman t ht action ha).trans hcost.le)
    dsimp only [regret]
    rw [max_eq_left hparent]
    linarith [hcomparison (t + 1) (by omega)]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_RationalWideSpatial
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial bounds for a literal rational refinement update. -/

namespace EditApproximation

open Finset

theorem rationalMinimum_map_spatial {ι : Type*} (indices : List ι)
    (fallback fallback' charge : ℚ) (value value' : ι → ℚ)
    (hfallback : fallback ≤ fallback' + charge)
    (hvalue : ∀ i ∈ indices, value i ≤ value' i + charge) :
    rationalMinimum fallback (indices.map value) ≤
      rationalMinimum fallback' (indices.map value') + charge := by
  induction indices with
  | nil => exact hfallback
  | cons i rest ih =>
    change min (value i) (rationalMinimum fallback (rest.map value)) ≤
      min (value' i) (rationalMinimum fallback' (rest.map value')) + charge
    rw [← min_add_add_right]
    exact min_le_min (hvalue i (by simp)) (ih fun j hj => hvalue j (by simp [hj]))

theorem rationalActionValue_spatial {ny : ℕ} {Child : Type*} {M : ℕ}
    (L : ℚ) (hL : 0 ≤ L) (child : Child → ℚ)
    (q q' : TargetInterval ny) (action : RationalBellmanAction (TargetInterval ny) Child M) :
    rationalActionValue (fun q r => targetEndpointDistance q r) L child q action ≤
      rationalActionValue (fun q r => targetEndpointDistance q r) L child q' action +
        L * targetEndpointDistance q q' := by
  have htriangle : (targetEndpointDistance q action.center : ℚ) ≤
      targetEndpointDistance q' action.center + targetEndpointDistance q q' := by
    exact_mod_cast targetEndpointDistance_triangle q q' action.center
  have h := mul_le_mul_of_nonneg_left htriangle hL
  dsimp only [rationalActionValue]
  linarith only [h]

theorem rationalBellman_spatial {ny : ℕ} {Child : Type*} {M : ℕ}
    (initial : TargetInterval ny → ℚ) (L : ℚ) (hL : 0 ≤ L)
    (actions : List (RationalBellmanAction (TargetInterval ny) Child M)) (child : Child → ℚ)
    (q q' : TargetInterval ny)
    (hinit : initial q ≤ initial q' + L * targetEndpointDistance q q') :
    rationalBellman initial (fun q r => targetEndpointDistance q r) L actions child q ≤
      rationalBellman initial (fun q r => targetEndpointDistance q r) L actions child q' +
        L * targetEndpointDistance q q' := by
  apply rationalMinimum_map_spatial _ _ _ _ _ _ hinit
  intro action _
  exact rationalActionValue_spatial L hL child q q' action

theorem rationalWideStepCone_spatial {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ)
    (initial : TargetInterval ny → ℚ) (L : ℚ) (hL : 0 ≤ L)
    (old current : Fin M × TargetInterval ny → ℚ)
    (groups : List (RationalBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (q q' : TargetInterval ny)
    (hinit : initial q ≤ initial q' + L * targetEndpointDistance q q') :
    rationalWideStepCone parent representatives P initial L old current groups q ≤
      rationalWideStepCone parent representatives P initial L old current groups q' +
        L * targetEndpointDistance q q' := by
  apply rationalMinimum_map_spatial _ _ _ _ _ _
    (rationalBellman_spatial initial L hL _ old q q' hinit)
  intro action _
  exact rationalActionValue_spatial L hL current q q' action

theorem rationalRefinementUpdate_le_cone (delta cone : ℚ) (online : Option ℚ) :
    rationalRefinementUpdate delta cone online ≤ cone := by
  cases online with
  | none => exact le_rfl
  | some value => exact min_le_left _ _

theorem rationalRefinementUpdate_div_lower (delta cone : ℚ) (online : Option ℚ)
    (hdelta : 0 ≤ delta) (hcone : 0 ≤ cone) :
    cone / (1 + delta) ≤ rationalRefinementUpdate delta cone online := by
  have hdiv : cone / (1 + delta) ≤ cone := div_le_self hcone (by linarith)
  cases online with
  | none => exact hdiv
  | some value => exact le_min hdiv (le_max_left _ _)

theorem rationalWideStep_spatial {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ)
    (initial : TargetInterval ny → ℚ) (L delta : ℚ) (hL : 0 ≤ L) (hdelta : 0 ≤ delta)
    (old current : Fin M × TargetInterval ny → ℚ)
    (groups : List (RationalBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (online : TargetInterval ny → List (RationalBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (q q' : TargetInterval ny)
    (hinit : initial q ≤ initial q' + L * targetEndpointDistance q q')
    (hcone : 0 ≤ rationalWideStepCone parent representatives P initial L old current groups q') :
    rationalWideStep parent representatives P initial L delta old current groups (online q) q ≤
      (1 + delta) * rationalWideStep parent representatives P initial L delta old current groups (online q') q' +
        L * targetEndpointDistance q q' := by
  have hu := rationalRefinementUpdate_le_cone delta
    (rationalWideStepCone parent representatives P initial L old current groups q)
    (rationalOnlineMinimum ((online q).map (rationalActionValue (fun q r => targetEndpointDistance q r) L current q)))
  have hs := rationalWideStepCone_spatial parent representatives P initial L hL old current groups q q' hinit
  have hl := rationalRefinementUpdate_div_lower delta
    (rationalWideStepCone parent representatives P initial L old current groups q')
    (rationalOnlineMinimum ((online q').map (rationalActionValue (fun q r => targetEndpointDistance q r) L current q')))
    hdelta hcone
  have hd : (0 : ℚ) < 1 + delta := by linarith
  have hl' := (div_le_iff₀ hd).mp hl
  change _ ≤ (1 + delta) * _ + _
  dsimp only [rationalWideStep] at *
  nlinarith only [hu, hs, hl']

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSpatial
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial regularity of the actual local initial table and physical warmup. -/

namespace EditApproximation

theorem physicalBellman_spatial {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (hL : 0 ≤ L) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (hinit : ∀ node q q', initial (node, q) ≤ initial (node, q') + L * targetEndpointDistance q q')
    (value : PhysicalEntry M J target.length → ℝ) (node : PhysicalNode M J)
    (q q' : TargetInterval target.length) :
    physicalBellman source target P L initial representatives value (node, q) ≤
      physicalBellman source target P L initial representatives value (node, q') +
        L * targetEndpointDistance q q' := by
  classical
  unfold physicalBellman
  dsimp only
  split_ifs with hbelow hleaf
  · exact hinit node q q'
  · exact finiteBellman_spatial (fun s => initial (node, s))
      (fun s t => targetEndpointDistance s t) L
      (actualWideActions (physicalSourceInterval source.length node) (representatives node) P)
      (fun is => value (physicalChild node hbelow is.1, is.2)) hL q q' (hinit node q q')
      (fun center => by exact_mod_cast targetEndpointDistance_triangle q q' center)
  · exact hinit node q q'

theorem physicalWarmup_spatial {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (hL : 0 ≤ L) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (hinit : ∀ node q q', initial (node, q) ≤ initial (node, q') + L * targetEndpointDistance q q')
    (t : ℕ) (node : PhysicalNode M J) (q q' : TargetInterval target.length) :
    physicalWarmup source target P L initial representatives t (node, q) ≤
      physicalWarmup source target P L initial representatives t (node, q') +
        L * targetEndpointDistance q q' := by
  cases t with
  | zero => exact hinit node q q'
  | succ t => exact physicalBellman_spatial source target P L hL initial representatives hinit _ node q q'

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRefinementSpatial
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.physicalMedianUpdateTable_value _root_.OAI.EditApproximation.physicalNodeCodeWithWork_value _root_.OAI.EditApproximation.physicalSubtreeNode_zero _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.treeLayerCodeWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonnegativity, exact zero states and spatial regularity of the full stage. -/

namespace EditApproximation

theorem stageInitial_spatial {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (node : PhysicalNode M J) (q q' : TargetInterval target.length) :
    stageInitial source target U N P F A (node, q) ≤
      stageInitial source target U N P F A (node, q') + (128 * F : ℚ) * targetEndpointDistance q q' := by
  have hfactor := refinementFactor_spec A F (by omega)
  have h32 := physicalInitialTable_spatial source target U N P F A (refinementFactor A F)
    hsize hP hF hA hfactor.1 hfactor.2 hseed node q q'
  have hcharge : (32 * F : ℚ) * targetEndpointDistance q q' ≤
      (128 * F : ℚ) * targetEndpointDistance q q' := by
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_right (by norm_num : (32 : ℚ) ≤ 128) (Nat.cast_nonneg F)
  change physicalInitialTable source target U N P F A (refinementFactor A F) (node, q) ≤
    physicalInitialTable source target U N P F A (refinementFactor A F) (node, q') +
      (128 * F : ℚ) * targetEndpointDistance q q'
  exact le_trans h32 (add_le_add_right hcharge
    (physicalInitialTable source target U N P F A (refinementFactor A F) (node, q')))

theorem physicalRefinement_nonneg {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (hM : 0 < M) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (hT : 0 < T) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (node : PhysicalNode M J)
    (t : ℕ) (q : TargetInterval target.length) :
    0 ≤ physicalRefinement source target U N P F A T delta choices node t q := by
  have h := (physicalRefinement_stage_bounds source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices node t q).1
  have hzero : 0 ≤ physicalLower source target (refinementFactor A F : ℝ) (node, q) :=
    (abs_nonneg _).trans (le_max_right _ _)
  exact (Rat.cast_nonneg (K := ℝ)).mp (hzero.trans h)

theorem physicalRefinement_spatial {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (hM : 0 < M) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (hT : 0 < T) (delta : ℚ) (hdelta : 0 ≤ delta)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (node : PhysicalNode M J)
    (t : ℕ) (q q' : TargetInterval target.length) :
    physicalRefinement source target U N P F A T delta choices node t q ≤
      (1 + delta) * physicalRefinement source target U N P F A T delta choices node t q' +
        (128 * F : ℚ) * targetEndpointDistance q q' := by
  have hL : (0 : ℚ) ≤ 128 * F := mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hinit (node : PhysicalNode M J) (r r' : TargetInterval target.length) :
      stageInitial source target U N P F A (node, r) ≤
        stageInitial source target U N P F A (node, r') + (128 * F : ℚ) * targetEndpointDistance r r' := by
    exact stageInitial_spatial source target U N P F A hsize hP hF hA hseed node r r'
  have hnonneg := physicalRefinement_nonneg source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices node t q'
  have hmul := mul_nonneg hdelta hnonneg
  by_cases hbelow : node.1.val < J
  · by_cases hleaf : (physicalSourceInterval source.length node).hi -
        (physicalSourceInterval source.length node).lo ≤ 1
    · rw [physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inr hleaf)] at hmul ⊢
      rw [physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inr hleaf)]
      nlinarith only [hinit node q q', hmul]
    · cases t with
      | zero =>
        rw [physicalRefinement_zero] at hmul ⊢
        rw [physicalRefinement_zero]
        have hinitR (n : PhysicalNode M J) (r r' : TargetInterval target.length) :
            (stageInitial source target U N P F A (n, r) : ℝ) ≤
              (stageInitial source target U N P F A (n, r') : ℝ) +
                ((128 * F : ℚ) : ℝ) * targetEndpointDistance r r' := by
          exact_mod_cast hinit n r r'
        have hw := physicalWarmup_spatial source target P ((128 * F : ℚ) : ℝ)
          ((Rat.cast_nonneg (K := ℝ)).mpr hL)
          (fun s => (stageInitial source target U N P F A s : ℝ))
          (stageRepresentatives source target U N P F A) hinitR T node q q'
        have hwQ : stageWarmup source target U N P F A T (node, q) ≤
            stageWarmup source target U N P F A T (node, q') +
              (128 * F : ℚ) * targetEndpointDistance q q' := by
          apply (Rat.cast_le (K := ℝ)).mp
          simpa only [stageWarmup, rationalPhysicalWarmup_cast, Rat.cast_add, Rat.cast_mul,
            Rat.cast_natCast] using hw
        nlinarith only [hwQ, hmul]
      | succ t =>
        let children : PhysicalChildTables M target.length := fun i =>
          physicalRefinement source target U N P F A T delta choices (physicalChild node hbelow i)
        have hcone : 0 ≤ rationalWideStepCone (physicalSourceInterval source.length node)
            (stageRepresentatives source target U N P F A node) P
            (fun r => stageInitial source target U N P F A (node, r)) (128 * F)
            (fun is => children is.1 t is.2) (fun is => children is.1 (t + 1) is.2)
            (choices.groups node children (t + 1)) q' := by
          rw [physicalRefinement_succ _ _ _ _ _ _ _ _ _ _ node hbelow hleaf] at hnonneg
          exact hnonneg.trans (rationalRefinementUpdate_le_cone _ _ _)
        rw [physicalRefinement_succ _ _ _ _ _ _ _ _ _ _ node hbelow hleaf,
          physicalRefinement_succ _ _ _ _ _ _ _ _ _ _ node hbelow hleaf]
        exact rationalWideStep_spatial _ _ P _ (128 * F) delta hL hdelta _ _ _
          (choices.online node children (t + 1)) q q' (hinit node q q') hcone
  · rw [physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inl hbelow)] at hmul ⊢
    rw [physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inl hbelow)]
    nlinarith only [hinit node q q', hmul]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalOnlineBand
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Online actions from the actual physical child histories

The fixed representative band uses the rational warmup-average child
table. Its envelopes scan the literal initial child table. Online gains
and decrements are computed from the full physical refinement histories.
-/

namespace EditApproximation

open Finset


section PhysicalBand

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A))
  (node : PhysicalNode M J) (hbelow : node.1.val < J)

variable (b thetaExponent : ℕ) (tau : ℚ) (r : TargetInterval target.length)

local notation "history" => physicalBandHistory source target U N P F A T delta choices node hbelow

theorem physicalBandHistory_nonincreasing (t : ℕ) (coordinate : Fin M × TargetInterval target.length) :
    history (t + 1) coordinate ≤ history t coordinate :=
  physicalRefinement_nonincreasing source target U N P F A T delta choices
    (physicalChild node hbelow coordinate.1) t coordinate.2


end PhysicalBand

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalNodeRegret
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# First crossing for the literal physical refinement

Online and selected-group candidates are connected to the complete
refinement by membership in its actual finite lists. Group success is the
literal simultaneous estimator-error test, rather than a cone-bound
assumption. The child environment remains fixed throughout this argument.
-/

namespace EditApproximation

open Finset



theorem rationalOnlineMinimum_le_member (values : List ℚ) (value : ℚ) (hvalue : value ∈ values) :
    ∃ online, rationalOnlineMinimum values = some online ∧ online ≤ value := by
  cases values with
  | nil => simp only [List.not_mem_nil] at hvalue
  | cons first rest =>
    refine ⟨rationalMinimum first rest, rfl, ?_⟩
    rcases List.mem_cons.mp hvalue with rfl | hrest
    · exact rationalMinimum_le_fallback _ _
    · exact rationalMinimum_le_member _ _ hrest

theorem rationalWideStep_online_exists {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ)
    (initial : TargetInterval ny → ℚ) (L delta : ℚ)
    (old current : Fin M × TargetInterval ny → ℚ)
    (groups online : List (PhysicalRationalAction M ny)) (q : TargetInterval ny)
    (action : PhysicalRationalAction M ny) (haction : action ∈ online) :
    ∃ value, rationalOnlineMinimum
        (online.map (rationalActionValue (fun q r => targetEndpointDistance q r) L current q)) = some value ∧
      value ≤ rationalActionValue (fun q r => targetEndpointDistance q r) L current q action ∧
      (rationalWideStep parent representatives P initial L delta old current groups online q : ℝ) =
        refinementUpdate (delta : ℝ)
          (rationalWideStepCone parent representatives P initial L old current groups q : ℝ) (value : ℝ) := by
  obtain ⟨value, hvalue, hle⟩ := rationalOnlineMinimum_le_member _ _
    (List.mem_map.mpr ⟨action, haction, rfl⟩)
  refine ⟨value, hvalue, hle, ?_⟩
  rw [rationalWideStep, hvalue, rationalRefinementUpdate_cast]

theorem rationalWideStepCone_le_group {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ)
    (initial : TargetInterval ny → ℚ) (L : ℚ)
    (old current : Fin M × TargetInterval ny → ℚ)
    (groups : List (PhysicalRationalAction M ny)) (q : TargetInterval ny)
    (action : PhysicalRationalAction M ny) (haction : action ∈ groups) :
    rationalWideStepCone parent representatives P initial L old current groups q ≤
      rationalActionValue (fun q r => targetEndpointDistance q r) L current q action :=
  rationalMinimum_le_member _ _ (List.mem_map.mpr ⟨action, haction, rfl⟩)

theorem rationalWideStepCone_le_wide {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ)
    (initial : TargetInterval ny → ℚ) (L : ℚ)
    (old current : Fin M × TargetInterval ny → ℚ)
    (groups : List (PhysicalRationalAction M ny)) (q : TargetInterval ny)
    (action : PhysicalRationalAction M ny)
    (haction : action ∈ rationalActualWideActions parent representatives P) :
    rationalWideStepCone parent representatives P initial L old current groups q ≤
      rationalActionValue (fun q r => targetEndpointDistance q r) L old q action :=
  (rationalMinimum_le_fallback _ _).trans (rationalBellman_le_action _ _ _ _ _ _ action haction)

theorem unskippedGroupFailure_false {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P thetaExponent : ℕ) (tau F : ℚ)
    (child initial value : Fin M → TargetInterval target.length → ℚ) (Q : ℕ)
    (members : List (UnskippedBand source target parent b P thetaExponent tau F child initial))
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (gamma : ℚ) (hfailure : unskippedGroupFailure source target parent b P thetaExponent tau F
      child initial value Q members draw gamma = false) :
    ∀ member ∈ members, |dyadicUnskippedGroupEstimate Q value member draw -
      rationalEndpointActionValue member.center member.rounded value| ≤ gamma * b := by
  intro member hmember
  by_contra hnot
  have hlt := lt_of_not_ge hnot
  have htrue : unskippedGroupFailure source target parent b P thetaExponent tau F
      child initial value Q members draw gamma = true := by
    exact List.any_eq_true.mpr ⟨member, hmember, by simp only [hlt, decide_true]⟩
  rw [hfailure] at htrue
  cases htrue

/-- A selected group candidate in the actual list supplies the cone bound
on the literal estimator-success event. -/
theorem rationalWideStepCone_group_bound {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (representatives : List (ℕ × TargetInterval target.length))
    (b P F thetaExponent Q : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (old current : Fin M × TargetInterval target.length → ℚ) (cell : ℕ × ℕ)
    (hnonempty : cellUnskippedBands source target parent b P F thetaExponent tau a
      parentInitial child initial cell ≠ [])
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (specified : UnskippedBand source target parent b P thetaExponent tau F child initial)
    (hspecified : specified ∈ cellUnskippedBands source target parent b P F thetaExponent tau a
      parentInitial child initial cell)
    (groups : List (PhysicalRationalAction M target.length))
    (hselected : (chooseUnskippedGroup Q (fun i s => current (i, s))
      (cellUnskippedBands source target parent b P F thetaExponent tau a parentInitial child initial cell)
      hnonempty draw).rationalAction ∈ groups)
    (delta L gamma : ℚ) (hF : 1 ≤ F) (hL : 2 ≤ L) (htau : 0 < tau)
    (hspatial : ∀ i s t, current (i, s) ≤ (1 + delta) * current (i, t) + L * targetEndpointDistance s t)
    (hfailure : unskippedGroupFailure source target parent b P thetaExponent tau F child initial
      (fun i s => current (i, s)) Q
      (cellUnskippedBands source target parent b P F thetaExponent tau a parentInitial child initial cell)
      draw gamma = false)
    (action : Fin M → TargetInterval target.length) (haction : action ∈ specified.actions)
    (q : TargetInterval target.length) :
    rationalWideStepCone parent representatives P parentInitial L old current groups q ≤
      L * targetEndpointDistance q specified.center + (1 + delta) * (∑ i, current (i, action i)) +
        (2 * gamma + 512 * L * F * (2 : ℚ) ^ (-(thetaExponent : ℤ))) * b := by
  have haccurate := unskippedGroupFailure_false source target parent b P thetaExponent tau F child initial
    (fun i s => current (i, s)) Q _ draw gamma hfailure
  exact (rationalWideStepCone_le_group parent representatives P parentInitial L old current groups q _ hselected).trans
    (chooseCellGroup_cone_bound source target parent b P F thetaExponent Q tau a parentInitial child initial
      (fun i s => current (i, s)) cell hnonempty draw specified hspecified delta L gamma hF hL htau
      hspatial haccurate action haction q)


section PhysicalNode

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A))
  (node : PhysicalNode M J) (hbelow : node.1.val < J)

local notation "history" => physicalBandHistory source target U N P F A T delta choices node hbelow
local notation "groups" => physicalNodeGroups source target U N P F A T delta choices node hbelow
local notation "online" => physicalNodeOnline source target U N P F A T delta choices node hbelow
local notation "cone" => physicalNodeCone source target U N P F A T delta choices node hbelow
local notation "onlineValue" => physicalNodeOnlineValue source target U N P F A T delta choices node hbelow
local notation "parent" => physicalSourceInterval source.length node
local notation "representatives" => stageRepresentatives source target U N P F A node
local notation "initialParent" => fun r => stageInitial source target U N P F A (node, r)
local notation "L" => (128 * F : ℚ)

/-- Literal candidate membership makes the online option present. -/
theorem physicalNode_next_eq (hleaf : ¬ (parent).hi - (parent).lo ≤ 1)
    (t : ℕ) (q : TargetInterval target.length) (action : PhysicalRationalAction M target.length)
    (haction : action ∈ online t q) :
    (physicalRefinement source target U N P F A T delta choices node (t + 1) q : ℝ) =
      refinementUpdate (delta : ℝ) (cone t q : ℝ) (onlineValue t q : ℝ) := by
  obtain ⟨value, hvalue, _, hstep⟩ := rationalWideStep_online_exists parent representatives P initialParent L delta
    (history t) (history (t + 1)) (groups t) (online t q) q action haction
  rw [physicalRefinement_succ source target U N P F A T delta choices node hbelow hleaf]
  change (rationalWideStep parent representatives P initialParent L delta
      (history t) (history (t + 1)) (groups t) (online t q) q : ℝ) = _
  rw [hstep]
  congr 1
  simp only [physicalNodeOnlineValue, hvalue, Option.getD_some]

/-- The actual online minimum is at most any listed shared band action. -/
theorem physicalNode_online_le (t : ℕ) (q r : TargetInterval target.length)
    (action : Fin M → TargetInterval target.length)
    (haction : sharedBandRationalAction r action ∈ online t q) :
    (onlineValue t q : ℝ) ≤ (L : ℝ) * targetEndpointDistance q r +
      ∑ i, (history (t + 1) (i, action i) : ℝ) := by
  obtain ⟨value, hvalue, hle⟩ := rationalOnlineMinimum_le_member
    ((online t q).map (rationalActionValue (fun q r => targetEndpointDistance q r) L (history (t + 1)) q))
    (rationalActionValue (fun q r => targetEndpointDistance q r) L (history (t + 1)) q
      (sharedBandRationalAction r action))
    (List.mem_map.mpr ⟨sharedBandRationalAction r action, haction, rfl⟩)
  have hvalueEq : onlineValue t q = value := by
    simp only [physicalNodeOnlineValue, hvalue, Option.getD_some]
  rw [hvalueEq]
  simpa only [rationalActionValue, sharedBandRationalAction, Rat.cast_add, Rat.cast_mul,
    Rat.cast_sum, Rat.cast_natCast, Rat.cast_zero, add_zero] using (Rat.cast_le (K := ℝ)).mpr hle

/-- The old-index wide candidate remains one of the literal cone options. -/
theorem physicalNode_cone_le_old (b : ℕ) (tau theta : ℚ) (r q : TargetInterval target.length)
    (child : Fin M → TargetInterval target.length → ℚ) (hrep : (b, r) ∈ representatives)
    (action : Fin M → TargetInterval target.length)
    (haction : action ∈ representativeBandActions source target parent r b P tau theta child) (t : ℕ) :
    (cone t q : ℝ) ≤ (L : ℝ) * targetEndpointDistance q r + ∑ i, (history t (i, action i) : ℝ) := by
  have hwide := sharedBandRationalAction_wide source target parent r representatives b P tau theta
    child hrep action haction
  have hcone := rationalWideStepCone_le_wide parent representatives P initialParent L
    (history t) (history (t + 1)) (groups t) q _ hwide
  simpa only [physicalNodeCone, rationalActionValue, sharedBandRationalAction,
    Rat.cast_add, Rat.cast_mul, Rat.cast_sum, Rat.cast_natCast, Rat.cast_zero, add_zero] using
    (Rat.cast_le (K := ℝ)).mpr hcone

/-- True cost is bounded by the actual connection charge and clipped
comparison children; no assumption about clipped warmup masses is needed. -/
theorem physicalNode_comparison_lower (hM : 0 < M) (hF : 1 ≤ F)
    (b : ℕ) (tau theta : ℚ) (r q : TargetInterval target.length)
    (child : Fin M → TargetInterval target.length → ℚ)
    (comparison : Fin M → TargetInterval target.length)
    (hc : comparison ∈ representativeBandActions source target parent r b P tau theta child) (t : ℕ) :
    (stateEditCost (physicalSource source node) target q : ℝ) ≤
      (L : ℝ) * targetEndpointDistance q r + ∑ i,
        max (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (comparison i) : ℝ)
          (history t (i, comparison i) : ℝ) := by
  have hzero := representativeBandActions_zero_connection source target parent r b P tau theta child comparison hc
  have hsplit := zero_connection_cost_sum_lower source target hM parent r comparison hzero
  have hspatial : (stateEditCost (physicalSource source node) target q : ℝ) ≤
      stateEditCost (physicalSource source node) target r + (targetEndpointDistance q r : ℝ) := by
    exact_mod_cast stateEditCost_spatial (physicalSource source node) target q r
  have hsum : (∑ i, (stateEditCost
      (physicalSource source (physicalChild node hbelow i)) target (comparison i) : ℝ)) ≤
      ∑ i, max (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (comparison i) : ℝ)
        (history t (i, comparison i) : ℝ) := sum_le_sum fun i _ => le_max_left _ _
  have hLR : (1 : ℝ) ≤ (L : ℝ) := by
    have hFQ : (1 : ℚ) ≤ F := by exact_mod_cast hF
    simpa only [Rat.cast_one] using
      (Rat.cast_le (K := ℝ)).mpr (by linarith only [hFQ] : (1 : ℚ) ≤ L)
  have hcharge := mul_le_mul_of_nonneg_right hLR (Nat.cast_nonneg (α := ℝ) (targetEndpointDistance q r))
  change (stateEditCost (physicalSource source node) target r : ℝ) ≤
    ∑ i, (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (comparison i) : ℝ) at hsplit
  linarith only [hsplit, hspatial, hsum, hcharge]


variable (hM : 0 < M) (hsize : source.length + target.length ≤ N)
  (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (hT : 0 < T)

include hM hsize hP hF hA hseed hT in
/-- The selected whole-cell representative supplies the actual physical
cone inequality on the actual estimator-success event. -/
theorem physicalNode_group_bound (b thetaExponent Q : ℕ) (tau gamma : ℚ)
    (htau : 0 < tau) (hdelta : 0 ≤ delta) (cell : ℕ × ℕ)
    (hnonempty : physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent tau cell ≠ [])
    (specified : UnskippedBand source target parent b P thetaExponent tau F
      (physicalBandChildMassTable source target U N P F A T node hbelow)
      (physicalBandChildInitial source target U N P F A node hbelow))
    (hspecified : specified ∈ physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent tau cell)
    (t : ℕ) (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (hselected : (physicalNodeSelectedGroup source target U N P F A T delta choices node hbelow
      b thetaExponent Q tau cell hnonempty t draw).rationalAction ∈ groups t)
    (hfailure : physicalNodeGroupFailure source target U N P F A T delta choices node hbelow
      b thetaExponent Q tau cell t draw gamma = false)
    (action : Fin M → TargetInterval target.length) (haction : action ∈ specified.actions)
    (q : TargetInterval target.length) :
    (cone t q : ℝ) ≤ (1 + (delta : ℝ)) *
        ((L : ℝ) * targetEndpointDistance q specified.center + ∑ i, (history (t + 1) (i, action i) : ℝ)) +
      ((2 * gamma + 512 * L * F * (2 : ℚ) ^ (-(thetaExponent : ℤ)) : ℚ) : ℝ) * b := by
  have hLR : (2 : ℚ) ≤ L := by
    have hFQ : (1 : ℚ) ≤ F := by exact_mod_cast hF
    linarith only [hFQ]
  have hgroup := rationalWideStepCone_group_bound source target parent representatives b P F thetaExponent Q tau
    (refinementFactor A F) initialParent
    (physicalBandChildMassTable source target U N P F A T node hbelow)
    (physicalBandChildInitial source target U N P F A node hbelow)
    (history t) (history (t + 1)) cell hnonempty draw specified hspecified (groups t) hselected
    delta L gamma hF hLR htau
    (fun i s s' => physicalRefinement_spatial source target hM U N P F A hsize hP hF hA hseed
      T hT delta hdelta choices (physicalChild node hbelow i) (t + 1) s s')
    hfailure action haction q
  have hcharge : (0 : ℚ) ≤ L * targetEndpointDistance q specified.center :=
    mul_nonneg (by linarith only [hLR]) (Nat.cast_nonneg _)
  have hslack := mul_nonneg hdelta hcharge
  have hbound : cone t q ≤ (1 + delta) *
      (L * targetEndpointDistance q specified.center + ∑ i, history (t + 1) (i, action i)) +
      (2 * gamma + 512 * L * F * (2 : ℚ) ^ (-(thetaExponent : ℤ))) * b := by
    change cone t q ≤ _ at hgroup
    nlinarith only [hgroup, hslack]
  exact_mod_cast hbound


include hM hsize hP hF hA hseed hT in
 theorem physicalNode_clipped_upper (t : ℕ) (q : TargetInterval target.length) :
    max (stateEditCost (physicalSource source node) target q : ℝ)
      (physicalRefinement source target U N P F A T delta choices node t q : ℝ) ≤
        2 * (F : ℝ) * stateEditCost (physicalSource source node) target q := by
  have hstage := physicalRefinement_stage_bounds source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices node t q
  have hupperQ := (hstage.2.1.trans (hstage.2.2.1.trans hstage.2.2.2.1)).trans hstage.2.2.2.2
  have hupper : (physicalRefinement source target U N P F A T delta choices node t q : ℝ) ≤
      2 * (F : ℝ) * stateEditCost (physicalSource source node) target q := by exact_mod_cast hupperQ
  have hFR : (1 : ℝ) ≤ F := by exact_mod_cast hF
  have hc : (0 : ℝ) ≤ stateEditCost (physicalSource source node) target q := Nat.cast_nonneg _
  exact max_le (by nlinarith only [hFR, hc]) hupper

include hM hsize hP hF hA hseed hT in
/-- Deterministic first-crossing transfer for the complete physical
recurrence, using its actual sampled candidate lists and group-error test. -/
theorem physicalNode_firstCrossing_regret_oai
    (hleaf : ¬ (parent).hi - (parent).lo ≤ 1)
    (b thetaExponent Q : ℕ) (tau gamma κ : ℚ) (htau : 0 < tau)
    (hdelta : 0 < delta) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (cell : ℕ × ℕ)
    (hnonempty : physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent tau cell ≠ [])
    (specified : UnskippedBand source target parent b P thetaExponent tau F
      (physicalBandChildMassTable source target U N P F A T node hbelow)
      (physicalBandChildInitial source target U N P F A node hbelow))
    (hspecified : specified ∈ physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent tau cell)
    (hrep : (b, specified.center) ∈ representatives)
    (q : TargetInterval target.length)
    (hb : (b : ℝ) ≤ stateEditCost (physicalSource source node) target q)
    (comparison : Fin M → TargetInterval target.length) (hc : comparison ∈ specified.actions)
    (sample : ℕ → Fin M → TargetInterval target.length) (hsample : ∀ t, sample t ∈ specified.actions)
    (draw : ℕ → ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (honline : ∀ t, sharedBandRationalAction specified.center (sample t) ∈ online t q)
    (hselected : ∀ t, (physicalNodeSelectedGroup source target U N P F A T delta choices node hbelow
      b thetaExponent Q tau cell hnonempty t (draw t)).rationalAction ∈ groups t)
    (herror : 2 * gamma + 512 * L * F * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ κ * delta)
    (S : ℕ) :
    let c : ℝ := stateEditCost (physicalSource source node) target q
    let charge : ℝ := (L : ℝ) * targetEndpointDistance q specified.center
    let clipped := physicalComparisonClipped source target U N P F A T delta choices node hbelow comparison
    let failure := fun t => physicalNodeGroupFailure source target U N P F A T delta choices node hbelow
      b thetaExponent Q tau cell t (draw t) gamma
    let crossing := firstCrossing specified.actions.toFinset S
      (fun t => bandActionCost charge (fun t coordinate => (history t coordinate : ℝ)) (t + 1)) c
    (∑ t ∈ range S,
      (max c (physicalRefinement source target U N P F A T delta choices node (t + 1) q : ℝ) -
        charge - clipped (t + 1))) ≤
      (∑ t ∈ range crossing, sampledPrefixRegret charge (κ : ℝ)
        (fun t coordinate => (history t coordinate : ℝ)) clipped sample t) +
          2 * (delta : ℝ) * c + 2 * (F : ℝ) * c *
            ∑ t ∈ range S, (if failure t then (1 : ℝ) else 0) := by
  let c : ℝ := stateEditCost (physicalSource source node) target q
  let charge : ℝ := (L : ℝ) * targetEndpointDistance q specified.center
  let table := fun t coordinate => (history t coordinate : ℝ)
  let clipped := physicalComparisonClipped source target U N P F A T delta choices node hbelow comparison
  let failure := fun t => physicalNodeGroupFailure source target U N P F A T delta choices node hbelow
    b thetaExponent Q tau cell t (draw t) gamma
  let error : ℚ := 2 * gamma + 512 * L * F * (2 : ℚ) ^ (-(thetaExponent : ℤ))
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hFR : (1 : ℝ) ≤ F := by exact_mod_cast hF
  have hδR : (0 : ℝ) < delta := (Rat.cast_pos (K := ℝ)).mpr hdelta
  have hκR : (0 : ℝ) ≤ κ := (Rat.cast_nonneg (K := ℝ)).mpr hκ
  have hκone : (κ : ℝ) ≤ 1 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hκhalf
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
    linarith only [h]
  have herrorQ : error ≤ κ * delta := herror
  have herrorR : (error : ℝ) ≤ (κ : ℝ) * delta := by
    simpa only [Rat.cast_mul] using (Rat.cast_le (K := ℝ)).mpr herrorQ
  have herrorScaled := mul_le_mul_of_nonneg_right herrorR (Nat.cast_nonneg (α := ℝ) b)
  have hκδ := mul_le_mul_of_nonneg_right hκone hδR.le
  have hκδb := mul_le_mul_of_nonneg_right hκδ (Nat.cast_nonneg (α := ℝ) b)
  have hδbc := mul_le_mul_of_nonneg_left hb hδR.le
  have herrorCross : (error : ℝ) * b ≤ (delta : ℝ) * c := by
    nlinarith only [herrorScaled, hκδb, hδbc]
  have hnext (t : ℕ) := physicalNode_next_eq source target U N P F A T delta choices node hbelow
    hleaf t q _ (honline t)
  dsimp only
  simp_rw [hnext]
  apply refinement_firstCrossing_regret specified.actions.toFinset S table clipped sample
    (fun t => (cone t q : ℝ)) (fun t => (onlineValue t q : ℝ)) failure charge c b F delta κ error
    hc0 hFR hδR hκR hb herrorScaled herrorCross
  · intro action _
    apply antitone_nat_of_succ_le
    intro t
    unfold bandActionCost
    apply add_le_add le_rfl
    apply sum_le_sum
    intro i _
    exact (Rat.cast_le (K := ℝ)).mpr
      (physicalBandHistory_nonincreasing source target U N P F A T delta choices node hbelow t (i, action i))
  · intro t _
    exact List.mem_toFinset.mpr (hsample t)
  · intro t _
    exact physicalNode_comparison_lower source target U N P F A T delta choices node hbelow hM hF
      b tau ((2 : ℚ) ^ (-(thetaExponent : ℤ))) specified.center q
      (physicalBandChildMassTable source target U N P F A T node hbelow) comparison hc t
  · intro t _
    exact physicalNode_online_le source target U N P F A T delta choices node hbelow t q specified.center
      (sample t) (honline t)
  · intro t _ action ha
    exact physicalNode_cone_le_old source target U N P F A T delta choices node hbelow
      b tau ((2 : ℚ) ^ (-(thetaExponent : ℤ))) specified.center q
      (physicalBandChildMassTable source target U N P F A T node hbelow) hrep action
      (List.mem_toFinset.mp ha) t
  · intro t _ hf action ha
    exact physicalNode_group_bound source target U N P F A T delta choices node hbelow hM hsize hP hF hA hseed hT
      b thetaExponent Q tau gamma htau hdelta.le cell hnonempty specified hspecified t (draw t)
      (hselected t) hf action (List.mem_toFinset.mp ha) q
  · intro t _
    rw [← hnext t]
    exact physicalNode_clipped_upper source target U N P F A T delta choices node hM hsize hP hF hA hseed hT
      (t + 1) q

end PhysicalNode

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.physicalNode_firstCrossing_regret_oai.{u_1} := @OAI.EditApproximation.physicalNode_firstCrossing_regret_oai.{u_1}
