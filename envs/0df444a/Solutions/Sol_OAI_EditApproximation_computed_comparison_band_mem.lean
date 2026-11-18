-- Prove2me | solution 1 for OAI.EditApproximation.computed_comparison_band_mem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:23:54.226629+00:00
-- url     : https://prove2.me/submissions/74028fc7-028a-4f13-af9e-75ada92d757f

import Mathlib
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_OAIQ361V3Ea000
import Definitions.Def_OAIQ361V3Ea001

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BalancedIntervals
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.balancedCutWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The actual balanced interval cuts

The fixed interval tree uses cuts `l + floor(i*width/M)`. Their substring
pieces concatenate exactly to the parent, including repeated cuts and
empty pieces. These facts instantiate optimal alignment splitting on the
manuscript's actual source intervals.
-/

namespace EditApproximation



theorem balancedCut_zero (lo width M : ℕ) : balancedCut lo width M 0 = lo := by
  simp [balancedCut]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ActualActionValues
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterSlack
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Explicit slack at the large-input cutoff

The cutoff is handled symbolically: no expression with an astronomically
large exponent is expanded. The small-growth estimate supplies the
induction step. This proves the generous polynomial-versus-binary bound
used throughout the manuscript's numerical estimates.
-/

namespace EditApproximation

theorem polynomial_binary_growth_step (degree m : ℕ)
    (hsize : 4 * degree ≤ 2 * m + 1) :
    (2 * (m : ℝ) + 3) ^ degree ≤ 2 * (2 * (m : ℝ) + 1) ^ degree := by
  let d : ℝ := 2 * m + 1
  have hd : 0 < d := by dsimp [d] <;> positivity
  have hsizeR : 4 * (degree : ℝ) ≤ d := by
    dsimp only [d]
    exact_mod_cast hsize
  have hsmall : (degree : ℝ) * (2 / d) ≤ 1 / 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).2
    nlinarith
  have hbound : (1 + 2 / d) ^ degree ≤ 2 :=
    (small_growth_pow degree (by positivity) hsmall).trans (by nlinarith)
  have hrew : 2 * (m : ℝ) + 3 = d * (1 + 2 / d) := by
    dsimp [d]
    field_simp
    ring
  rw [hrew, mul_pow]
  have hmul := mul_le_mul_of_nonneg_left hbound (pow_nonneg hd.le degree)
  simpa only [d, mul_comm] using hmul

theorem astronomical_polynomial_bound (ell : ℕ) (hell : 2 ^ 1000 ≤ ell) :
    (ell : ℝ) ^ 20000 ≤ (2 : ℝ) ^ (ell / 2) := by
  let m0 : ℕ := 2 ^ 999
  have hbaseSize : (2 * (m0 : ℝ) + 1) ≤ (2 : ℝ) ^ 1001 := by
    have hm0 : (m0 : ℝ) = (2 : ℝ) ^ 999 := by
      simp only [m0, Nat.cast_pow, Nat.cast_ofNat]
    have hone : (1 : ℝ) ≤ m0 := by rw [hm0]; exact one_le_pow₀ (by norm_num)
    have hbig : (2 : ℝ) ^ 1001 = 4 * (m0 : ℝ) := by
      rw [show 1001 = 999 + 2 by decide, pow_add, ← hm0]
      norm_num only [pow_two]
      ring
    rw [hbig]
    calc
      2 * (m0 : ℝ) + 1 ≤ 2 * (m0 : ℝ) + m0 := add_le_add le_rfl hone
      _ = 3 * (m0 : ℝ) := by ring
      _ ≤ 4 * (m0 : ℝ) := mul_le_mul_of_nonneg_right (by norm_num)
        ((by norm_num : (0 : ℝ) ≤ 1).trans hone)
  have hbasePower := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * (m0 : ℝ) + 1)
    hbaseSize 20000
  rw [← pow_mul] at hbasePower
  have hexponent : 1001 * 20000 ≤ m0 := by
    have hsmall : 1001 * 20000 ≤ (2 : ℕ) ^ 25 := by norm_num
    exact hsmall.trans (pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (by decide : 25 ≤ 999))
  have hbase : (2 * (m0 : ℝ) + 1) ^ 20000 ≤ (2 : ℝ) ^ m0 :=
    hbasePower.trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexponent)
  have hgrowth : ∀ m : ℕ, m0 ≤ m → (2 * (m : ℝ) + 1) ^ 20000 ≤ (2 : ℝ) ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hbase
    | succ m hm ih =>
      have hsize0 : 4 * 20000 ≤ 2 * m0 + 1 := by omega
      have hstep := polynomial_binary_growth_step 20000 m (by omega)
      calc
        (2 * ((m + 1 : ℕ) : ℝ) + 1) ^ 20000 = (2 * (m : ℝ) + 3) ^ 20000 := by
          congr 1
          push_cast
          ring
        _ ≤ 2 * (2 * (m : ℝ) + 1) ^ 20000 := hstep
        _ ≤ 2 * (2 : ℝ) ^ m := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 : ℝ) ^ (m + 1) := by rw [pow_succ]; ring
  have hcutoff : 2 ^ 1000 = 2 * m0 := by
    dsimp only [m0]
    rw [show 1000 = 999 + 1 by decide, pow_succ]
    exact Nat.mul_comm _ _
  have hm : m0 ≤ ell / 2 := by omega
  have hellR : (ell : ℝ) ≤ 2 * ((ell / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show ell ≤ 2 * (ell / 2) + 1 by omega)
  exact (pow_le_pow_left₀ (Nat.cast_nonneg ell) hellR 20000).trans (hgrowth _ hm)

theorem astronomical_parameter_slack (ell : ℕ) (H : ℝ)
    (hell : 2 ^ 1000 ≤ ell) (hH : (2 : ℝ) ^ (ell / 2) ≤ H) :
    (ell : ℝ) ^ 20000 ≤ H :=
  (astronomical_polynomial_bound ell hell).trans hH

/-- The fourth-root scale has ample polynomial slack. -/
theorem fourth_root_polynomial_slack {ell H quarterRoot : ℝ}
    (hell : 1 ≤ ell) (hH : ell ^ 20000 ≤ H)
    (hroot : 0 ≤ quarterRoot) (hrootPower : quarterRoot ^ 4 = H) :
    ell ^ 5000 ≤ quarterRoot := by
  apply (pow_le_pow_iff_left₀ (pow_nonneg (zero_le_one.trans hell) 5000)
    hroot (by decide : 4 ≠ 0)).mp
  rw [← pow_mul, hrootPower]
  exact hH

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Parameters
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Integer-computed parameters

The logarithms and fourth roots in Section 2 are computed by natural bit
lengths and nested integer square roots. No real arithmetic oracle is
used to form the algorithm's parameters.
-/

namespace EditApproximation
















theorem inputSmallLog_bounds (N : ℕ) (hN : 0 < N) :
    heightExponent N ≤ inputSmallLog N ∧ inputSmallLog N < 2 * heightExponent N := by
  have hpos := heightExponent_pos N hN
  have hone : 1 ≤ heightExponent N := hpos
  have hrange := rejectionWord_range (heightExponent N) hpos
  simpa only [inputSmallLog, smallLogExponent, rejectionBitCount, max_eq_right hone] using hrange

theorem inputHeight_binary_slack (N : ℕ) (hN : 0 < N) :
    (2 : ℝ) ^ (inputSmallLog N / 2) ≤ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hexponent : inputSmallLog N / 2 ≤ heightExponent N := by omega
  have hpower := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexponent
  simpa only [inputHeight, Nat.cast_pow, Nat.cast_ofNat] using hpower

theorem inputHeight_polynomial_slack (N : ℕ) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) :
    (inputSmallLog N : ℝ) ^ 20000 ≤ inputHeight N :=
  astronomical_parameter_slack _ _ hell (inputHeight_binary_slack N hN)

theorem heightQuarterRoot_fourth_power (N : ℕ) :
    heightQuarterRoot N ^ 4 = inputHeight N := by
  unfold heightQuarterRoot
  rw [show (Real.sqrt (Real.sqrt (inputHeight N : ℝ))) ^ 4 =
    ((Real.sqrt (Real.sqrt (inputHeight N : ℝ))) ^ 2) ^ 2 by ring]
  rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandParameters
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Computed numerical slack for comparison-band coverage at non-bad nodes. -/

namespace EditApproximation

theorem computed_branching_fourth_power_le_quarterRoot (N : ℕ) :
    ((integerParameters N).M : ℝ) ^ 4 ≤ heightQuarterRoot N := by
  have hexponent : 16 * (heightExponent N / 20) ≤ heightExponent N := by
    have h := Nat.div_mul_le_self (heightExponent N) 20
    omega
  have hpower : ((integerParameters N).M : ℝ) ^ 16 ≤ inputHeight N := by
    simp only [integerParameters, Nat.cast_pow, Nat.cast_ofNat, inputHeight]
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  apply (pow_le_pow_iff_left₀ (by positivity : (0 : ℝ) ≤ ((integerParameters N).M : ℝ) ^ 4)
    (Real.sqrt_nonneg _) (by decide : 4 ≠ 0)).mp
  change (((integerParameters N).M : ℝ) ^ 4) ^ 4 ≤ heightQuarterRoot N ^ 4
  rw [← pow_mul, heightQuarterRoot_fourth_power]
  exact hpower

theorem band_root_slack {ell root M : ℝ} (hell : 2 ≤ ell) (hroot : 0 ≤ root)
    (hlarge : ell ^ 5000 ≤ root) (_hM : 0 ≤ M) (hMfour : M ^ 4 ≤ root) :
    128 * ell ^ 90 * M ^ 2 ≤ root := by
  have hellone : 1 ≤ ell := by linarith
  have hcoef : (16384 : ℝ) ≤ ell ^ 14 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hell 14
    norm_num at h
    exact h
  have hbig : 16384 * ell ^ 180 ≤ root := by
    calc
      16384 * ell ^ 180 ≤ ell ^ 14 * ell ^ 180 :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = ell ^ 194 := by rw [← pow_add]
      _ ≤ ell ^ 5000 := pow_le_pow_right₀ hellone (by decide)
      _ ≤ root := hlarge
  have hproduct := mul_le_mul hMfour hbig (by positivity : (0 : ℝ) ≤ 16384 * ell ^ 180) hroot
  apply (sq_le_sq₀ (by positivity : 0 ≤ 128 * ell ^ 90 * M ^ 2) hroot).mp
  calc
    (128 * ell ^ 90 * M ^ 2) ^ 2 = M ^ 4 * (16384 * ell ^ 180) := by ring
    _ ≤ root * root := hproduct
    _ = root ^ 2 := by ring

theorem nonbad_band_numerical_bound {ell root M b K G W : ℝ}
    (hell : 2 ≤ ell) (hM : 1 ≤ M) (hb : 0 ≤ b)
    (hroot : 128 * ell ^ 90 * M ^ 2 ≤ root)
    (_hK : 0 ≤ K) (_hG : 0 ≤ G) (hW : 0 ≤ W)
    (hKsmall : K ≤ b / root) (hGsmall : G ≤ b / root) (hWsmall : W ≤ 8 * ell * b) :
    Real.sqrt (K * W) + 2 * G ≤ (1 / ell ^ 4) * (1 / ell ^ 40) * b / M := by
  have hellpos : 0 < ell := by linarith
  have hellone : 1 ≤ ell := by linarith
  have hMpos : 0 < M := by linarith
  have hMtwo : M ≤ M ^ 2 := by nlinarith only [hM]
  have hrootpos : 0 < root := (by positivity : 0 < 128 * ell ^ 90 * M ^ 2).trans_le hroot
  have hscale : 32 * ell ^ 89 * M ^ 2 ≤ root := by
    calc
      32 * ell ^ 89 * M ^ 2 ≤ 128 * ell ^ 90 * M ^ 2 := by
        have hp : ell ^ 89 ≤ ell ^ 90 := pow_le_pow_right₀ hellone (by decide : 89 ≤ 90)
        have hc : 32 * ell ^ 89 ≤ 128 * ell ^ 90 :=
          mul_le_mul (by norm_num : (32 : ℝ) ≤ 128) hp (by positivity) (by norm_num)
        exact mul_le_mul_of_nonneg_right hc (sq_nonneg M)
      _ ≤ root := hroot
  have hscale' : 4 * ell ^ 44 * M ≤ root := by
    calc
      4 * ell ^ 44 * M ≤ 128 * ell ^ 90 * M ^ 2 := by
        have hp : ell ^ 44 ≤ ell ^ 90 := pow_le_pow_right₀ hellone (by decide : 44 ≤ 90)
        have hc : 4 * ell ^ 44 ≤ 128 * ell ^ 90 :=
          mul_le_mul (by norm_num : (4 : ℝ) ≤ 128) hp (by positivity) (by norm_num)
        exact mul_le_mul hc hMtwo hMpos.le (by positivity)
      _ ≤ root := hroot
  have hKW : K * W ≤ (8 * ell * b ^ 2) / root := by
    calc
      K * W ≤ (b / root) * (8 * ell * b) :=
        mul_le_mul hKsmall hWsmall hW (div_nonneg hb hrootpos.le)
      _ = (8 * ell * b ^ 2) / root := by ring
  have hsquare : K * W ≤ (b / (2 * ell ^ 44 * M)) ^ 2 := by
    calc
      K * W ≤ (8 * ell * b ^ 2) / root := hKW
      _ ≤ b ^ 2 / (4 * ell ^ 88 * M ^ 2) := by
        apply (div_le_div_iff₀ hrootpos (by positivity : 0 < 4 * ell ^ 88 * M ^ 2)).2
        have h := mul_le_mul_of_nonneg_right hscale (sq_nonneg b)
        nlinarith only [h, show (8 * ell * b ^ 2) * (4 * ell ^ 88 * M ^ 2) =
          (32 * ell ^ 89 * M ^ 2) * b ^ 2 by ring]
      _ = (b / (2 * ell ^ 44 * M)) ^ 2 := by field_simp <;> ring
  have hsqrt : Real.sqrt (K * W) ≤ b / (2 * ell ^ 44 * M) :=
    (Real.sqrt_le_left (by positivity)).2 hsquare
  have htwice : 2 * G ≤ b / (2 * ell ^ 44 * M) := by
    calc
      2 * G ≤ 2 * (b / root) := mul_le_mul_of_nonneg_left hGsmall (by norm_num)
      _ = (2 * b) / root := by ring
      _ ≤ b / (2 * ell ^ 44 * M) := by
        apply (div_le_div_iff₀ hrootpos (by positivity : 0 < 2 * ell ^ 44 * M)).2
        have h := mul_le_mul_of_nonneg_right hscale' hb
        nlinarith only [h]
  have hid : b / (2 * ell ^ 44 * M) + b / (2 * ell ^ 44 * M) =
      (1 / ell ^ 4) * (1 / ell ^ 40) * b / M := by
    field_simp
    ring
  exact (add_le_add hsqrt htwice).trans_eq hid

theorem computed_nonbad_band_numerical_bound (N : ℕ) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) {b K G W : ℝ}
    (hb : 0 ≤ b) (hK : 0 ≤ K) (hG : 0 ≤ G) (hW : 0 ≤ W)
    (hKsmall : K ≤ b / heightQuarterRoot N) (hGsmall : G ≤ b / heightQuarterRoot N)
    (hWsmall : W ≤ 8 * inputSmallLog N * b) :
    Real.sqrt (K * W) + 2 * G ≤
      ((rationalParameters (inputSmallLog N)).tau : ℝ) *
        ((rationalParameters (inputSmallLog N)).theta : ℝ) * b / (integerParameters N).M := by
  have helltwo : (2 : ℝ) ≤ inputSmallLog N := by
    have htwo : 2 ≤ (2 : ℕ) ^ 1000 := by
      simpa only [pow_one] using pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by decide : 1 ≤ 1000)
    exact_mod_cast htwo.trans hell
  have hroot := band_root_slack helltwo (Real.sqrt_nonneg _)
    (fourth_root_polynomial_slack (by linarith) (inputHeight_polynomial_slack N hN hell)
      (Real.sqrt_nonneg _) (heightQuarterRoot_fourth_power N))
    (Nat.cast_nonneg (integerParameters N).M) (computed_branching_fourth_power_le_quarterRoot N)
  have hM : (1 : ℝ) ≤ (integerParameters N).M := by
    exact_mod_cast (Nat.one_le_two_pow (n := heightExponent N / 20))
  have h := nonbad_band_numerical_bound helltwo hM hb hroot hK hG hW hKsmall hGsmall hWsmall
  simpa only [rationalParameters, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_natCast] using h

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Bands
attribute [-instance] _root_.OAI.EditApproximation.physicalFamilyRange_neZero
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
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

/-- The comparison prefix error is the weighted deviation plus two
warmup-mass discrepancy charges. -/
theorem comparison_prefix_prediction_error
    {point origin velocity predictedVelocity prefixMass prefixCost totalMass discrepancy deviation : ℝ}
    (hprefix : 0 ≤ prefixMass) (hprefixTotal : prefixMass ≤ totalMass)
    (hprediction : |velocity - predictedVelocity| * totalMass ≤ discrepancy)
    (hvelocity : |predictedVelocity| ≤ 1)
    (hcostLower : prefixMass - discrepancy ≤ prefixCost)
    (hcostUpper : prefixCost ≤ prefixMass)
    (hdeviation : |point - origin - velocity * prefixMass| ≤ deviation) :
    |point - origin - predictedVelocity * prefixCost| ≤ deviation + 2 * discrepancy := by
  have hcostDiff : |prefixMass - prefixCost| ≤ discrepancy := by
    rw [abs_of_nonneg (by linarith : 0 ≤ prefixMass - prefixCost)]
    linarith
  have hfirst : |(velocity - predictedVelocity) * prefixMass| ≤ discrepancy := by
    rw [abs_mul, abs_of_nonneg hprefix]
    exact (mul_le_mul_of_nonneg_left hprefixTotal (abs_nonneg _)).trans hprediction
  have hsecond : |predictedVelocity * (prefixMass - prefixCost)| ≤ discrepancy := by
    rw [abs_mul]
    have hprod := mul_le_mul hvelocity hcostDiff (abs_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hprod
  have hid : point - origin - predictedVelocity * prefixCost =
      (point - origin - velocity * prefixMass) +
        (velocity - predictedVelocity) * prefixMass +
          predictedVelocity * (prefixMass - prefixCost) := by ring
  rw [hid]
  exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    (by linarith)

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

/-- Weighted Cauchy--Schwarz controls the total absolute deviation by
the curvature times the total warmup mass. -/
theorem curvature_l1_squared_le {ι : Type*} (children : Finset ι)
    (mass gap : ι → ℝ)
    (hmass : ∀ i ∈ children, 0 ≤ mass i)
    (hzero : ∀ i ∈ children, mass i = 0 → gap i = 0)
    (hW : 0 < ∑ i ∈ children, mass i) :
    (∑ i ∈ children,
      |gap i - ((∑ j ∈ children, gap j) / (∑ j ∈ children, mass j)) * mass i|) ^ 2 ≤
      (∑ i ∈ children, mass i) *
        ((∑ i ∈ children, gap i ^ 2 / mass i) -
          (∑ i ∈ children, gap i) ^ 2 / (∑ i ∈ children, mass i)) := by
  let v := (∑ i ∈ children, gap i) / (∑ i ∈ children, mass i)
  have hterm (i : ι) (hi : i ∈ children) :
      |gap i - v * mass i| ^ 2 ≤ mass i * ((gap i - v * mass i) ^ 2 / mass i) := by
    by_cases hz : mass i = 0
    · simp only [hz, hzero i hi hz, mul_zero, sub_zero, abs_zero,
        zero_pow (by omega : 2 ≠ 0), zero_div, le_refl]
    · rw [sq_abs]
      exact le_of_eq (by field_simp)
  have hcs := sum_sq_le_sum_mul_sum_of_sq_le_mul children hmass
    (fun i hi => div_nonneg (sq_nonneg (gap i - v * mass i)) (hmass i hi)) hterm
  rw [weighted_variance_identity children mass gap hzero hW]
  exact hcs

theorem curvature_l1_le_sqrt {ι : Type*} (children : Finset ι)
    (mass gap : ι → ℝ)
    (hmass : ∀ i ∈ children, 0 ≤ mass i)
    (hzero : ∀ i ∈ children, mass i = 0 → gap i = 0)
    (hW : 0 < ∑ i ∈ children, mass i) :
    (∑ i ∈ children,
      |gap i - ((∑ j ∈ children, gap j) / (∑ j ∈ children, mass j)) * mass i|) ≤
      Real.sqrt ((∑ i ∈ children, mass i) *
        ((∑ i ∈ children, gap i ^ 2 / mass i) -
          (∑ i ∈ children, gap i) ^ 2 / (∑ i ∈ children, mass i))) := by
  apply (sq_le_sq₀ (sum_nonneg fun _ _ => abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (mul_nonneg hW.le (curvature_nonneg children mass gap hmass hzero hW))]
  exact curvature_l1_squared_le children mass gap hmass hzero hW

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SharedActions
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PrefixCosts
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

theorem realConnectionBudget_cast {n : ℕ} (start finish : ℕ) (states : List (TargetInterval n)) :
    realConnectionBudget start states finish = (connectionBudget start states finish : ℝ) := by
  induction states generalizing start with
  | nil => exact natural_distance_cast start finish
  | cons state rest ih =>
    simp only [realConnectionBudget, connectionBudget, Nat.cast_add, ih,
      natural_distance_cast]

theorem widePrefixMinimum_le_member {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (actions : List (Fin M → TargetInterval ny)) (hnonempty : actions ≠ [])
    (child : Fin M → TargetInterval ny → ℝ) (j : ℕ) (p : ℝ)
    (action : Fin M → TargetInterval ny) (haction : action ∈ actions) :
    widePrefixMinimum parent r actions hnonempty child j p ≤ widePrefixCost parent r action child j p :=
  finiteMinimum_le_member _ _ (List.mem_map.mpr ⟨action, haction, rfl⟩)

theorem le_widePrefixMinimum {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (actions : List (Fin M → TargetInterval ny)) (hnonempty : actions ≠ [])
    (child : Fin M → TargetInterval ny → ℝ) (j : ℕ) (p lower : ℝ)
    (hlower : ∀ action ∈ actions, lower ≤ widePrefixCost parent r action child j p) :
    lower ≤ widePrefixMinimum parent r actions hnonempty child j p := by
  apply (le_finiteMinimum_iff _ _ _).2
  refine ⟨hlower _ (List.head_mem hnonempty), ?_⟩
  intro value hvalue
  obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hvalue
  exact hlower action ha

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PrefixComparison
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
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

theorem realConnectionBudget_nonneg {n : ℕ} (start finish : ℝ)
    (states : List (TargetInterval n)) : 0 ≤ realConnectionBudget start states finish := by
  induction states generalizing start with
  | nil => exact abs_nonneg _
  | cons state rest ih => exact add_nonneg (abs_nonneg _) (ih state.hi)

/-- Exact splitting at the first endpoint of the remaining suffix. -/
theorem realConnectionBudget_split {n : ℕ} (states : List (TargetInterval n))
    (start : ℝ) (finish j : ℕ) :
    realConnectionBudget start states finish =
      realConnectionBudget start (states.take j) (connectionPrefixBoundary states finish j) +
      realConnectionBudget (connectionPrefixBoundary states finish j) (states.drop j) finish := by
  induction states generalizing start j with
  | nil => simp [connectionPrefixBoundary, realConnectionBudget]
  | cons state rest ih =>
    cases j with
    | zero => simp [connectionPrefixBoundary, realConnectionBudget]
    | succ j =>
      simp only [List.take_succ_cons, List.drop_succ_cons, connectionPrefixBoundary,
        realConnectionBudget]
      rw [ih (state.hi : ℝ) j]
      dsimp only [connectionPrefixBoundary]
      ring

/-- A detour through an arbitrary real cut only increases the budget. -/
theorem realConnectionBudget_append_le {n : ℕ} (before after : List (TargetInterval n))
    (start finish cut : ℝ) :
    realConnectionBudget start (before ++ after) finish ≤
      realConnectionBudget start before cut + realConnectionBudget cut after finish := by
  induction before generalizing start with
  | nil =>
    cases after with
    | nil => exact abs_sub_le start cut finish
    | cons state rest =>
      have h := abs_sub_le start cut (state.lo : ℝ)
      simp only [List.nil_append, realConnectionBudget]
      linarith
  | cons state rest ih =>
    have h := ih (state.hi : ℝ)
    simp only [List.cons_append, realConnectionBudget]
    linarith

theorem zero_connection_prefix_suffix {n M : ℕ} (r : TargetInterval n)
    (comparison : Fin M → TargetInterval n) (j : ℕ)
    (hzero : endpointActionConnection r comparison = 0) :
    realConnectionBudget r.lo ((List.ofFn comparison).take j)
        (connectionPrefixBoundary (List.ofFn comparison) r.hi j) = 0 ∧
      realConnectionBudget (connectionPrefixBoundary (List.ofFn comparison) r.hi j)
        ((List.ofFn comparison).drop j) r.hi = 0 := by
  have hsplit := realConnectionBudget_split (List.ofFn comparison) (r.lo : ℝ) r.hi j
  have hfull : realConnectionBudget r.lo (List.ofFn comparison) r.hi = 0 := by
    rw [realConnectionBudget_cast]
    exact_mod_cast hzero
  rw [hfull] at hsplit
  have hbefore := realConnectionBudget_nonneg (r.lo : ℝ)
    (connectionPrefixBoundary (List.ofFn comparison) r.hi j)
    ((List.ofFn comparison).take j)
  have hafter := realConnectionBudget_nonneg
    (connectionPrefixBoundary (List.ofFn comparison) r.hi j) (r.hi : ℝ)
    ((List.ofFn comparison).drop j)
  constructor <;> linarith

theorem comparisonPrefixSplice_list {n M : ℕ} (before comparison : Fin M → TargetInterval n)
    (j : ℕ) (hj : j ≤ M) :
    List.ofFn (comparisonPrefixSplice before comparison j) =
      (List.ofFn before).take j ++ (List.ofFn comparison).drop j := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_take, List.length_drop,
      Nat.min_eq_left hj]
    omega
  · intro i hi hi'
    simp only [List.getElem_ofFn, comparisonPrefixSplice]
    by_cases hij : i < j
    · rw [ite_eq_left hij, List.getElem_append_left]
      · rw [List.getElem_take, List.getElem_ofFn]
      · simp only [List.length_take, List.length_ofFn, Nat.min_eq_left hj]
        exact hij
    · rw [ite_eq_right hij, List.getElem_append_right]
      · simp only [List.length_take, List.length_ofFn, Nat.min_eq_left hj,
          List.getElem_drop, List.getElem_ofFn]
        congr 1
        apply Fin.ext
        change i = j + (i - j)
        omega
      · simp only [List.length_take, List.length_ofFn, Nat.min_eq_left hj]
        omega

theorem comparisonPrefixSplice_mem {nx ny M b P : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (before comparison : Fin M → TargetInterval ny) (j : ℕ)
    (hbefore : before ∈ wideActionList M parent r b P)
    (hcomparison : comparison ∈ wideActionList M parent r b P) :
    comparisonPrefixSplice before comparison j ∈ wideActionList M parent r b P := by
  apply finiteAssignments_complete
  intro i
  unfold comparisonPrefixSplice
  split_ifs with hi
  · exact finiteAssignments_sound M _ before hbefore i
  · exact finiteAssignments_sound M _ comparison hcomparison i

theorem connectionPrefixBoundary_ofFn {n M : ℕ} (states : Fin M → TargetInterval n)
    (finish : ℕ) (j : Fin M) :
    connectionPrefixBoundary (List.ofFn states) finish j.val = (states j).lo := by
  simp only [connectionPrefixBoundary, List.head?_drop, List.getElem?_ofFn,
    dite_eq_left j.isLt, Option.map_some, Option.getD_some]

/-- Internal comparison cuts are exactly the next child's left shift. -/
theorem comparisonPrefixShift_at_child {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (comparison : Fin M → TargetInterval ny) (j : Fin M) :
    comparisonPrefixShift parent r comparison j.val =
      ((comparison j).lo : ℝ) - (sourceChild parent j).lo := by
  simp only [comparisonPrefixShift, connectionPrefixBoundary_ofFn, sourceChild]

theorem comparisonPrefixCost_eq {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (comparison : Fin M → TargetInterval ny)
    (child : Fin M → TargetInterval ny → ℝ) (j : ℕ)
    (hzero : endpointActionConnection r comparison = 0) :
    widePrefixCost parent r comparison child j (comparisonPrefixShift parent r comparison j) =
      comparisonPrefixValue comparison child j := by
  have hprefix := (zero_connection_prefix_suffix r comparison j hzero).1
  have hfinish : (balancedCut parent.lo (parent.hi - parent.lo) M j : ℝ) +
      comparisonPrefixShift parent r comparison j =
      connectionPrefixBoundary (List.ofFn comparison) r.hi j := by
    unfold comparisonPrefixShift
    ring
  simp only [widePrefixCost, hfinish, hprefix, zero_add, comparisonPrefixValue]

/-- An arbitrary actual wide prefix can be completed by the comparator
suffix at exactly the comparison cut. -/
theorem comparisonPrefixSplice_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (before comparison : Fin M → TargetInterval ny)
    (child : Fin M → TargetInterval ny → ℝ) (j : ℕ) (hj : j ≤ M)
    (hzero : endpointActionConnection r comparison = 0) :
    endpointActionValue r (comparisonPrefixSplice before comparison j) child ≤
      widePrefixCost parent r before child j (comparisonPrefixShift parent r comparison j) +
        (∑ i, child i (comparison i)) - comparisonPrefixValue comparison child j := by
  have hsuffix := (zero_connection_prefix_suffix r comparison j hzero).2
  have hconnection := realConnectionBudget_append_le
    ((List.ofFn before).take j) ((List.ofFn comparison).drop j) (r.lo : ℝ) (r.hi : ℝ)
    (connectionPrefixBoundary (List.ofFn comparison) r.hi j)
  rw [← comparisonPrefixSplice_list before comparison j hj,
    realConnectionBudget_cast, hsuffix, add_zero] at hconnection
  have hsum : (∑ i, child i (comparisonPrefixSplice before comparison j i)) =
      (∑ i, if i.val < j then child i (before i) else 0) +
        (∑ i, child i (comparison i)) - comparisonPrefixValue comparison child j := by
    unfold comparisonPrefixValue
    rw [← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    by_cases hij : i.val < j <;> simp [comparisonPrefixSplice, hij]
  have hfinish : (balancedCut parent.lo (parent.hi - parent.lo) M j : ℝ) +
      comparisonPrefixShift parent r comparison j =
      connectionPrefixBoundary (List.ofFn comparison) r.hi j := by
    unfold comparisonPrefixShift
    ring
  unfold endpointActionValue widePrefixCost
  rw [hfinish, hsum]
  change (connectionBudget r.lo (List.ofFn (comparisonPrefixSplice before comparison j)) r.hi : ℝ) + _ ≤ _
  linarith

/-- The comparison prefix is covered by the literal finite predictor.
The full-action lower bound is later instantiated by the actual warmup
Bellman value; no prefix estimate is assumed. -/
theorem comparisonPrefixMinimum_bounds {nx ny M b P : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (comparison : Fin M → TargetInterval ny)
    (hcomparison : comparison ∈ wideActionList M parent r b P)
    (hnonempty : wideActionList M parent r b P ≠ [])
    (child : Fin M → TargetInterval ny → ℝ) (j : ℕ) (hj : j ≤ M)
    (hzero : endpointActionConnection r comparison = 0) (fullLower : ℝ)
    (hfull : ∀ action ∈ wideActionList M parent r b P,
      fullLower ≤ endpointActionValue r action child) :
    comparisonPrefixValue comparison child j - ((∑ i, child i (comparison i)) - fullLower) ≤
        widePrefixMinimum parent r (wideActionList M parent r b P) hnonempty child j
          (comparisonPrefixShift parent r comparison j) ∧
      widePrefixMinimum parent r (wideActionList M parent r b P) hnonempty child j
          (comparisonPrefixShift parent r comparison j) ≤ comparisonPrefixValue comparison child j := by
  constructor
  · apply le_widePrefixMinimum
    intro action ha
    have hsplice := comparisonPrefixSplice_mem parent r action comparison j ha hcomparison
    have hcost := comparisonPrefixSplice_cost parent r action comparison child j hj hzero
    have hlower := hfull _ hsplice
    linarith
  · exact (widePrefixMinimum_le_member parent r _ hnonempty child j _ comparison hcomparison).trans_eq
      (comparisonPrefixCost_eq parent r comparison child j hzero)

theorem wideActionMinimum_le_member {nx ny M b P : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (hnonempty : wideActionList M parent r b P ≠ [])
    (child : Fin M → TargetInterval ny → ℝ) (action : Fin M → TargetInterval ny)
    (haction : action ∈ wideActionList M parent r b P) :
    wideActionMinimum parent r b P hnonempty child ≤ endpointActionValue r action child :=
  finiteMinimum_le_member _ _ (List.mem_map.mpr ⟨action, haction, rfl⟩)

/-- Exact finite predictor coverage with its actual wide-action minimum Z. -/
theorem comparisonPrefixMinimum_actual_bounds {nx ny M b P : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (comparison : Fin M → TargetInterval ny)
    (hcomparison : comparison ∈ wideActionList M parent r b P)
    (hnonempty : wideActionList M parent r b P ≠ [])
    (child : Fin M → TargetInterval ny → ℝ) (j : ℕ) (hj : j ≤ M)
    (hzero : endpointActionConnection r comparison = 0) :
    comparisonPrefixValue comparison child j -
        ((∑ i, child i (comparison i)) - wideActionMinimum parent r b P hnonempty child) ≤
      widePrefixMinimum parent r (wideActionList M parent r b P) hnonempty child j
        (comparisonPrefixShift parent r comparison j) ∧
      widePrefixMinimum parent r (wideActionList M parent r b P) hnonempty child j
        (comparisonPrefixShift parent r comparison j) ≤ comparisonPrefixValue comparison child j :=
  comparisonPrefixMinimum_bounds parent r comparison hcomparison hnonempty child j hj hzero
    (wideActionMinimum parent r b P hnonempty child)
    (fun action ha => wideActionMinimum_le_member parent r hnonempty child action ha)

/-- A zero connection path has exactly the endpoint length span. -/
theorem connectionBudget_zero_span {n : ℕ} (states : List (TargetInterval n))
    (start finish : ℕ) (hzero : connectionBudget start states finish = 0) :
    start ≤ finish ∧ (states.map fun state => state.hi - state.lo).sum = finish - start := by
  induction states generalizing start with
  | nil =>
    have heq : start = finish := Nat.eq_of_dist_eq_zero hzero
    subst start
    simp only [List.map_nil, List.sum_nil, Nat.sub_self, le_refl, and_self]
  | cons state rest ih =>
    have hparts : Nat.dist start state.lo + connectionBudget state.hi rest finish = 0 := hzero
    have hstart : start = state.lo := Nat.eq_of_dist_eq_zero (by omega)
    have htail : connectionBudget state.hi rest finish = 0 := by omega
    obtain ⟨horder, hsum⟩ := ih state.hi htail
    subst start
    constructor
    · exact state.ordered.trans horder
    · simp only [List.map_cons, List.sum_cons, hsum]
      have := state.ordered
      omega

/-- The comparison cut displacement is the sum of the actual target-minus-
source child length gaps in its prefix. -/
theorem comparisonPrefixShift_gap_sum {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (parent : TargetInterval source.length)
    (r : TargetInterval target.length) (comparison : Fin M → TargetInterval target.length)
    (j : ℕ) (hj : j ≤ M) (hzero : endpointActionConnection r comparison = 0) :
    comparisonPrefixShift parent r comparison j - comparisonPrefixShift parent r comparison 0 =
      ∑ i, if i.val < j then
        stateLengthGap (substring source (sourceChild parent i).lo (sourceChild parent i).hi)
          target (comparison i) else 0 := by
  let cut := connectionPrefixBoundary (List.ofFn comparison) r.hi j
  have hprefix := (zero_connection_prefix_suffix r comparison j hzero).1
  have hprefixNat : connectionBudget r.lo ((List.ofFn comparison).take j) cut = 0 := by
    rw [realConnectionBudget_cast] at hprefix
    exact_mod_cast hprefix
  obtain ⟨htargetOrder, htargetSpan⟩ := connectionBudget_zero_span
    ((List.ofFn comparison).take j) r.lo cut hprefixNat
  have htargetNat : (∑ i : Fin M with i.val < j, ((comparison i).hi - (comparison i).lo)) = cut - r.lo := by
    rw [← List.sum_take_ofFn]
    simpa only [List.map_take, List.map_ofFn, Function.comp_def] using htargetSpan
  have hsourceSpan := sourceChildren_prefix_length source hM parent j hj
  simp only [List.length_flatten, List.map_take, List.map_ofFn, Function.comp_def] at hsourceSpan
  have hsourceNat : (∑ i : Fin M with i.val < j,
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi).length) =
        balancedCut parent.lo (parent.hi - parent.lo) M j - parent.lo := by
    rw [← List.sum_take_ofFn]
    exact hsourceSpan
  have htargetReal : (∑ i : Fin M, if i.val < j then
      ((comparison i).hi : ℝ) - (comparison i).lo else 0) = (cut : ℝ) - r.lo := by
    rw [← sum_filter]
    calc
      _ = ((∑ i : Fin M with i.val < j, ((comparison i).hi - (comparison i).lo) : ℕ) : ℝ) := by
        rw [Nat.cast_sum]
        apply sum_congr rfl
        intro i hi
        rw [Nat.cast_sub (comparison i).ordered]
      _ = ((cut - r.lo : ℕ) : ℝ) := congrArg (fun a : ℕ => (a : ℝ)) htargetNat
      _ = _ := Nat.cast_sub htargetOrder
  have hsourceOrder := (balancedCut_bounds parent.lo (parent.hi - parent.lo) M j hM hj).1
  have hsourceReal : (∑ i : Fin M, if i.val < j then
      ((substring source (sourceChild parent i).lo (sourceChild parent i).hi).length : ℝ) else 0) =
        (balancedCut parent.lo (parent.hi - parent.lo) M j : ℝ) - parent.lo := by
    rw [← sum_filter]
    calc
      _ = ((∑ i : Fin M with i.val < j,
          (substring source (sourceChild parent i).lo (sourceChild parent i).hi).length : ℕ) : ℝ) := by
        rw [Nat.cast_sum]
      _ = ((balancedCut parent.lo (parent.hi - parent.lo) M j - parent.lo : ℕ) : ℝ) := congrArg (fun a : ℕ => (a : ℝ)) hsourceNat
      _ = _ := Nat.cast_sub hsourceOrder
  have hgap : (∑ i : Fin M, if i.val < j then
      stateLengthGap (substring source (sourceChild parent i).lo (sourceChild parent i).hi)
        target (comparison i) else 0) =
      (cut : ℝ) - r.lo - ((balancedCut parent.lo (parent.hi - parent.lo) M j : ℝ) - parent.lo) := by
    rw [← htargetReal, ← hsourceReal, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    by_cases hij : i.val < j <;> simp only [hij, ↓reduceIte, stateLengthGap, sub_zero]
  have horigin := (zero_connection_prefix_suffix r comparison 0 hzero).1
  simp only [List.take_zero, realConnectionBudget] at horigin
  have horiginEq : (connectionPrefixBoundary (List.ofFn comparison) r.hi 0 : ℝ) = r.lo := by
    exact (sub_eq_zero.mp (abs_eq_zero.mp horigin)).symm
  rw [hgap]
  unfold comparisonPrefixShift
  rw [balancedCut_zero, horiginEq]
  dsimp only [cut]
  ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_RationalPrefix
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
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









theorem computedBandActions_complete {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (tau theta velocity : ℚ)
    (child : Fin M → TargetInterval ny → ℚ) (states : Fin M → TargetInterval ny)
    (hnonempty : wideActionList M parent r b P ≠ [])
    (hstates : states ∈ wideActionList M parent r b P) (hvelocity : |velocity| ≤ 1 - tau)
    (hpredicate : bandActionPredicate parent r b tau theta velocity
      (wideActionList M parent r b P) hnonempty child states) :
    states ∈ computedBandActions parent r b P tau theta velocity child := by
  simp only [computedBandActions, dite_eq_right hnonempty, ite_eq_left hvelocity]
  exact List.mem_filter.mpr ⟨hstates, decide_eq_true hpredicate⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RepresentativeBands
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ComparisonBandCoverage
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Comparison action coverage by the computed predictor

Masses, gaps, prefix costs and curvature are those of the actual labeled
comparison action. The finite wide-action minimum supplies Z. No scalar
prefix prediction contract is assumed.
-/

namespace EditApproximation

open Finset

theorem comparisonPrefixShift_origin {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (comparison : Fin M → TargetInterval ny)
    (hzero : endpointActionConnection r comparison = 0) :
    comparisonPrefixShift parent r comparison 0 = (r.lo : ℝ) - parent.lo := by
  have h := (zero_connection_prefix_suffix r comparison 0 hzero).1
  simp only [List.take_zero, realConnectionBudget] at h
  have heq : (connectionPrefixBoundary (List.ofFn comparison) r.hi 0 : ℝ) = r.lo :=
    (sub_eq_zero.mp (abs_eq_zero.mp h)).symm
  simp only [comparisonPrefixShift, balancedCut_zero, heq]

/-- The actual comparison prefix prediction error is at most
`sqrt(W*K) + 2*(W-Z)`. All mass, gap and finite-minimum inequalities are
derived from the genuine child table lower invariant. -/
theorem comparisonPrefixPrediction_error {α : Type*} (source target : List α)
    {M b P : ℕ} (hM : 0 < M) (parent : TargetInterval source.length)
    (r : TargetInterval target.length) (comparison : Fin M → TargetInterval target.length)
    (hcomparison : comparison ∈ wideActionList M parent r b P)
    (hnonempty : wideActionList M parent r b P ≠ [])
    (child : Fin M → TargetInterval target.length → ℝ)
    (a : ℝ) (ha : 1 ≤ a)
    (hchild : ∀ i s, max ((stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s : ℝ) / a)
        |stateLengthGap (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s| ≤
          child i s)
    (hzero : endpointActionConnection r comparison = 0)
    (hZpos : 0 < wideActionMinimum parent r b P hnonempty child)
    (j : ℕ) (hj : j ≤ M) :
    |comparisonPrefixShift parent r comparison j - ((r.lo : ℝ) - parent.lo) -
      (stateLengthGap (substring source parent.lo parent.hi) target r /
        wideActionMinimum parent r b P hnonempty child) *
        widePrefixMinimum parent r (wideActionList M parent r b P) hnonempty child j
          (comparisonPrefixShift parent r comparison j)| ≤
      Real.sqrt (comparisonActionMass comparison child *
        comparisonActionCurvature source target parent r comparison child) +
        2 * (comparisonActionMass comparison child - wideActionMinimum parent r b P hnonempty child) := by
  let mass := fun i : Fin M => child i (comparison i)
  let gap := fun i : Fin M => stateLengthGap
    (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i)
  let W := comparisonActionMass comparison child
  let Z := wideActionMinimum parent r b P hnonempty child
  let parentGap := stateLengthGap (substring source parent.lo parent.hi) target r
  let K := comparisonActionCurvature source target parent r comparison child
  let prefixMass := comparisonPrefixValue comparison child j
  let point := comparisonPrefixShift parent r comparison j
  let origin := (r.lo : ℝ) - parent.lo
  let predictor := widePrefixMinimum parent r (wideActionList M parent r b P) hnonempty child j point
  have hgap (i : Fin M) : |gap i| ≤ mass i := (le_max_right _ _).trans (hchild i (comparison i))
  have hmass (i : Fin M) : 0 ≤ mass i := (abs_nonneg _).trans (hgap i)
  have hzeroMass (i : Fin M) (hi : mass i = 0) : gap i = 0 := by
    have h := hgap i
    rw [hi] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  have hsum : (∑ i, gap i) = parentGap := zero_connection_gap_sum source target hM parent r comparison hzero
  have hZW : Z ≤ W := by
    have h := wideActionMinimum_le_member parent r hnonempty child comparison hcomparison
    simpa only [Z, W, comparisonActionMass, endpointActionValue, hzero, Nat.cast_zero, zero_add] using h
  have hZ : 0 < Z := hZpos
  have hW : 0 < W := hZ.trans_le hZW
  have hG : 0 ≤ W - Z := sub_nonneg.mpr hZW
  have hparentGap : |parentGap| ≤ Z :=
    (le_max_right _ _).trans (wideActionMinimum_lower source target hM parent r b P hnonempty a ha child hchild)
  have hvelocity : |parentGap / Z| ≤ 1 := by
    rw [abs_div, abs_of_pos hZpos]
    exact (div_le_one hZpos).2 hparentGap
  have hprediction : |parentGap / W - parentGap / Z| * W ≤ W - Z := by
    have hid : (parentGap / W - parentGap / Z) * W = -(parentGap / Z) * (W - Z) := by
      field_simp [hW.ne', hZ.ne']
      ring
    calc
      _ = |(parentGap / W - parentGap / Z) * W| := by rw [abs_mul, abs_of_pos hW]
      _ = |parentGap / Z| * (W - Z) := by rw [hid, abs_mul, abs_neg, abs_of_nonneg hG]
      _ ≤ 1 * (W - Z) := mul_le_mul_of_nonneg_right hvelocity hG
      _ = _ := one_mul _
  have hprefix : 0 ≤ prefixMass := sum_nonneg (fun i _ => by
    dsimp only [mass] at hmass
    by_cases hi : i.val < j
    · simpa only [comparisonPrefixValue, hi, ite_eq_left] using hmass i
    · simp only [hi, ↓reduceIte, le_refl])
  have hprefixTotal : prefixMass ≤ W := by
    apply sum_le_sum
    intro i hi
    by_cases hij : i.val < j
    · simp only [hij, ↓reduceIte, le_refl]
    · simpa only [hij, ↓reduceIte] using hmass i
  have hcost := comparisonPrefixMinimum_actual_bounds parent r comparison hcomparison hnonempty child j hj hzero
  have hcurvature := curvature_l1_le_sqrt univ mass gap
    (fun i _ => hmass i) (fun i _ hi => hzeroMass i hi) hW
  rw [hsum] at hcurvature
  change (∑ i, |gap i - (parentGap / W) * mass i|) ≤ Real.sqrt (W * K) at hcurvature
  have hprefixGap := comparisonPrefixShift_gap_sum source target hM parent r comparison j hj hzero
  rw [comparisonPrefixShift_origin parent r comparison hzero] at hprefixGap
  have hdecomposition : point - origin - (parentGap / W) * prefixMass =
      ∑ i, if i.val < j then gap i - (parentGap / W) * mass i else 0 := by
    rw [hprefixGap]
    simp only [prefixMass, comparisonPrefixValue]
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    by_cases hij : i.val < j <;> simp only [hij, ↓reduceIte, mul_zero, sub_zero, mass, gap]
  have hdeviation : |point - origin - (parentGap / W) * prefixMass| ≤ Real.sqrt (W * K) := by
    rw [hdecomposition]
    apply (abs_sum_le_sum_abs _ _).trans
    apply (sum_le_sum (fun i _ => ?_)).trans hcurvature
    by_cases hij : i.val < j
    · simp only [hij, ↓reduceIte, le_refl]
    · simp only [hij, ↓reduceIte, abs_zero]
      exact abs_nonneg _
  exact comparison_prefix_prediction_error hprefix hprefixTotal hprediction hvelocity
    hcost.1 hcost.2 hdeviation

/-- The derived analytic estimate places the actual comparison action in
the literal rational finite filter once its explicit numerical budget holds. -/
theorem comparison_computedBandActions_mem {α : Type*} (source target : List α)
    {M b P : ℕ} (hM : 0 < M) (parent : TargetInterval source.length)
    (r : TargetInterval target.length) (comparison : Fin M → TargetInterval target.length)
    (hcomparison : comparison ∈ wideActionList M parent r b P)
    (hnonempty : wideActionList M parent r b P ≠ [])
    (tau theta : ℚ) (child : Fin M → TargetInterval target.length → ℚ)
    (a : ℝ) (ha : 1 ≤ a)
    (hchild : ∀ i s, max ((stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s : ℝ) / a)
        |stateLengthGap (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s| ≤
          (child i s : ℝ))
    (hzero : endpointActionConnection r comparison = 0)
    (hanchors : ∀ i, Nat.dist (r.lo + ((sourceChild parent i).lo - parent.lo)) (comparison i).lo ≤ 6 * b ∧
      Nat.dist (r.lo + ((sourceChild parent i).hi - parent.lo)) (comparison i).hi ≤ 6 * b)
    (hZpos : 0 < rationalWideActionMinimum parent r b P hnonempty child)
    (hvelocity : |rationalStateGap (substring source parent.lo parent.hi) target r /
      rationalWideActionMinimum parent r b P hnonempty child| ≤ 1 - tau)
    (hnumerical : Real.sqrt (comparisonActionMass comparison (fun i s => (child i s : ℝ)) *
        comparisonActionCurvature source target parent r comparison (fun i s => (child i s : ℝ))) +
        2 * (comparisonActionMass comparison (fun i s => (child i s : ℝ)) -
          wideActionMinimum parent r b P hnonempty (fun i s => (child i s : ℝ))) ≤
        (tau : ℝ) * theta * b / M) :
    comparison ∈ computedBandActions parent r b P tau theta
      (rationalStateGap (substring source parent.lo parent.hi) target r /
        rationalWideActionMinimum parent r b P hnonempty child) child := by
  apply computedBandActions_complete parent r b P tau theta _ child comparison hnonempty hcomparison hvelocity
  refine ⟨hzero, hanchors, ?_⟩
  intro j hj
  have hZreal : 0 < wideActionMinimum parent r b P hnonempty (fun i s => (child i s : ℝ)) := by
    rw [← rationalWideActionMinimum_cast]
    exact_mod_cast hZpos
  have herror := comparisonPrefixPrediction_error source target hM parent r comparison hcomparison hnonempty
    (fun i s => (child i s : ℝ)) a ha hchild hzero hZreal j.val (Nat.le_of_lt j.isLt)
  have hbound := herror.trans hnumerical
  have hpoint : ((bandCutShift parent comparison j : ℚ) : ℝ) =
      comparisonPrefixShift parent r comparison j.val := by
    rw [comparisonPrefixShift_at_child]
    simp only [bandCutShift, Rat.cast_sub, Rat.cast_natCast]
  apply (Rat.cast_le (K := ℝ)).mp
  simp only [Rat.cast_abs, Rat.cast_sub, Rat.cast_natCast, Rat.cast_div, Rat.cast_mul,
    rationalStateGap_cast, rationalWideActionMinimum_cast, rationalWidePrefixMinimum_cast]
  rw [hpoint]
  exact hbound

/-- The representative wrapper computes precisely the velocity used in
the preceding finite-filter membership result. -/
theorem comparison_representativeBandActions_mem {α : Type*} (source target : List α)
    {M b P : ℕ} (hM : 0 < M) (parent : TargetInterval source.length)
    (r : TargetInterval target.length) (comparison : Fin M → TargetInterval target.length)
    (hcomparison : comparison ∈ wideActionList M parent r b P)
    (hnonempty : wideActionList M parent r b P ≠ [])
    (tau theta : ℚ) (child : Fin M → TargetInterval target.length → ℚ)
    (a : ℝ) (ha : 1 ≤ a)
    (hchild : ∀ i s, max ((stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s : ℝ) / a)
        |stateLengthGap (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s| ≤
          (child i s : ℝ))
    (hzero : endpointActionConnection r comparison = 0)
    (hanchors : ∀ i, Nat.dist (r.lo + ((sourceChild parent i).lo - parent.lo)) (comparison i).lo ≤ 6 * b ∧
      Nat.dist (r.lo + ((sourceChild parent i).hi - parent.lo)) (comparison i).hi ≤ 6 * b)
    (hZpos : 0 < rationalWideActionMinimum parent r b P hnonempty child)
    (hvelocity : |rationalStateGap (substring source parent.lo parent.hi) target r /
      rationalWideActionMinimum parent r b P hnonempty child| ≤ 1 - tau)
    (hnumerical : Real.sqrt (comparisonActionMass comparison (fun i s => (child i s : ℝ)) *
        comparisonActionCurvature source target parent r comparison (fun i s => (child i s : ℝ))) +
        2 * (comparisonActionMass comparison (fun i s => (child i s : ℝ)) -
          wideActionMinimum parent r b P hnonempty (fun i s => (child i s : ℝ))) ≤
        (tau : ℝ) * theta * b / M) :
    comparison ∈ representativeBandActions source target parent r b P tau theta child := by
  simp only [representativeBandActions, dite_eq_right hnonempty, ite_eq_left hZpos]
  exact comparison_computedBandActions_mem source target hM parent r comparison hcomparison hnonempty
    tau theta child a ha hchild hzero hanchors hZpos hvelocity hnumerical

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedComparisonBand
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

theorem computed_comparison_band_mem_oai {α : Type*} (source target : List α)
    (N : ℕ) (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
    {M b P : ℕ} (hM : 0 < M) (hMeq : M = (integerParameters N).M)
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (comparison : Fin M → TargetInterval target.length)
    (hcomparison : comparison ∈ wideActionList M parent r b P)
    (hnonempty : wideActionList M parent r b P ≠ [])
    (child : Fin M → TargetInterval target.length → ℚ) (a : ℝ) (ha : 1 ≤ a)
    (hchild : ∀ i s, max ((stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s : ℝ) / a)
        |stateLengthGap (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s| ≤
          (child i s : ℝ))
    (hupper : ∀ i, (child i (comparison i) : ℝ) ≤ 2 * inputSmallLog N * stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i))
    (hcostSum : (∑ i, (stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i) : ℝ)) ≤ 4 * b)
    (hpositive : 0 < stateEditCost (substring source parent.lo parent.hi) target r)
    (hzero : endpointActionConnection r comparison = 0)
    (hanchors : ∀ i, Nat.dist (r.lo + ((sourceChild parent i).lo - parent.lo)) (comparison i).lo ≤ 6 * b ∧
      Nat.dist (r.lo + ((sourceChild parent i).hi - parent.lo)) (comparison i).hi ≤ 6 * b)
    (hvelocity : |rationalStateGap (substring source parent.lo parent.hi) target r /
      rationalWideActionMinimum parent r b P hnonempty child| ≤
        1 - (rationalParameters (inputSmallLog N)).tau)
    (hKsmall : comparisonActionCurvature source target parent r comparison (fun i s => (child i s : ℝ)) ≤
      b / heightQuarterRoot N)
    (hGsmall : comparisonActionMass comparison (fun i s => (child i s : ℝ)) -
      wideActionMinimum parent r b P hnonempty (fun i s => (child i s : ℝ)) ≤ b / heightQuarterRoot N) :
    comparison ∈ representativeBandActions source target parent r b P
      (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).theta child := by
  let childR := fun i s => (child i s : ℝ)
  let W := comparisonActionMass comparison childR
  let Z := wideActionMinimum parent r b P hnonempty childR
  let K := comparisonActionCurvature source target parent r comparison childR
  have hgap (i : Fin M) : |stateLengthGap
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i)| ≤
        childR i (comparison i) := (le_max_right _ _).trans (hchild i (comparison i))
  have hZlower : (stateEditCost (substring source parent.lo parent.hi) target r : ℝ) / a ≤ Z :=
    (le_max_left _ _).trans (wideActionMinimum_lower source target hM parent r b P hnonempty a ha childR hchild)
  have hcpos : (0 : ℝ) < stateEditCost (substring source parent.lo parent.hi) target r := by exact_mod_cast hpositive
  have hZpos : 0 < Z := (div_pos hcpos (by linarith only [ha] : 0 < a)).trans_le hZlower
  have hZposQ : 0 < rationalWideActionMinimum parent r b P hnonempty child := by
    have h := hZpos
    change 0 < wideActionMinimum parent r b P hnonempty childR at h
    rw [← rationalWideActionMinimum_cast] at h
    exact_mod_cast h
  have hZW : Z ≤ W := by
    have h := wideActionMinimum_le_member parent r hnonempty childR comparison hcomparison
    simpa only [Z, W, comparisonActionMass, endpointActionValue, hzero, Nat.cast_zero, zero_add] using h
  have hWpos : 0 < W := hZpos.trans_le hZW
  have hK : 0 ≤ K := comparisonActionCurvature_nonneg source target hM parent r comparison childR hgap hzero hWpos
  have hG : 0 ≤ W - Z := sub_nonneg.mpr hZW
  have hWupper : W ≤ 8 * inputSmallLog N * b := by
    calc
      W = ∑ i, childR i (comparison i) := rfl
      _ ≤ ∑ i, 2 * (inputSmallLog N : ℝ) * stateEditCost
          (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i) :=
        sum_le_sum fun i _ => hupper i
      _ = 2 * (inputSmallLog N : ℝ) * ∑ i, (stateEditCost
          (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i) : ℝ) := by rw [mul_sum]
      _ ≤ 2 * (inputSmallLog N : ℝ) * (4 * b) :=
        mul_le_mul_of_nonneg_left hcostSum (by positivity)
      _ = 8 * inputSmallLog N * b := by ring
  have hnumerical := computed_nonbad_band_numerical_bound N hN hell (Nat.cast_nonneg b)
    hK hG hWpos.le hKsmall hGsmall hWupper
  rw [← hMeq] at hnumerical
  apply comparison_representativeBandActions_mem source target hM parent r comparison hcomparison hnonempty
    (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).theta child
    a ha hchild hzero hanchors hZposQ hvelocity
  simpa only [mul_comm, W, Z, K, childR] using hnumerical

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.computed_comparison_band_mem_oai.{u_1} := @OAI.EditApproximation.computed_comparison_band_mem_oai.{u_1}
