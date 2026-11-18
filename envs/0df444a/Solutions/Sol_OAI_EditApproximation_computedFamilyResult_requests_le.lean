-- Prove2me | solution 1 for OAI.EditApproximation.computedFamilyResult_requests_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:42:13.48119+00:00
-- url     : https://prove2.me/submissions/7381bd82-9c3a-4f9d-bce1-416dd367b30f

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_EditApproxScheme_16
import Definitions.Def_OAIQ361V3Ea002
import Theorems.Thm_OAI_EditApproximation_computedFamilyMemoCode_fits
import Theorems.Thm_OAI_EditApproximation_computedFamilyTree_valid
import Theorems.Thm_OAI_EditApproximation_physicalFamilyMemo_requests_le_width

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BalancedWidths
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.physicalSubtreeNode_zero _root_.OAI.EditApproximation.treeLayerCodeWithWork_value
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

theorem treeLayer_card (M d : ℕ) : Fintype.card (TreeLayer M d) = M ^ d := by
  induction d with
  | zero =>
    change Fintype.card PUnit = 1
    exact Fintype.card_punit
  | succ d ih =>
    change Fintype.card (TreeLayer M d × Fin M) = M ^ (d + 1)
    rw [Fintype.card_prod, Fintype.card_fin, ih, pow_succ]

theorem complete_tree_node_count (M J : ℕ) (hM : 2 ≤ M) :
    (∑ d ∈ range (J + 1), Fintype.card (TreeLayer M d)) ≤ 2 * M ^ J := by
  simp_rw [treeLayer_card]
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ, pow_succ]
    have hmul := Nat.mul_le_mul_right (M ^ J) hM
    nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Work
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite dependency-path accounting

The double sum is the dependency-path budget in Section 10 of the
edit-distance manuscript, with separate branching bounds for same-index
and earlier-index requests.
-/

namespace EditApproximation

open Finset

/-- Explicit bound on the double sum, before substituting asymptotic
parameters. All quantities are natural numbers. -/
theorem dependencyPathBudget_le (depth indices same earlier : ℕ)
    (hsame : 1 ≤ same) (hearlier : 1 ≤ earlier) :
    dependencyPathBudget depth indices same earlier ≤
      (depth + 1) * (indices + 1) * 2 ^ (depth + indices) *
        same ^ depth * earlier ^ indices := by
  let bound := 2 ^ (depth + indices) * same ^ depth * earlier ^ indices
  have hterm (r s : ℕ) (hr : r ≤ depth) (hs : s ≤ indices) :
      (r + s).choose r * same ^ r * earlier ^ s ≤ bound := by
    have hchoose := (Nat.choose_le_two_pow (r + s) r).trans
      (pow_le_pow_right' (by omega : 1 ≤ (2 : ℕ)) (Nat.add_le_add hr hs))
    exact Nat.mul_le_mul (Nat.mul_le_mul hchoose (pow_le_pow_right' hsame hr))
      (pow_le_pow_right' hearlier hs)
  have hsum : dependencyPathBudget depth indices same earlier ≤
      ∑ _r ∈ range (depth + 1), ∑ _s ∈ range (indices + 1), bound := by
    apply sum_le_sum
    intro r hr
    apply sum_le_sum
    intro s hs
    exact hterm r s (by simpa using mem_range.mp hr) (by simpa using mem_range.mp hs)
  apply hsum.trans_eq
  simp only [sum_const, card_range, smul_eq_mul, bound]
  ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_DependencyExpansion
attribute [-instance] _root_.OAI.EditApproximation.physicalNodeFintype _root_.OAI.EditApproximation.physicalScalarIndexFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
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

theorem dependencyWordCount_succ (a b r s : ℕ) :
    dependencyWordCount a b (r + 1) (s + 1) =
      a * dependencyWordCount a b r (s + 1) + b * dependencyWordCount a b (r + 1) s := by
  unfold dependencyWordCount
  rw [show r + 1 + (s + 1) = (r + s + 1) + 1 by omega, Nat.choose_succ_succ']
  rw [show r + (s + 1) = r + s + 1 by omega, show r + 1 + s = r + s + 1 by omega]
  simp only [pow_succ]
  ring

theorem dependencyPathBudget_mono (d k D K a b : ℕ) (hd : d ≤ D) (hk : k ≤ K) :
    dependencyPathBudget d k a b ≤ dependencyPathBudget D K a b := by
  unfold dependencyPathBudget
  apply le_trans (sum_le_sum_of_subset (range_mono (Nat.add_le_add_right hd 1)))
  apply sum_le_sum
  intro r hr
  exact sum_le_sum_of_subset (range_mono (Nat.add_le_add_right hk 1))

theorem dependencyPathBudget_zero_zero (a b : ℕ) : dependencyPathBudget 0 0 a b = 1 := by
  simp [dependencyPathBudget]

theorem dependencyPathBudget_succ_zero (d a b : ℕ) :
    dependencyPathBudget (d + 1) 0 a b = 1 + a * dependencyPathBudget d 0 a b := by
  simp only [dependencyPathBudget, zero_add, sum_range_one, add_zero, Nat.choose_self,
    one_mul, pow_zero, mul_one]
  rw [sum_range_succ']
  simp only [pow_succ, pow_zero]
  rw [← sum_mul]
  ring

theorem dependencyPathBudget_zero_succ (k a b : ℕ) :
    dependencyPathBudget 0 (k + 1) a b = 1 + b * dependencyPathBudget 0 k a b := by
  simp only [dependencyPathBudget, zero_add, sum_range_one, Nat.choose_zero_right,
    pow_zero, one_mul]
  rw [sum_range_succ']
  simp only [pow_succ, pow_zero]
  rw [← sum_mul]
  ring

theorem dependencyPathBudget_succ_succ (d k a b : ℕ) :
    dependencyPathBudget (d + 1) (k + 1) a b =
      1 + a * dependencyPathBudget d (k + 1) a b +
        b * dependencyPathBudget (d + 1) k a b := by
  have hpascal (r s : ℕ) := dependencyWordCount_succ a b r s
  have hleft (r : ℕ) : dependencyWordCount a b (r + 1) 0 =
      a * dependencyWordCount a b r 0 := by
    simp [dependencyWordCount, pow_succ, Nat.mul_comm]
  have hright (s : ℕ) : dependencyWordCount a b 0 (s + 1) =
      b * dependencyWordCount a b 0 s := by
    simp [dependencyWordCount, pow_succ, Nat.mul_comm]
  have hzero : dependencyWordCount a b 0 0 = 1 := by simp [dependencyWordCount]
  have hsplit (r : ℕ) : (∑ s ∈ range (k + 2), dependencyWordCount a b r s) =
      dependencyWordCount a b r 0 + ∑ s ∈ range (k + 1), dependencyWordCount a b r (s + 1) := by
    rw [sum_range_succ']
    ring
  change (∑ r ∈ range (d + 2), ∑ s ∈ range (k + 2), dependencyWordCount a b r s) =
    1 + a * (∑ r ∈ range (d + 1), ∑ s ∈ range (k + 2), dependencyWordCount a b r s) +
      b * (∑ r ∈ range (d + 2), ∑ s ∈ range (k + 1), dependencyWordCount a b r s)
  rw [sum_range_succ' (fun r => ∑ s ∈ range (k + 2), dependencyWordCount a b r s) (d + 1),
    sum_range_succ' (fun r => ∑ s ∈ range (k + 1), dependencyWordCount a b r s) (d + 1)]
  simp_rw [hsplit]
  simp_rw [hpascal, sum_add_distrib, ← mul_sum]
  simp_rw [hleft, hright, hzero, ← mul_sum]
  ring

theorem dependencyPathBudget_recurrence (d k a b : ℕ) :
    dependencyPathBudget d k a b = 1 +
      (if d = 0 then 0 else a * dependencyPathBudget (d - 1) k a b) +
      (if k = 0 then 0 else b * dependencyPathBudget d (k - 1) a b) := by
  cases d with
  | zero =>
    cases k with
    | zero => simp [dependencyPathBudget_zero_zero]
    | succ k => simpa using dependencyPathBudget_zero_succ k a b
  | succ d =>
    cases k with
    | zero => simpa using dependencyPathBudget_succ_zero d a b
    | succ k => simpa using dependencyPathBudget_succ_succ d k a b

namespace DependencyExpansion

theorem nodeCountAtOrAbove_eq_zero (a b floor : ℕ) (tree : DependencyExpansion)
    (h : Valid a b tree) (hd : tree.depth < floor) :
    nodeCountAtOrAbove floor tree = 0 := by
  revert h hd
  induction tree with
  | node d k m n same earlier ihs ihe =>
    intro h hd
    obtain ⟨hm, hn, hs, he⟩ := h
    change d < floor at hd
    change (if floor ≤ d then 1 else 0) +
      (∑ i, nodeCountAtOrAbove floor (same i)) +
      (∑ i, nodeCountAtOrAbove floor (earlier i)) = 0
    have hsame : ∀ i, nodeCountAtOrAbove floor (same i) = 0 := by
      intro i
      exact ihs i (hs i).2.2 (lt_trans (hs i).1 hd)
    have hearlier : ∀ i, nodeCountAtOrAbove floor (earlier i) = 0 := by
      intro i
      exact ihe i (he i).2.2 (lt_of_le_of_lt (he i).1 hd)
    simp [Nat.not_le.mpr hd, hsame, hearlier]

/-- The path budget for a depth threshold uses only the available descent
above that threshold, independently of the total depth of the expansion. -/
theorem nodeCountAtOrAbove_le_budget (a b floor : ℕ) (tree : DependencyExpansion)
    (h : Valid a b tree) :
    nodeCountAtOrAbove floor tree ≤
      dependencyPathBudget (tree.depth - floor) tree.rank a b := by
  revert h
  induction tree generalizing floor with
  | node d k m n same earlier ihs ihe =>
    intro h
    by_cases hfloor : d < floor
    · have hzero := nodeCountAtOrAbove_eq_zero a b floor
        (.node d k m n same earlier) h hfloor
      rw [hzero]
      exact Nat.zero_le _
    obtain ⟨hm, hn, hs, he⟩ := h
    have hfd : floor ≤ d := Nat.le_of_not_gt hfloor
    have hsame : (∑ i, nodeCountAtOrAbove floor (same i)) ≤
        if d - floor = 0 then 0
        else a * dependencyPathBudget (d - floor - 1) k a b := by
      by_cases hd : d - floor = 0
      · have hzero : ∀ i, nodeCountAtOrAbove floor (same i) = 0 := by
          intro i
          apply nodeCountAtOrAbove_eq_zero a b floor (same i) (hs i).2.2
          have hp := (hs i).1
          omega
        simp [hd, hzero]
      · rw [ite_eq_right hd]
        calc
          (∑ i, nodeCountAtOrAbove floor (same i)) ≤
              ∑ _ : Fin m, dependencyPathBudget (d - floor - 1) k a b := by
            apply sum_le_sum
            intro i hi
            exact (ihs i floor (hs i).2.2).trans
              (dependencyPathBudget_mono _ _ _ _ a b
                (by have hp := (hs i).1; omega) (hs i).2.1)
          _ = m * dependencyPathBudget (d - floor - 1) k a b := by simp
          _ ≤ a * dependencyPathBudget (d - floor - 1) k a b :=
            Nat.mul_le_mul_right _ hm
    have hearlier : (∑ i, nodeCountAtOrAbove floor (earlier i)) ≤
        if k = 0 then 0 else b * dependencyPathBudget (d - floor) (k - 1) a b := by
      by_cases hk : k = 0
      · have hempty : n = 0 := by
          by_contra hn0
          have hbad := (he ⟨0, Nat.pos_of_ne_zero hn0⟩).2.1
          omega
        subst n
        simp [hk]
      · rw [ite_eq_right hk]
        calc
          (∑ i, nodeCountAtOrAbove floor (earlier i)) ≤
              ∑ _ : Fin n, dependencyPathBudget (d - floor) (k - 1) a b := by
            apply sum_le_sum
            intro i hi
            exact (ihe i floor (he i).2.2).trans
              (dependencyPathBudget_mono _ _ _ _ a b
                (Nat.sub_le_sub_right (he i).1 floor)
                (by have hp := (he i).2.1; omega))
          _ = n * dependencyPathBudget (d - floor) (k - 1) a b := by simp
          _ ≤ b * dependencyPathBudget (d - floor) (k - 1) a b :=
            Nat.mul_le_mul_right _ hn
    change (if floor ≤ d then 1 else 0) +
      (∑ i, nodeCountAtOrAbove floor (same i)) +
      (∑ i, nodeCountAtOrAbove floor (earlier i)) ≤ dependencyPathBudget (d - floor) k a b
    rw [ite_eq_left hfd, dependencyPathBudget_recurrence]
    exact Nat.add_le_add (Nat.add_le_add_left hsame 1) hearlier

theorem nodeCountAtDepth_le_atOrAbove (target : ℕ) (tree : DependencyExpansion) :
    nodeCountAtDepth target tree ≤ nodeCountAtOrAbove target tree := by
  induction tree with
  | node d k m n same earlier ihs ihe =>
    change (if d = target then 1 else 0) +
      (∑ i, nodeCountAtDepth target (same i)) +
      (∑ i, nodeCountAtDepth target (earlier i)) ≤
      (if target ≤ d then 1 else 0) +
      (∑ i, nodeCountAtOrAbove target (same i)) +
      (∑ i, nodeCountAtOrAbove target (earlier i))
    apply Nat.add_le_add
    · apply Nat.add_le_add
      · split_ifs <;> omega
      · exact sum_le_sum (fun i hi => ihs i)
    · exact sum_le_sum (fun i hi => ihe i)

theorem nodeCountThroughDescent_le_budget (a b j K : ℕ) (tree : DependencyExpansion)
    (h : Valid a b tree) (hk : tree.rank ≤ K) :
    nodeCountThroughDescent j tree ≤ dependencyPathBudget j K a b := by
  exact (nodeCountAtOrAbove_le_budget a b (tree.depth - j) tree h).trans
    (dependencyPathBudget_mono _ _ _ _ a b (by omega) hk)

theorem layerNodeCount_le_throughDescent (j : ℕ) (tree : DependencyExpansion) :
    layerNodeCount j tree ≤ nodeCountThroughDescent j tree := by
  unfold layerNodeCount nodeCountThroughDescent
  split_ifs
  · exact nodeCountAtDepth_le_atOrAbove _ tree
  · exact Nat.zero_le _

theorem layerNodeCount_le_budget (a b j K : ℕ) (tree : DependencyExpansion)
    (h : Valid a b tree) (hk : tree.rank ≤ K) :
    layerNodeCount j tree ≤ dependencyPathBudget j K a b :=
  (layerNodeCount_le_throughDescent j tree).trans
    (nodeCountThroughDescent_le_budget a b j K tree h hk)

theorem depthWeightedCount_eq_depth_sum (a b D : ℕ) (weight : ℕ → ℕ)
    (tree : DependencyExpansion) (h : Valid a b tree) (hd : tree.depth ≤ D) :
    (∑ t ∈ range (D + 1), nodeCountAtDepth t tree * weight t) =
      depthWeightedCount weight tree := by
  revert h hd
  induction tree with
  | node d k m n same earlier ihs ihe =>
    intro h hd
    obtain ⟨hm, hn, hs, he⟩ := h
    change d ≤ D at hd
    have hroot : (∑ t ∈ range (D + 1), (if d = t then 1 else 0) * weight t) = weight d := by
      simp [ite_mul, mem_range.mpr (Nat.lt_succ_of_le hd)]
    have hsame : (∑ t ∈ range (D + 1), (∑ i, nodeCountAtDepth t (same i)) * weight t) =
        ∑ i, depthWeightedCount weight (same i) := by
      simp_rw [sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro i hi
      exact ihs i (hs i).2.2 (le_trans (Nat.le_of_lt (hs i).1) hd)
    have hearlier : (∑ t ∈ range (D + 1), (∑ i, nodeCountAtDepth t (earlier i)) * weight t) =
        ∑ i, depthWeightedCount weight (earlier i) := by
      simp_rw [sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro i hi
      exact ihe i (he i).2.2 (le_trans (he i).1 hd)
    change (∑ t ∈ range (D + 1), ((if d = t then 1 else 0) +
      (∑ i, nodeCountAtDepth t (same i)) +
      (∑ i, nodeCountAtDepth t (earlier i))) * weight t) =
      weight d + (∑ i, depthWeightedCount weight (same i)) +
        ∑ i, depthWeightedCount weight (earlier i)
    simp_rw [add_mul, sum_add_distrib]
    rw [hroot, hsame, hearlier]

theorem depthWeightedCount_eq_layer_sum (a b : ℕ) (weight : ℕ → ℕ)
    (tree : DependencyExpansion) (h : Valid a b tree) :
    depthWeightedCount weight tree =
      ∑ j ∈ range (tree.depth + 1), layerNodeCount j tree * weight (tree.depth - j) := by
  symm
  calc
    (∑ j ∈ range (tree.depth + 1), layerNodeCount j tree * weight (tree.depth - j)) =
        ∑ j ∈ range (tree.depth + 1),
          nodeCountAtDepth (tree.depth - j) tree * weight (tree.depth - j) := by
      apply sum_congr rfl
      intro j hj
      rw [layerNodeCount, ite_eq_left (Nat.le_of_lt_succ (mem_range.mp hj))]
    _ = ∑ t ∈ range (tree.depth + 1), nodeCountAtDepth t tree * weight t := by
      simpa only [Nat.add_sub_cancel] using
        sum_range_reflect (fun t => nodeCountAtDepth t tree * weight t) (tree.depth + 1)
    _ = depthWeightedCount weight tree :=
      depthWeightedCount_eq_depth_sum a b tree.depth weight tree h le_rfl

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

end Builder

end DependencyExpansion
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Parameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
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
















theorem inputHeight_covers_length (N : ℕ) : N + 2 ≤ 2 ^ inputHeight N := by
  have hlog := Nat.le_pow_clog (by decide : 1 < 2) (N + 2)
  have hheight := Nat.le_pow_clog (by decide : 1 < 2) (Nat.clog 2 (N + 2))
  exact hlog.trans (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hheight)

theorem inputSmallLog_bounds (N : ℕ) (hN : 0 < N) :
    heightExponent N ≤ inputSmallLog N ∧ inputSmallLog N < 2 * heightExponent N := by
  have hpos := heightExponent_pos N hN
  have hone : 1 ≤ heightExponent N := hpos
  have hrange := rejectionWord_range (heightExponent N) hpos
  simpa only [inputSmallLog, smallLogExponent, rejectionBitCount, max_eq_right hone] using hrange

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_TreeParameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Depth of the computed interval tree

The branching factor is the power of two prescribed by the algorithm.
Ceiling logarithms count physical levels, including empty intervals.
-/

namespace EditApproximation

open Finset



theorem intervalTreeDepth_power_le (M nx : ℕ) (hM : 2 ≤ M) :
    M ^ intervalTreeDepth M nx ≤ M * max 1 nx := by
  by_cases hx : max 1 nx = 1
  · have hz : Nat.clog M 1 = 0 := by
      apply Nat.eq_zero_of_le_zero
      exact (Nat.clog_le_iff_le_pow hM).2 (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    simpa only [intervalTreeDepth, hx, hz, pow_zero, mul_one] using
      (by omega : 1 ≤ M)
  · have hx1 : 1 < max 1 nx := by omega
    have hdepth := Nat.clog_pos hM hx1
    have hpred := Nat.pow_pred_clog_lt_self hM hx1
    unfold intervalTreeDepth
    rw [← Nat.succ_pred_eq_of_pos hdepth,
      pow_succ]
    nlinarith

theorem computed_branching_bounds (N : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) :
    2 ≤ (integerParameters N).M ∧
      inputSmallLog N ≤ 50 * (heightExponent N / 20) ∧
      heightExponent N / 20 ≤ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hquot := Nat.mod_lt (heightExponent N) (by decide : 0 < 20)
  have hsplit := Nat.mod_add_div (heightExponent N) 20
  have hk : 1 ≤ heightExponent N / 20 := by omega
  have hpow : 2 ≤ 2 ^ (heightExponent N / 20) := by
    simpa using pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hk
  have hexp : heightExponent N ≤ inputHeight N := by
    exact (Nat.lt_pow_self (by decide : 1 < 2)).le
  exact ⟨hpow, by omega, (Nat.div_le_self _ _).trans hexp⟩

theorem computed_tree_depth_bound (N nx : ℕ) (hN : 0 < N) (hnx : nx ≤ N)
    (hell : 200 ≤ inputSmallLog N) :
    intervalTreeDepth (integerParameters N).M nx * inputSmallLog N ≤ 100 * inputHeight N := by
  let k := heightExponent N / 20
  have hbranch := computed_branching_bounds N hN hell
  have hbound : max 1 nx ≤ 2 ^ inputHeight N := by
    apply max_le Nat.one_le_two_pow
    exact hnx.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N))
  have hlog : Nat.clog 2 (max 1 nx) ≤ inputHeight N :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 hbound
  have hdepth : intervalTreeDepth (integerParameters N).M nx =
      (Nat.clog 2 (max 1 nx) + (k - 1)) / k := by
    exact Nat.clog_pow_left 2 k (max 1 nx)
  have hproduct := Nat.div_mul_le_self (Nat.clog 2 (max 1 nx) + (k - 1)) k
  rw [← hdepth] at hproduct
  have hscale := Nat.mul_le_mul_left
    (intervalTreeDepth (integerParameters N).M nx) hbranch.2.1
  change intervalTreeDepth (integerParameters N).M nx * inputSmallLog N ≤
    intervalTreeDepth (integerParameters N).M nx * (50 * k) at hscale
  have hkH : k ≤ inputHeight N := hbranch.2.2
  have hsub : k - 1 ≤ k := Nat.sub_le _ _
  nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SeedFactorSchedule
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The literal dyadic factor schedule stops at A<=F. Each active pass
replaces A by 4A/F and uses the integer factor a=A/F. -/

namespace EditApproximation





theorem computedSeed_initial_factor (N : ℕ) :
    (2 : ℚ) ^ computedSeedInitialExponent N =
      ((integerParameters N).initialFactor : ℚ) := by
  simp only [computedSeedInitialExponent, integerParameters, inputHeight, Nat.cast_pow, Nat.cast_ofNat]
  rw [← pow_mul, Nat.mul_comm]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterDependencyAsymptotics
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual pass/index count and the exponents in the dependency-path
bound. These statements concern computed numbers, independently of the
proof that an evaluator satisfies the dependency budgets. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem intervalTreeDepth_le_computedMax (N nx : ℕ) (hnx : nx ≤ N) :
    intervalTreeDepth (integerParameters N).M nx ≤ computedMaxTreeDepth N :=
  Nat.clog_mono_right _ (max_le_max le_rfl hnx)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_DependencyPathEnvelope
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit subpolynomial envelope for the finite dependency-path sum.
The connection between this sum and an execution is a separate obligation. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem nat_pow_eq_exp_log (a n : ℕ) (ha : 0 < a) :
    (a : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log a) := by
  rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast ha)]

theorem dependencyPathBudget_exp_bound (M ell H q C₁ C₂ j K : ℕ)
    (hM : 1 ≤ M) (hell : 1 ≤ ell) (hH : 1 ≤ H) :
    (dependencyPathBudget j K (M * ell ^ C₁) (H ^ (C₂ * q)) : ℝ) ≤
      (M : ℝ) ^ j * Real.exp ((1 + Real.log 2) * (j + K : ℝ) +
        C₁ * j * Real.log (ell : ℝ) + C₂ * q * K * Real.log (H : ℝ)) := by
  have hsame : 1 ≤ M * ell ^ C₁ := by
    have hp : 1 ≤ ell ^ C₁ := one_le_pow₀ hell
    nlinarith
  have hearlier : 1 ≤ H ^ (C₂ * q) := one_le_pow₀ hH
  have hnat := dependencyPathBudget_le j K (M * ell ^ C₁) (H ^ (C₂ * q)) hsame hearlier
  have hcast : (dependencyPathBudget j K (M * ell ^ C₁) (H ^ (C₂ * q)) : ℝ) ≤
      (j + 1 : ℝ) * (K + 1 : ℝ) * (2 : ℝ) ^ (j + K) *
        ((M : ℝ) * (ell : ℝ) ^ C₁) ^ j * ((H : ℝ) ^ (C₂ * q)) ^ K := by
    exact_mod_cast hnat
  have hj : (j + 1 : ℝ) ≤ Real.exp (j : ℝ) := Real.add_one_le_exp _
  have hK : (K + 1 : ℝ) ≤ Real.exp (K : ℝ) := Real.add_one_le_exp _
  have hproduct : (j + 1 : ℝ) * (K + 1 : ℝ) ≤ Real.exp (j : ℝ) * Real.exp (K : ℝ) :=
    mul_le_mul hj hK (by positivity) (Real.exp_nonneg _)
  calc
    _ ≤ (j + 1 : ℝ) * (K + 1 : ℝ) * (2 : ℝ) ^ (j + K) *
        ((M : ℝ) * (ell : ℝ) ^ C₁) ^ j * ((H : ℝ) ^ (C₂ * q)) ^ K := hcast
    _ ≤ (Real.exp (j : ℝ) * Real.exp (K : ℝ)) * (2 : ℝ) ^ (j + K) *
        ((M : ℝ) * (ell : ℝ) ^ C₁) ^ j * ((H : ℝ) ^ (C₂ * q)) ^ K := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hproduct (by positivity)
    _ = (M : ℝ) ^ j * Real.exp ((1 + Real.log 2) * (j + K : ℝ) +
        C₁ * j * Real.log (ell : ℝ) + C₂ * q * K * Real.log (H : ℝ)) := by
      have htwo : (2 : ℝ) ^ (j + K) = Real.exp (((j + K : ℕ) : ℝ) * Real.log 2) := by
        simpa only [Nat.cast_ofNat] using nat_pow_eq_exp_log 2 (j + K) (by decide)
      rw [mul_pow, ← pow_mul, ← pow_mul, htwo,
        nat_pow_eq_exp_log ell (C₁ * j) (by omega),
        nat_pow_eq_exp_log H (C₂ * q * K) (by omega)]
      calc
        _ = (M : ℝ) ^ j * (Real.exp (j : ℝ) * Real.exp (K : ℝ) *
            Real.exp (((j + K : ℕ) : ℝ) * Real.log 2) *
            Real.exp (((C₁ * j : ℕ) : ℝ) * Real.log ell) *
            Real.exp (((C₂ * q * K : ℕ) : ℝ) * Real.log H)) := by ring
        _ = (M : ℝ) ^ j * Real.exp ((j : ℝ) + K +
            ((j + K : ℕ) : ℝ) * Real.log 2 + ((C₁ * j : ℕ) : ℝ) * Real.log ell +
            ((C₂ * q * K : ℕ) : ℝ) * Real.log H) := by simp only [← Real.exp_add]
        _ = _ := by congr 2; push_cast <;> ring

theorem computed_dependency_path_envelope (N C₁ C₂ j : ℕ)
    (hj : j ≤ computedMaxTreeDepth N) :
    (dependencyPathBudget j (computedDependencyIndexCount N)
      ((integerParameters N).M * inputSmallLog N ^ C₁)
      (inputHeight N ^ (C₂ * (coarseExponent (inputSmallLog N) + 1))) : ℝ) ≤
      ((integerParameters N).M : ℝ) ^ j *
        Real.exp (computedDependencyOverheadExponent C₁ C₂ N) := by
  have hM : 1 ≤ (integerParameters N).M := Nat.one_le_two_pow
  have hell : 1 ≤ inputSmallLog N := Nat.one_le_two_pow
  have hH : 1 ≤ inputHeight N := Nat.one_le_two_pow
  have h := dependencyPathBudget_exp_bound (integerParameters N).M (inputSmallLog N)
    (inputHeight N) (coarseExponent (inputSmallLog N) + 1) C₁ C₂ j
    (computedDependencyIndexCount N) hM hell hH
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  unfold computedDependencyOverheadExponent
  have hjR : (j : ℝ) ≤ computedMaxTreeDepth N := by exact_mod_cast hj
  have hlog : 0 ≤ Real.log (inputSmallLog N : ℝ) := Real.log_nonneg (by exact_mod_cast hell)
  have hlogtwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hjR (mul_nonneg (Nat.cast_nonneg C₁) hlog)]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_WeightedTreeWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Summing width-sensitive work over physical levels

At depth `d`, the product of the number of nodes and their maximum
balanced width is at most the source length plus one layer's node count.
This is the precise summation used for fresh coarse-entry requests.
-/

namespace EditApproximation

open Finset

theorem mul_ceilDiv_le_add (n m : ℕ) (hm : 0 < m) :
    m * (n ⌈/⌉ m) ≤ n + m := by
  have hceil : n ⌈/⌉ m ≤ n / m + 1 :=
    (ceilDiv_le_iff_le_mul hm).2 (Nat.lt_mul_div_succ n hm).le
  have hmul := Nat.mul_le_mul_left m hceil
  have hfloor := Nat.mul_div_le n m
  nlinarith

theorem layer_width_work (M n d : ℕ) (hM : 0 < M) :
    M ^ d * (1 + n ⌈/⌉ M ^ d) ≤ n + 2 * M ^ d := by
  have hwidth := mul_ceilDiv_le_add n (M ^ d) (pow_pos hM d)
  nlinarith

theorem interval_tree_width_work (M n : ℕ) (hM : 2 ≤ M) :
    (∑ d ∈ range (intervalTreeDepth M n + 1), M ^ d * (1 + n ⌈/⌉ M ^ d)) ≤
      (intervalTreeDepth M n + 1) * n + 4 * M * max 1 n := by
  have hpoint (d : ℕ) (_ : d ∈ range (intervalTreeDepth M n + 1)) :=
    layer_width_work M n d (by omega)
  have hsum := sum_le_sum hpoint
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum] at hsum
  have hnodes := complete_tree_node_count M (intervalTreeDepth M n) hM
  simp_rw [treeLayer_card] at hnodes
  have hcapacity := intervalTreeDepth_power_le M n hM
  nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_DependencyWeightedWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Width-sensitive work summed over an actual finite dependency expansion.
The bound uses its per-layer counts, including earlier edges that descend. -/

namespace EditApproximation

open Finset Filter

namespace DependencyExpansion

theorem widthWork_le (M n a b K : ℕ) (hM : 2 ≤ M)
    (tree : DependencyExpansion) (hvalid : tree.Valid a b)
    (hdepth : tree.depth = intervalTreeDepth M n) (hrank : tree.rank ≤ K)
    (overhead : ℝ) (hoverhead : 0 ≤ overhead)
    (hpath : ∀ j ≤ intervalTreeDepth M n,
      (dependencyPathBudget j K a b : ℝ) ≤ (M : ℝ) ^ j * overhead) :
    (tree.widthWork M n : ℝ) ≤
      (((intervalTreeDepth M n + 1) * n + 4 * M * max 1 n : ℕ) : ℝ) * overhead := by
  have hpartition : tree.widthWork M n =
      ∑ j ∈ range (intervalTreeDepth M n + 1),
        tree.layerNodeCount j * (1 + n ⌈/⌉ M ^ j) := by
    unfold widthWork
    rw [depthWeightedCount_eq_layer_sum a b _ tree hvalid]
    rw [hdepth]
    apply sum_congr rfl
    intro j hj
    have hsub : intervalTreeDepth M n - (intervalTreeDepth M n - j) = j := by
      have := mem_range.mp hj
      omega
    rw [hsub]
  rw [hpartition]
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ ∑ j ∈ range (intervalTreeDepth M n + 1),
        ((M : ℝ) ^ j * overhead) * (1 + (n ⌈/⌉ M ^ j : ℕ)) := by
      apply sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (show (tree.layerNodeCount j : ℝ) ≤ dependencyPathBudget j K a b by
        exact_mod_cast layerNodeCount_le_budget a b j K tree hvalid hrank).trans
        (hpath j (Nat.le_of_lt_succ (mem_range.mp hj)))
    _ = (∑ j ∈ range (intervalTreeDepth M n + 1),
        (M : ℝ) ^ j * (1 + (n ⌈/⌉ M ^ j : ℕ))) * overhead := by
      rw [sum_mul]
      apply sum_congr rfl
      intro j _
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hoverhead
      exact_mod_cast interval_tree_width_work M n hM

end DependencyExpansion

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

theorem queryDependencyExpansion_depth (root : κ) :
    (queryDependencyExpansion depth index program progress root).depth = depth root :=
  DependencyExpansion.build_depth _ _ _ _ _ _ _ _ root

theorem queryDependencyExpansion_index (root : κ) :
    (queryDependencyExpansion depth index program progress root).rank = index root :=
  DependencyExpansion.build_rank _ _ _ _ _ _ _ _ root

end Queries

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalInputEncoding
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Fixed-width binary keys for gathered child states. The encoding uses
mixed radix arithmetic on the child label and the two state endpoints. -/

namespace EditApproximation

theorem childInputCode_bound {M n : ℕ} (input : Fin M × TargetInterval n) :
    childInputCode input < M * (n + 1) ^ 2 := by
  have hlow := input.2.ordered.trans input.2.valid
  have hhigh := input.2.valid
  have hlabel := input.1.isLt
  have hM : 0 < M := by omega
  have hinner : input.2.lo + (n + 1) * input.2.hi < (n + 1) ^ 2 := by
    nlinarith only [hlow, hhigh]
  unfold childInputCode
  nlinarith only [hlabel, Nat.mul_le_mul_left M (Nat.succ_le_of_lt hinner)]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalNodeEncoding
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Computable base-M node labels and mixed-radix table-entry keys.
Equal source intervals at different physical nodes keep distinct keys. -/

namespace EditApproximation



theorem treeLayerCode_bound (M d : ℕ) (path : TreeLayer M d) :
    treeLayerCode M d path < M ^ d := by
  induction d with
  | zero => exact Nat.zero_lt_one
  | succ d ih =>
    have hp := ih path.1
    have hi := path.2.isLt
    change path.2.val + M * treeLayerCode M d path.1 < M ^ (d + 1)
    rw [pow_succ]
    nlinarith only [hi, Nat.mul_le_mul_left M (Nat.succ_le_of_lt hp)]

theorem treeLayerCode_injective (M d : ℕ) : Function.Injective (treeLayerCode M d) := by
  induction d with
  | zero => intro first second _; cases first; cases second; rfl
  | succ d ih =>
    rintro ⟨first, i⟩ ⟨second, j⟩ heq
    obtain ⟨hlabel, hpath⟩ := mixedRadix_injective i.isLt j.isLt heq
    exact Prod.ext (ih hpath) (Fin.ext hlabel)



theorem physicalNode_layer_bound {M J : ℕ} (hM : 1 ≤ M) (node : PhysicalNode M J) :
    treeLayerCode M node.1.val node.2 < M ^ J :=
  (treeLayerCode_bound M node.1.val node.2).trans_le
    (pow_le_pow_right₀ hM (Nat.le_of_lt_succ node.1.isLt))

theorem physicalNodeCode_injective {M J : ℕ} (hM : 1 ≤ M) :
    Function.Injective (@physicalNodeCode M J) := by
  rintro ⟨depth, path⟩ ⟨depth', path'⟩ heq
  obtain ⟨hp, hd⟩ := mixedRadix_injective
    (physicalNode_layer_bound hM ⟨depth, path⟩)
    (physicalNode_layer_bound hM ⟨depth', path'⟩) heq
  have hdepth : depth = depth' := Fin.ext hd
  subst depth'
  have hpath := treeLayerCode_injective M depth.val hp
  change path = path' at hpath
  subst path'
  rfl

theorem physicalNodeCode_bound {M J : ℕ} (hM : 1 ≤ M) (node : PhysicalNode M J) :
    physicalNodeCode node < M ^ J * (J + 1) := by
  have hpath := physicalNode_layer_bound hM node
  have hdepth := node.1.isLt
  unfold physicalNodeCode
  nlinarith only [hpath, Nat.mul_le_mul_left (M ^ J) (Nat.succ_le_of_lt hdepth)]



theorem physicalEntryCode_injective {M J n : ℕ} (hM : 1 ≤ M) :
    Function.Injective (@physicalEntryCode M J n) := by
  rintro ⟨node, q⟩ ⟨node', q'⟩ heq
  obtain ⟨hq, hn⟩ := mixedRadix_injective
    (by simpa only [Nat.one_mul] using childInputCode_bound ((0 : Fin 1), q))
    (by simpa only [Nat.one_mul] using childInputCode_bound ((0 : Fin 1), q')) heq
  have hstate := childInputCode_injective 1 n hq
  have hqeq : q = q' := congrArg (fun pair : Fin 1 × TargetInterval n => pair.2) hstate
  exact Prod.ext (physicalNodeCode_injective hM hn) hqeq

theorem physicalEntryCode_bound {M J n : ℕ} (hM : 1 ≤ M) (state : PhysicalEntry M J n) :
    physicalEntryCode state < (n + 1) ^ 2 * (M ^ J * (J + 1)) := by
  have hstate : childInputCode ((0 : Fin 1), state.2) < (n + 1) ^ 2 := by
    simpa only [Nat.one_mul] using childInputCode_bound ((0 : Fin 1), state.2)
  have hnode := physicalNodeCode_bound hM state.1
  unfold physicalEntryCode
  nlinarith only [hstate, Nat.mul_le_mul_left ((n + 1) ^ 2) (Nat.succ_le_of_lt hnode)]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRequestEncoding
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Fixed-width keys for the bounded physical cache. Their construction
uses only the request's coordinates, without enumerating table entries. -/

namespace EditApproximation
namespace PhysicalTableRequest





theorem code_injective {M J n : ℕ} (hM : 1 ≤ M) (passes copies T S : ℕ) :
    Function.Injective (fun request : {r : PhysicalTableRequest M J n // Bounded passes copies T S r} =>
      code copies T S request.val) := by
  intro first second heq
  obtain ⟨hindex, hrest⟩ := mixedRadix_injective
    (Nat.lt_succ_of_le first.2.2.2) (Nat.lt_succ_of_le second.2.2.2) heq
  obtain ⟨hcopy, hrest⟩ := mixedRadix_injective first.2.2.1 second.2.2.1 hrest
  obtain ⟨hentry, hpass⟩ := mixedRadix_injective
    (physicalEntryCode_bound hM (first.1.node, first.1.state))
    (physicalEntryCode_bound hM (second.1.node, second.1.state)) hrest
  have he := physicalEntryCode_injective hM hentry
  have hnode := congrArg Prod.fst he
  have hstate := congrArg Prod.snd he
  apply Subtype.ext
  cases first with
  | mk first hf =>
    cases second with
    | mk second hs =>
      cases first
      cases second
      simp only at hpass hcopy hnode hindex hstate
      cases hpass
      cases hcopy
      cases hnode
      cases hindex
      cases hstate
      rfl

end PhysicalTableRequest
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedPhysicalRequest
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Coarse seed computations are explicit cache requests, alongside the
bounded warmup/refinement requests. Their rank is below every table request,
so first exposure of a same-node coarse entry is a genuine leaf of the lazy program. -/

namespace EditApproximation



namespace ChargedPhysicalRequest









 theorem code_injective {M J ny passes copies T S : ℕ} (hM : 1 ≤ M) :
    Function.Injective (@code M J ny passes copies T S) := by
  intro left right heq
  cases left with
  | inl left =>
    cases right with
    | inl right =>
      have hentry : physicalEntryCode left = physicalEntryCode right := by
        change 2 * physicalEntryCode left = 2 * physicalEntryCode right at heq
        omega
      exact congrArg Sum.inl (physicalEntryCode_injective hM hentry)
    | inr right =>
      change 2 * physicalEntryCode left = 2 * PhysicalTableRequest.code copies T S right.val + 1 at heq
      omega
  | inr left =>
    cases right with
    | inl right =>
      change 2 * PhysicalTableRequest.code copies T S left.val + 1 = 2 * physicalEntryCode right at heq
      omega
    | inr right =>
      have htable : PhysicalTableRequest.code copies T S left.val =
          PhysicalTableRequest.code copies T S right.val := by
        change 2 * PhysicalTableRequest.code copies T S left.val + 1 =
          2 * PhysicalTableRequest.code copies T S right.val + 1 at heq
        omega
      exact congrArg Sum.inr (PhysicalTableRequest.code_injective hM passes copies T S htable)

end ChargedPhysicalRequest

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedEarlierInputBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual earlier-input cover satisfies the polynomial branching
budget at every seed, after substituting the computed time and grid
parameters. -/

namespace EditApproximation

theorem computed_smallLog_le_height (N : ℕ) : inputSmallLog N ≤ inputHeight N := by
  have hf : smallLogExponent N ≤ heightExponent N := by
    unfold smallLogExponent
    apply Nat.clog_le_of_le_pow
    exact max_le Nat.one_le_two_pow (heightExponent N).lt_two_pow_self.le
  exact pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) hf

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedDependencyExpansion
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dependency expansion is built from the charged evaluator's
executed requests. Its branching bounds therefore apply to actual lazy
evaluation, with coarse leaves at their original physical depths. -/

namespace EditApproximation

theorem chargedRequest_index_le {M J ny passes copies T S : ℕ}
    (request : ChargedPhysicalRequest M J ny passes copies T S) :
    request.index ≤ passes * (T + S + 1) := by
  cases request with
  | inl entry => exact Nat.zero_le _
  | inr parent =>
    have hp : parent.val.pass + 1 ≤ passes := parent.property.1
    have hi : parent.val.index + 1 ≤ T + S + 1 := Nat.add_le_add_right parent.property.2.2 1
    change parent.val.pass * (T + S + 1) + parent.val.index + 1 ≤ _
    calc
      _ ≤ (parent.val.pass + 1) * (T + S + 1) := by rw [Nat.add_mul, Nat.one_mul]; omega
      _ ≤ _ := Nat.mul_le_mul_right _ hp

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedQueryAsymptotics
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Almost-linear bounds for the executed request tree. These count
requests and depth-weighted source widths, independently of accuracy events.
Local arithmetic and random-source costs are separate obligations. -/

namespace EditApproximation

open Filter
open scoped Topology

/-- The deterministic balanced-tree prefactor is only `N` times a fixed
polynomial in the logarithmic height. -/
theorem computed_width_prefactor_le (N n : ℕ) (hN : 0 < N) (hn : n ≤ N)
    (hell : 200 ≤ inputSmallLog N) (hH : 105 ≤ inputHeight N) :
    (intervalTreeDepth (integerParameters N).M n + 1) * n +
      4 * (integerParameters N).M * max 1 n ≤ (N + 2) * inputHeight N ^ 2 := by
  have hdepth := computed_tree_depth_bound N n hN hn hell
  have hellone : 1 ≤ inputSmallLog N := by omega
  have hJ : intervalTreeDepth (integerParameters N).M n ≤ 100 * inputHeight N := by
    have hm := Nat.mul_le_mul_left (intervalTreeDepth (integerParameters N).M n) hellone
    omega
  have hM : (integerParameters N).M ≤ inputHeight N := by
    change 2 ^ (heightExponent N / 20) ≤ 2 ^ heightExponent N
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.div_le_self _ _)
  have hx : max 1 n ≤ N + 2 := max_le (by omega) (by omega)
  calc
    _ ≤ (100 * inputHeight N + 1) * (N + 2) +
        4 * inputHeight N * (N + 2) := by gcongr; omega
    _ ≤ 105 * inputHeight N * (N + 2) := by nlinarith
    _ ≤ (N + 2) * inputHeight N ^ 2 := by
      have hsquare : 105 * inputHeight N ≤ inputHeight N ^ 2 := by nlinarith
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_right (N + 2) hsquare

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SourceRankedEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! An explicit parity tag separates source coordinates and table keys.
The code is computed from coordinates without enumerating the key type. -/

namespace EditApproximation.SourceRanked

variable {σ κ : Type*}



 theorem keyCode_injective (sourceCode : σ → ℕ) (tableCode : κ → ℕ)
    (hs : Function.Injective sourceCode) (ht : Function.Injective tableCode) :
    Function.Injective (keyCode sourceCode tableCode) := by
  intro left right h
  cases left with
  | inl left =>
    cases right with
    | inl right =>
      have heq : sourceCode left = sourceCode right := by
        change 2 * sourceCode left = 2 * sourceCode right at h
        omega
      exact congrArg Sum.inl (hs heq)
    | inr right =>
      change 2 * sourceCode left = 2 * tableCode right + 1 at h
      omega
  | inr left =>
    cases right with
    | inl right =>
      change 2 * tableCode left + 1 = 2 * sourceCode right at h
      omega
    | inr right =>
      have heq : tableCode left = tableCode right := by
        change 2 * tableCode left + 1 = 2 * tableCode right + 1 at h
        omega
      exact congrArg Sum.inr (ht heq)

end EditApproximation.SourceRanked

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalScalarEncoding
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Scalar-source addresses are computed from physical coordinates by
integer pairing. No enumeration of the probability space is performed. -/

namespace EditApproximation

variable {M J N n exponent F Q R B : ℕ}



 theorem physicalScalarCode_injective (hM : 1 ≤ M) :
    Function.Injective (@physicalScalarCode M J N n exponent F Q R B) := by
  intro left right heq
  rcases left with ⟨left, li⟩
  rcases right with ⟨right, ri⟩
  cases left with
  | inl left =>
    cases right with
    | inl right =>
      have hp : Nat.pair (physicalEntryCode (left.1.1.val, left.1.2.2))
          (Nat.pair left.1.2.1.val (Nat.pair left.2.val.val li.val)) =
          Nat.pair (physicalEntryCode (right.1.1.val, right.1.2.2))
          (Nat.pair right.1.2.1.val (Nat.pair right.2.val.val ri.val)) := by
        change 2 * _ = 2 * _ at heq
        omega
      rcases Nat.pair_eq_pair.mp hp with ⟨he, hs⟩
      rcases Nat.pair_eq_pair.mp hs with ⟨hs, hr⟩
      rcases Nat.pair_eq_pair.mp hr with ⟨hr, ht⟩
      have he := physicalEntryCode_injective hM he
      have hn : left.1.1 = right.1.1 := Subtype.ext (congrArg Prod.fst he)
      have hq := congrArg Prod.snd he
      have hs : left.1.2.1 = right.1.2.1 := Fin.ext hs
      have hr : left.2 = right.2 := Subtype.ext (Fin.ext hr)
      have ht : li = ri := Fin.ext ht
      rcases left with ⟨⟨node, scale, q⟩, range⟩
      rcases right with ⟨⟨node', scale', q'⟩, range'⟩
      dsimp only at hn hq hs hr
      subst node'
      subst scale'
      subst q'
      subst range'
      cases ht
      rfl
    | inr right =>
      change 2 * _ = 2 * _ + 1 at heq
      omega
  | inr left =>
    cases right with
    | inl right =>
      change 2 * _ + 1 = 2 * _ at heq
      omega
    | inr right =>
      have hp : Nat.pair (physicalNodeCode left.1.val)
          (Nat.pair left.2.1.val (Nat.pair left.2.2.1.val (Nat.pair left.2.2.2.val
            (Nat.pair li.1.val (Nat.pair li.2.1.val li.2.2.val))))) =
          Nat.pair (physicalNodeCode right.1.val)
          (Nat.pair right.2.1.val (Nat.pair right.2.2.1.val (Nat.pair right.2.2.2.val
            (Nat.pair ri.1.val (Nat.pair ri.2.1.val ri.2.2.val))))) := by
        change 2 * _ + 1 = 2 * _ + 1 at heq
        omega
      rcases Nat.pair_eq_pair.mp hp with ⟨hn, hp⟩
      rcases Nat.pair_eq_pair.mp hp with ⟨hs, hp⟩
      rcases Nat.pair_eq_pair.mp hp with ⟨hx, hp⟩
      rcases Nat.pair_eq_pair.mp hp with ⟨hy, hp⟩
      rcases Nat.pair_eq_pair.mp hp with ⟨ht, hp⟩
      rcases Nat.pair_eq_pair.mp hp with ⟨hl, hv⟩
      have hn : left.1 = right.1 := Subtype.ext (physicalNodeCode_injective hM hn)
      have hs : left.2.1 = right.2.1 := Fin.ext hs
      have hx : left.2.2.1 = right.2.2.1 := Fin.ext hx
      have hy : left.2.2.2 = right.2.2.2 := Fin.ext hy
      rcases left with ⟨node, scale, x, y⟩
      rcases right with ⟨node', scale', x', y'⟩
      dsimp only at hn hs hx hy
      subst node'
      subst scale'
      subst x'
      subst y'
      rcases li with ⟨time, label, value⟩
      rcases ri with ⟨time', label', value'⟩
      have ht : time = time' := Fin.ext ht
      cases ht
      have hl : label = label' := Fin.ext hl
      cases hl
      have hv : value = value' := Fin.ext hv
      cases hv
      rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyEncoding
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

section Encoding

variable {α : Type*} {M J R : ℕ} (target : List α) (N P F exponent H Q passes copies : ℕ)



 theorem physicalFamilyCode_injective (hM : 1 ≤ M) :
    Function.Injective (physicalFamilyCode (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies) := by
  intro first second h
  obtain ⟨hp, h⟩ := Nat.pair_eq_pair.mp h
  obtain ⟨hc, hs⟩ := Nat.pair_eq_pair.mp h
  exact Prod.ext (Fin.ext hp) (Prod.ext (Fin.ext hc) (physicalScalarCode_injective hM hs))

end Encoding

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedFamilyMemoCode
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation







 theorem computedFamilyMemoCode_injective (source target : List ℕ) (N R : ℕ)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) :
    Function.Injective (computedFamilyMemoCode source target N R) := by
  have hM : 1 ≤ (integerParameters N).M := (by omega : 1 ≤ 2).trans
    (computed_branching_bounds N hN hell).1
  exact SourceRanked.keyCode_injective _ _
    (physicalFamilyCode_injective target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
      (computedSeedPassCount N) (inputHeight N ^ 2) hM)
    (ChargedPhysicalRequest.code_injective hM)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedPhysicalUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

theorem two_hundred_le_two_pow_thousand : 200 ≤ (2 : ℕ) ^ 1000 := by
  have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by decide : 8 ≤ 1000)
  exact le_trans (by decide : 200 ≤ (2 : ℕ) ^ 8) h

open MeasureTheory ProbabilityTheory

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedWidthEnvelope
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A parameter-only majorant for every executed dependency tree. It is
independent of the accepted random values and of all accuracy events. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem computed_widthWork_le_envelope (N n : ℕ) (hN : 0 < N) (hn : n ≤ N)
    (hell : 200 ≤ inputSmallLog N) (hH : 105 ≤ inputHeight N)
    (tree : DependencyExpansion)
    (hv : tree.Valid ((integerParameters N).M * inputSmallLog N ^ 257)
      (inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1))))
    (hd : tree.depth = intervalTreeDepth (integerParameters N).M n)
    (hk : tree.rank ≤ computedDependencyIndexCount N) :
    (tree.widthWork (integerParameters N).M n : ℝ) ≤ computedWidthEnvelope N := by
  have hw := DependencyExpansion.widthWork_le (integerParameters N).M n _ _ _
    (computed_branching_bounds N hN hell).1 tree hv hd hk
    (Real.exp (computedDependencyOverheadExponent 257 512 N)) (Real.exp_nonneg _) (by
      intro j hj
      exact computed_dependency_path_envelope N 257 512 j
        (hj.trans (intervalTreeDepth_le_computedMax N n hn)))
  have hpref := computed_width_prefactor_le N n hN hn hell hH
  have hprefR : (((intervalTreeDepth (integerParameters N).M n + 1) * n +
      4 * (integerParameters N).M * max 1 n : ℕ) : ℝ) ≤
      (N + 2 : ℝ) * (inputHeight N : ℝ) ^ 2 := by exact_mod_cast hpref
  exact hw.trans (mul_le_mul_of_nonneg_right hprefR (Real.exp_nonneg _))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
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

 theorem physicalFamilyDependencyTree_depth
    (root : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) :
    (physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta initial hPpos draw root).depth = root.depth := by
  exact queryDependencyExpansion_depth _ _ _
    (chargedRandomRequestList_progress source target N P H T S (passes + 1) copies factor multiplier
      tau eta kappa delta group integer initial readGroup readInteger answer bodyValue) root

 theorem physicalFamilyDependencyTree_rank
    (hpasses : passes = computedSeedPassCount N) (hT : T = (integerParameters N).T)
    (hS : S = (integerParameters N).S)
    (root : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) :
    (physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta initial hPpos draw root).rank ≤ computedDependencyIndexCount N := by
  have heq : (physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta initial hPpos draw root).rank = root.index :=
    queryDependencyExpansion_index _ _ _
      (chargedRandomRequestList_progress source target N P H T S (passes + 1) copies factor multiplier
        tau eta kappa delta group integer initial readGroup readInteger answer bodyValue) root
  rw [heq]
  apply (chargedRequest_index_le root).trans_eq
  simp only [computedDependencyIndexCount, hpasses, hT, hS]

end Work

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedPhysicalWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

open Filter MeasureTheory

 theorem scheduledSeedFactor_bounds (N pass : ℕ) :
    1 ≤ scheduledSeedFactor N pass ∧
      scheduledSeedFactor N pass ≤ ((integerParameters N).initialFactor : ℚ) := by
  constructor
  · exact one_le_pow₀ (by norm_num)
  · rw [← computedSeed_initial_factor]
    exact pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (Nat.sub_le _ _)









 theorem computedFamilyTree_depth (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N) :
    (computedFamilyTree source target N input).depth =
      intervalTreeDepth (integerParameters N).M source.length := by
  unfold computedFamilyTree
  rw [physicalFamilyDependencyTree_depth]
  rfl

 theorem computedFamilyTree_rank (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N) :
    (computedFamilyTree source target N input).rank ≤ computedDependencyIndexCount N := by
  unfold computedFamilyTree
  exact physicalFamilyDependencyTree_rank source target N (integerParameters N).P (inputHeight N)
    (integerParameters N).T (integerParameters N).S (computedSeedPassCount N) (inputHeight N ^ 2)
    (scheduledSeedFactor N) (scheduledSeedMultiplier N) _ _ _ _
    (clampedSeedNat input.1) (computedParameterP_pos N) input.2 rfl rfl rfl _

 theorem computedFamilyTree_width_le (source target : List ℕ) (N : ℕ)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) (hH : 105 ≤ inputHeight N)
    (hsize : source.length + target.length ≤ N) (input : ComputedFamilyInput source target N) :
    ((computedFamilyTree source target N input).widthWork (integerParameters N).M source.length : ℝ) ≤
      computedWidthEnvelope N :=
  computed_widthWork_le_envelope N source.length hN (by omega) hell hH _
    (computedFamilyTree_valid source target N hN hell input)
    (computedFamilyTree_depth source target N input) (computedFamilyTree_rank source target N input)

 theorem computedFamilyResult_requests_le_oai (source target : List ℕ) (N : ℕ)
    (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N) (hsize : source.length + target.length ≤ N)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N) (input : ComputedFamilyInput source target N) :
    ((computedFamilyResult source target N input).requests : ℝ) ≤
      ((inputHeight N : ℝ) ^ 91 + 1) * computedWidthEnvelope N := by
  have hsmall : 200 ≤ inputSmallLog N := two_hundred_le_two_pow_thousand.trans hell
  have hH : 105 ≤ inputHeight N := (by omega : 105 ≤ inputSmallLog N).trans
    (computed_smallLog_le_height N)
  have hr : (computedFamilyResult source target N input).requests ≤
      (inputHeight N ^ 91 + 1) *
        (computedFamilyTree source target N input).widthWork (integerParameters N).M source.length := by
    exact physicalFamilyMemo_requests_le_width source target N (integerParameters N).P
      (inputHeight N) (integerParameters N).T (integerParameters N).S (computedSeedPassCount N)
      (inputHeight N ^ 2) (scheduledSeedFactor N) (scheduledSeedMultiplier N) _ _ _ _
      (clampedSeedNat input.1) (computedParameterP_pos N) input.2 hN hsmall rfl
      (fun p => (scheduledSeedFactor_bounds N p).2) (16384 * inputHeight N + 5)
      (computedFamilyMemoCode source target N (inputHeight N ^ 2))
      (computedFamilyMemoCode_injective source target N (inputHeight N ^ 2) hN hsmall)
      (computedFamilyMemoCode_fits source target N (inputHeight N ^ 2) hN hell hsize le_rfl hB) _
  have hrR : ((computedFamilyResult source target N input).requests : ℝ) ≤
      ((inputHeight N : ℝ) ^ 91 + 1) *
        (computedFamilyTree source target N input).widthWork (integerParameters N).M source.length := by
    exact_mod_cast hr
  exact hrR.trans (mul_le_mul_of_nonneg_left
    (computedFamilyTree_width_le source target N hN hsmall hH hsize input) (by positivity))


end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.computedFamilyResult_requests_le_oai := @OAI.EditApproximation.computedFamilyResult_requests_le_oai
