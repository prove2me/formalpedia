-- Prove2me | solution 1 for OAI.EditApproximation.physical_tree_expected_excess
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:46:31.985254+00:00
-- url     : https://prove2.me/submissions/1fe89459-ec51-4ab3-aea0-d3dc7cf8d876

import Mathlib
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_physicalRefinement_zero_cost
import Theorems.Thm_OAI_EditApproximation_stageWarmup_postfixed

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BalancedWidths
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
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
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalSubtreeNode_zero _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.treeLayerCodeWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
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

theorem comparisonStep_stopped_or_width {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (node : ComparisonState source.length target.length) (w : ℕ)
    (hnode : ∀ parent q, node = some (parent, q) →
      comparisonStopped source target parent q ∨ parent.hi - parent.lo ≤ w)
    (i : Fin M) (resultParent : TargetInterval source.length) (resultQ : TargetInterval target.length)
    (heq : comparisonStep source target hM P hP node i = some (resultParent, resultQ)) :
    comparisonStopped source target resultParent resultQ ∨
      resultParent.hi - resultParent.lo ≤ w ⌈/⌉ M := by
  classical
  cases node with
  | none => cases heq
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hs : comparisonStopped source target parent q
    · simp only [comparisonStep, dite_eq_left hs] at heq
      split_ifs at heq with hi
      have hpq := Option.some.inj heq
      have hp : parent = resultParent := congrArg Prod.fst hpq
      have hq : q = resultQ := congrArg Prod.snd hpq
      exact Or.inl (by rw [← hp, ← hq]; exact hs)
    · simp only [comparisonStep, dite_eq_right hs] at heq
      have hpq := Option.some.inj heq
      have hp : sourceChild parent i = resultParent := congrArg Prod.fst hpq
      have hw := (hnode parent q rfl).resolve_left hs
      apply Or.inr
      rw [← hp]
      exact (sourceChild_width_le_ceiling parent i).trans ((gc_mul_ceilDiv hM).monotone_l hw)

theorem comparison_frontier_stopped_or_width {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (rootParent : TargetInterval source.length) (rootQ : TargetInterval target.length)
    (d : ℕ) (node : TreeLayer M d)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (heq : comparisonFrontier source target hM P hP (some (rootParent, rootQ)) d node = some (parent, q)) :
    comparisonStopped source target parent q ∨
      parent.hi - parent.lo ≤ (rootParent.hi - rootParent.lo) ⌈/⌉ M ^ d := by
  induction d generalizing parent q with
  | zero =>
    change some (rootParent, rootQ) = some (parent, q) at heq
    have hp : rootParent = parent := congrArg Prod.fst (Option.some.inj heq)
    apply Or.inr
    rw [← hp, pow_zero]
    simp
  | succ d ih =>
    have h := comparisonStep_stopped_or_width source target hM P hP
      (comparisonFrontier source target hM P hP (some (rootParent, rootQ)) d node.1)
      ((rootParent.hi - rootParent.lo) ⌈/⌉ M ^ d)
      (fun parent q heq => ih node.1 parent q heq) node.2 parent q heq
    rw [ceilDiv_comp _ _ _ (pow_pos hM d) hM, ← pow_succ] at h
    exact h

theorem comparison_frontier_terminal {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (rootParent : TargetInterval source.length) (rootQ : TargetInterval target.length) (J : ℕ)
    (hcapacity : rootParent.hi - rootParent.lo ≤ M ^ J) (node : TreeLayer M J)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (heq : comparisonFrontier source target hM P hP (some (rootParent, rootQ)) J node = some (parent, q)) :
    comparisonStopped source target parent q := by
  rcases comparison_frontier_stopped_or_width source target hM P hP rootParent rootQ J node parent q heq with h | h
  · exact h
  · apply Or.inl
    exact h.trans ((ceilDiv_le_iff_le_mul (pow_pos hM J)).2 (by simpa using hcapacity))

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

theorem comparisonPhysicalLift_root {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (table : PhysicalEntry M J target.length → ℝ)
    (hterminal : ∀ node q, comparisonStopped source target (physicalSourceInterval source.length node) q →
      table (node, q) = stateEditCost (physicalSource source node) target q)
    (rootQ : TargetInterval target.length) :
    comparisonPhysicalLift source target hM P hP table rootQ 0 PUnit.unit =
      table (⟨⟨0, by omega⟩, PUnit.unit⟩, rootQ) := by
  classical
  unfold comparisonPhysicalLift
  rw [dite_eq_left (Nat.zero_le J)]
  exact stoppedComparisonValue_physical source target table hterminal _ rootQ

theorem comparisonPhysicalLift_terminal {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (table : PhysicalEntry M J target.length → ℝ) (rootQ : TargetInterval target.length)
    (hcapacity : source.length ≤ M ^ J) (path : TreeLayer M J) :
    comparisonPhysicalLift source target hM P hP table rootQ J path =
      comparisonStateCost source target (comparisonFrontier source target hM P hP
        (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) J path) := by
  classical
  unfold comparisonPhysicalLift
  generalize heq : comparisonFrontier source target hM P hP
    (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) J path = state
  cases state with
  | none => rfl
  | some state =>
    rcases state with ⟨parent, q⟩
    have hstop := comparison_frontier_terminal source target hM P hP
      (sourceIntervalAt M source.length 0 PUnit.unit) rootQ J hcapacity path parent q heq
    simp only [stoppedComparisonValue, ite_eq_left hstop, comparisonStateCost]

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalTreeRegret
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.physicalMedianUpdateTable_value _root_.OAI.EditApproximation.physicalNodeCodeWithWork_value _root_.OAI.EditApproximation.physicalSubtreeNode_zero _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.treeLayerCodeWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The time and comparison-tree telescope for the actual clipped refinement values. -/

namespace EditApproximation

open Finset

theorem comparisonPhysicalLift_mono {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (table table' : PhysicalEntry M J target.length → ℝ) (hle : table ≤ table')
    (rootQ : TargetInterval target.length) (d : ℕ) (path : TreeLayer M d) :
    comparisonPhysicalLift source target hM P hP table rootQ d path ≤
      comparisonPhysicalLift source target hM P hP table' rootQ d path := by
  classical
  unfold comparisonPhysicalLift stoppedComparisonValue
  generalize comparisonFrontier source target hM P hP
    (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) d path = state
  cases state with
  | none => exact le_rfl
  | some state =>
    rcases state with ⟨parent, q⟩
    dsimp only
    split_ifs
    · exact le_rfl
    · exact hle _
    · exact le_rfl

section Refinement

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A)) (rootQ : TargetInterval target.length)

local notation "lifted" => physicalClippedLift source target hM U N P F A hP T delta choices rootQ
local notation "frontier" => comparisonFrontier source target hM P hP
  (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))

 theorem physicalClippedLift_antitone (d : ℕ) (path : TreeLayer M d) : Antitone (fun t => lifted t d path) := by
  apply antitone_nat_of_succ_le
  intro t
  apply comparisonPhysicalLift_mono
  intro state
  apply max_le_max_left
  exact Rat.cast_le.mpr (physicalRefinement_nonincreasing source target U N P F A T delta choices state.1 t state.2)

include hsize hF hA hseed hT in
 theorem physicalClippedLift_root (t : ℕ) : lifted t 0 PUnit.unit =
    max (stateEditCost source target rootQ : ℝ)
      (physicalRefinement source target U N P F A T delta choices
        (⟨⟨0, by omega⟩, PUnit.unit⟩ : PhysicalNode M J) t rootQ : ℝ) := by
  have h := comparisonPhysicalLift_root source target hM P hP
    (physicalClippedTable source target U N P F A T delta choices t)
    (fun node q hstop => by
      have heq := physicalRefinement_at_stopped source target hM U N P F A hsize hP hF hA hseed
        T hT delta choices node t q hstop
      simp only [physicalClippedTable, heq, Rat.cast_natCast, max_self]) rootQ
  simpa only [physicalClippedLift, physicalClippedTable, physicalSource, physicalSourceInterval,
    sourceIntervalAt, substring, List.take_length, List.drop_zero] using h

 theorem physicalClippedLift_terminal (t : ℕ) (hcapacity : source.length ≤ M ^ J) (path : TreeLayer M J) :
    lifted t J path = comparisonStateCost source target (frontier J path) :=
  comparisonPhysicalLift_terminal source target hM P hP _ rootQ hcapacity path

include hsize hF hA hseed hT in
 theorem physical_tree_regret_time (S : ℕ) (hcapacity : source.length ≤ M ^ J)
    (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) :
    (S : ℝ) * max (stateEditCost source target rootQ : ℝ)
      (physicalRefinement source target U N P F A T delta choices
        (⟨⟨0, by omega⟩, PUnit.unit⟩ : PhysicalNode M J) S rootQ : ℝ) ≤
      (S : ℝ) * ((1 + (8 * (M : ℝ) + 512 * F) * J / P) * stateEditCost source target rootQ) +
        ∑ t ∈ range S, ∑ d ∈ range J, ∑ path : TreeLayer M d,
          (lifted (t + 1) d path - (128 * (F : ℝ)) * comparisonMovement source target P (frontier d path) -
            ∑ i : Fin M, lifted (t + 1) (d + 1) (path, i)) := by
  let D : ℝ := stateEditCost source target rootQ
  let charge := fun d (path : TreeLayer M d) => (128 * (F : ℝ)) * comparisonMovement source target P (frontier d path)
  let terminal := (1 + 8 * (M : ℝ) * J / P) * D
  have hrootCost : comparisonStateCost source target
      (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) = D := by
    simp only [comparisonStateCost, sourceIntervalAt, substring, List.take_length, List.drop_zero, D]
  have hterminal (t : ℕ) (_ht : t < S) : (∑ path : TreeLayer M J, lifted (t + 1) J path) ≤ terminal := by
    simp_rw [physicalClippedLift_terminal source target hM U N P F A hP T delta choices rootQ (t + 1) hcapacity]
    have h := comparison_frontier_cost_slack source target hM P hP
      (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) J hsmall
    rw [hrootCost] at h
    exact h
  have htime := tree_regret_time_bound M J S lifted charge terminal
    (fun t ht => physicalClippedLift_antitone source target hM U N P F A hP T delta choices rootQ
      0 PUnit.unit (by omega)) hterminal
  rw [physicalClippedLift_root source target hM U N P F A hsize hP hF hA hseed T hT delta choices rootQ S] at htime
  have hmovement := comparison_total_movement_bound source target hM P hP
    (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) J hsmall
  rw [hrootCost] at hmovement
  have hcharge : (∑ d ∈ range J, ∑ path : TreeLayer M d, charge d path) ≤ 512 * F * J * D / P := by
    dsimp only [charge]
    simp only [← mul_sum]
    have h := mul_le_mul_of_nonneg_left hmovement
      (show (0 : ℝ) ≤ 128 * F from mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hterm : terminal + (∑ d ∈ range J, ∑ path : TreeLayer M d, charge d path) ≤
      (1 + (8 * (M : ℝ) + 512 * F) * J / P) * D := by
    calc
      _ ≤ terminal + 512 * F * J * D / P := add_le_add_right hcharge terminal
      _ = _ := by dsimp only [terminal] <;> ring
  exact htime.trans (add_le_add_left (mul_le_mul_of_nonneg_left hterm (Nat.cast_nonneg S)) _)

end Refinement

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalTreeExpectation
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
    (stageRepresentatives source target U N P F A)) (rootQ : TargetInterval target.length)
  (μ : Measure Ω) [IsProbabilityMeasure μ]

local notation "D" => (stateEditCost source target rootQ : ℝ)
local notation "root" => (Sigma.mk (Fin.mk 0 (Nat.zero_lt_succ J)) PUnit.unit : PhysicalNode M J)
local notation "lifted" => fun ω => physicalClippedLift source target hM U N P F A hP T delta (choices ω) rootQ
local notation "frontier" => comparisonFrontier source target hM P hP
  (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))

include hsize hF hA hseed hT in
 theorem physical_tree_expected_excess_oai (S : ℕ) (hS : 0 < S)
    (hcapacity : source.length ≤ M ^ J) (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2)
    (budget : (d : ℕ) → TreeLayer M d → ℝ)
    (hnode : ∀ d < J, ∀ path : TreeLayer M d,
      (∫ ω, (∑ t ∈ range S,
        (lifted ω (t + 1) d path - (128 * (F : ℝ)) * comparisonMovement source target P (frontier d path) -
          ∑ i : Fin M, lifted ω (t + 1) (d + 1) (path, i))) ∂μ) ≤ budget d path) :
    (∫ ω, max ((physicalRefinement source target U N P F A T delta (choices ω) root S rootQ : ℝ) - D) 0 ∂μ) ≤
      ((8 * (M : ℝ) + 512 * F) * J / P) * D +
        (∑ d ∈ range J, ∑ path : TreeLayer M d, budget d path) / S := by
  let charge := fun d (path : TreeLayer M d) => (128 * (F : ℝ)) * comparisonMovement source target P (frontier d path)
  let regret := fun ω t d (path : TreeLayer M d) =>
    lifted ω (t + 1) d path - charge d path - ∑ i : Fin M, lifted ω (t + 1) (d + 1) (path, i)
  let coefficient : ℝ := (8 * (M : ℝ) + 512 * F) * J / P
  have hpoint (ω : Ω) := physical_tree_regret_time source target hM U N P F A hsize hP hF hA hseed
    T hT delta (choices ω) rootQ S hcapacity hsmall
  have hmean := integral_mono (μ := μ) (.of_finite) (.of_finite) hpoint
  have hregret : (∫ ω, (∑ t ∈ range S, ∑ d ∈ range J, ∑ path : TreeLayer M d, regret ω t d path) ∂μ) ≤
      ∑ d ∈ range J, ∑ path : TreeLayer M d, budget d path := by
    have hswap (ω : Ω) : (∑ t ∈ range S, ∑ d ∈ range J, ∑ path : TreeLayer M d, regret ω t d path) =
        ∑ d ∈ range J, ∑ path : TreeLayer M d, ∑ t ∈ range S, regret ω t d path := by
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
      (∑ t ∈ range S, ∑ d ∈ range J, ∑ path : TreeLayer M d, regret ω t d path) ∂μ) at hmean
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

theorem solution.{u_1, u_2} : type_of% @OAI.EditApproximation.physical_tree_expected_excess_oai.{u_1, u_2} := @OAI.EditApproximation.physical_tree_expected_excess_oai.{u_1, u_2}
