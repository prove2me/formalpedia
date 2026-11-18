-- Prove2me | solution 1 for OAI.EditApproximation.subtreeComparisonCharges_total
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:47:26.927271+00:00
-- url     : https://prove2.me/submissions/989cf713-2614-4b0b-940c-97739cc7932e

import Mathlib
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_stageWarmup_invariants
import Theorems.Thm_OAI_EditApproximation_subtreeComparisonCharges_local

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

/-- The final scalar summation of the local curvature/energy estimates.
The conservation identities are supplied by `tree_frontier_telescope` for
the comparison masses and energies. -/
theorem curvature_total_from_telescope {ι : Type*} (nodes : Finset ι)
    (curvature discrepancy massDifference movement slack energyDifference : ι → ℝ)
    (D rootMass terminalMass : ℝ)
    (hroot : 0 ≤ rootMass) (hterminal : terminalMass ≤ 2 * D)
    (hconservation : (∑ v ∈ nodes, massDifference v) = rootMass - terminalMass)
    (henergy : (∑ v ∈ nodes, energyDifference v) ≤ 2 * D)
    (hdiscrepancy : ∀ v ∈ nodes, 0 ≤ discrepancy v)
    (hslackNonneg : ∀ v ∈ nodes, 0 ≤ slack v)
    (hslack : ∀ v ∈ nodes, massDifference v + discrepancy v ≤ slack v)
    (hcurvature : ∀ v ∈ nodes, curvature v ≤ energyDifference v + 3 * movement v +
      2 * max (-massDifference v) 0) :
    (∑ v ∈ nodes, (curvature v + discrepancy v)) ≤
      8 * D + 3 * (∑ v ∈ nodes, movement v) + 4 * (∑ v ∈ nodes, slack v) := by
  have hpositive (v : ι) (hv : v ∈ nodes) : max (massDifference v) 0 ≤ slack v := by
    apply max_le
    · linarith [hslack v hv, hdiscrepancy v hv]
    · exact hslackNonneg v hv
  have hidentity : (∑ v ∈ nodes, max (-massDifference v) 0) =
      (∑ v ∈ nodes, max (massDifference v) 0) - rootMass + terminalMass := by
    have hpoint (v : ι) : max (-massDifference v) 0 =
        max (massDifference v) 0 - massDifference v := by
      by_cases h : 0 ≤ massDifference v
      · rw [max_eq_left h, max_eq_right (by linarith : -massDifference v ≤ 0)]
        ring
      · rw [max_eq_right (by linarith : massDifference v ≤ 0),
          max_eq_left (by linarith : 0 ≤ -massDifference v)]
        ring
    simp_rw [hpoint]
    rw [sum_sub_distrib, hconservation]
    ring
  have hnegative : (∑ v ∈ nodes, max (-massDifference v) 0) ≤
      (∑ v ∈ nodes, slack v) + 2 * D := by
    rw [hidentity]
    have hsum := sum_le_sum hpositive
    linarith
  have hG : (∑ v ∈ nodes, discrepancy v) ≤
      (∑ v ∈ nodes, max (-massDifference v) 0) + (∑ v ∈ nodes, slack v) := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro v hv
    have hminus := le_max_left (-massDifference v) 0
    linarith [hslack v hv]
  have hK : (∑ v ∈ nodes, curvature v) ≤
      (∑ v ∈ nodes, energyDifference v) + 3 * (∑ v ∈ nodes, movement v) +
        2 * (∑ v ∈ nodes, max (-massDifference v) 0) := by
    have hsum := sum_le_sum hcurvature
    simpa only [sum_add_distrib, ← mul_sum] using hsum
  rw [sum_add_distrib]
  linarith

/-- Substituting the endpoint and warmup slack totals gives the
manuscript's stated curvature constant. Here `u=J/P` and `v=J/T`. -/
theorem curvature_total_parameter_bound {total movement slack D F u v : ℝ}
    (hD : 0 ≤ D) (hF : 1 ≤ F) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (htotal : total ≤ 8 * D + 3 * movement + 4 * slack)
    (hmove : movement ≤ 4 * u * D)
    (hslack : slack ≤ 512 * F * u * D + 4 * F * v * D) :
    total ≤ 5000 * F * (1 + u + v) * D := by
  have hF0 : 0 ≤ F := by linarith
  have hroot : 8 * D ≤ 5000 * F * D :=
    mul_le_mul_of_nonneg_right (by linarith) hD
  have huc : (2048 * F + 12) * u * D ≤ 5000 * F * u * D :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : 2048 * F + 12 ≤ 5000 * F) hu) hD
  have hvc : 16 * F * v * D ≤ 5000 * F * v * D :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by nlinarith : 16 * F ≤ 5000 * F) hv) hD
  nlinarith

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ComparisonLiftBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual stopped-tree warmup masses and their energy telescope bounds. -/

namespace EditApproximation

open Finset

theorem gap_energy_bounds {gap mass : ℝ} (hgap : |gap| ≤ mass) :
    0 ≤ gap ^ 2 / mass ∧ gap ^ 2 / mass ≤ mass := by
  have hm : 0 ≤ mass := (abs_nonneg _).trans hgap
  refine ⟨div_nonneg (sq_nonneg _) hm, ?_⟩
  by_cases hz : mass = 0
  · simp only [hz, div_zero, le_refl]
  · have hp : 0 < mass := lt_of_le_of_ne hm (Ne.symm hz)
    apply (div_le_iff₀ hp).2
    have hsq : gap ^ 2 ≤ mass ^ 2 := by
      simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg gap) hgap 2)
    simpa only [pow_two] using hsq

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

theorem comparisonSubtreeLift_bounds {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P) (F : ℝ) (hF : 1 ≤ F)
    (table : PhysicalEntry M J target.length → ℝ)
    (htable : ∀ state, 0 ≤ table state ∧ table state ≤
      2 * F * stateEditCost (physicalSource source state.1) target state.2)
    (root : PhysicalNode M J) (rootQ : TargetInterval target.length) (d : ℕ) (path : TreeLayer M d) :
    0 ≤ comparisonSubtreeLift source target hM P hP table root rootQ d path ∧
      comparisonSubtreeLift source target hM P hP table root rootQ d path ≤
        2 * F * comparisonStateCost source target (comparisonFrontier source target hM P hP
          (some (physicalSourceInterval source.length root, rootQ)) d path) := by
  classical
  unfold comparisonSubtreeLift
  generalize heq : comparisonFrontier source target hM P hP
    (some (physicalSourceInterval source.length root, rootQ)) d path = state
  cases state with
  | none => simp only [stoppedComparisonValue, comparisonStateCost, mul_zero, le_refl, and_self]
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hstop : comparisonStopped source target parent q
    · simp only [stoppedComparisonValue, ite_eq_left hstop, comparisonStateCost]
      refine ⟨Nat.cast_nonneg _, ?_⟩
      have h := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 * F by linarith) (Nat.cast_nonneg
        (stateEditCost (substring source parent.lo parent.hi) target q))
      simpa only [one_mul] using h
    · simp only [stoppedComparisonValue, ite_eq_right hstop, comparisonStateCost]
      split_ifs with hd
      · have hp := comparisonSubtree_active_source source target hM P hP root rootQ d path parent q heq hstop
        have h := htable (physicalSubtreeNode root d path hd, q)
        simpa only [physicalSource, physicalSourceInterval, physicalSubtreeNode, ← hp] using h
      · exact ⟨le_rfl, mul_nonneg (by linarith) (Nat.cast_nonneg _)⟩

theorem comparisonSubtreeLift_gap {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (table : PhysicalEntry M J target.length → ℝ)
    (htable : ∀ state, |stateLengthGap (physicalSource source state.1) target state.2| ≤ table state)
    (root : PhysicalNode M J) (rootQ : TargetInterval target.length)
    (d : ℕ) (hd : root.1.val + d ≤ J) (path : TreeLayer M d) :
    |comparisonStateGap source target (comparisonFrontier source target hM P hP
      (some (physicalSourceInterval source.length root, rootQ)) d path)| ≤
        comparisonSubtreeLift source target hM P hP table root rootQ d path := by
  classical
  unfold comparisonSubtreeLift
  rw [dite_eq_left hd]
  generalize heq : comparisonFrontier source target hM P hP
    (some (physicalSourceInterval source.length root, rootQ)) d path = state
  cases state with
  | none => simp only [comparisonStateGap, stoppedComparisonValue, abs_zero, le_refl]
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hstop : comparisonStopped source target parent q
    · simp only [stoppedComparisonValue, ite_eq_left hstop, comparisonStateGap]
      exact stateEditCost_length_lower (substring source parent.lo parent.hi) target q
    · simp only [stoppedComparisonValue, ite_eq_right hstop, comparisonStateGap]
      have hp := comparisonSubtree_active_source source target hM P hP root rootQ d path parent q heq hstop
      have h := htable (physicalSubtreeNode root d path hd, q)
      simpa only [physicalSource, physicalSourceInterval, physicalSubtreeNode, ← hp] using h

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

include hsize hF hA hseed hT in
 theorem subtreeComparisonMass_bounds (d : ℕ) (path : TreeLayer M d) :
    0 ≤ subtreeComparisonMass source target hM U N P F A hP T root rootQ d path ∧
      subtreeComparisonMass source target hM U N P F A hP T root rootQ d path ≤
        2 * F * comparisonStateCost source target (comparisonFrontier source target hM P hP
          (some (physicalSourceInterval source.length root, rootQ)) d path) := by
  exact comparisonSubtreeLift_bounds source target hM P hP F (by exact_mod_cast hF) _
    (fun state => by
      have h := stageWarmup_invariants source target hM U N P F A hsize hP hF hA hseed T hT state
      have hlower := ((le_max_right _ _).trans h.1).trans (Rat.cast_le.mpr h.2.1)
      have hupper : (stageWarmupMass source target U N P F A T state : ℝ) ≤
          ((2 * F * stateEditCost (physicalSource source state.1) target state.2 : ℚ) : ℝ) :=
        Rat.cast_le.mpr (h.2.2.1.trans h.2.2.2)
      exact ⟨(abs_nonneg _).trans hlower, by simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using hupper⟩)
    root rootQ d path

include hsize hF hA hseed hT in
 theorem subtreeComparisonEnergy_bounds (d : ℕ) (hd : root.1.val + d ≤ J) (path : TreeLayer M d) :
    0 ≤ subtreeComparisonEnergy source target hM U N P F A hP T root rootQ d path ∧
      subtreeComparisonEnergy source target hM U N P F A hP T root rootQ d path ≤
        subtreeComparisonMass source target hM U N P F A hP T root rootQ d path := by
  apply gap_energy_bounds
  exact comparisonSubtreeLift_gap source target hM P hP _
    (fun state => by
      have h := stageWarmup_invariants source target hM U N P F A hsize hP hF hA hseed T hT state
      exact ((le_max_right _ _).trans h.1).trans (Rat.cast_le.mpr h.2.1)) root rootQ d hd path

 theorem subtreeComparisonMass_terminal (K : ℕ) (hheight : root.1.val + K = J) (hcapacity : source.length ≤ M ^ J) (path : TreeLayer M K) :
    subtreeComparisonMass source target hM U N P F A hP T root rootQ K path =
      comparisonStateCost source target (comparisonFrontier source target hM P hP
        (some (physicalSourceInterval source.length root, rootQ)) K path) := by
  exact comparisonSubtreeLift_terminal source target hM P hP _ root rootQ K hheight hcapacity path

include hsize hF hA hseed hT in
 theorem subtreeComparisonEnergy_telescope (K : ℕ) (hheight : root.1.val + K = J) (hcapacity : source.length ≤ M ^ J)
    (hsmall : (K : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) :
    (∑ d ∈ range K, ∑ path : TreeLayer M d,
      ((∑ i : Fin M, subtreeComparisonEnergy source target hM U N P F A hP T root rootQ (d + 1) (path, i)) -
        subtreeComparisonEnergy source target hM U N P F A hP T root rootQ d path)) ≤
      2 * comparisonStateCost source target (some (physicalSourceInterval source.length root, rootQ)) := by
  have htel := tree_frontier_telescope M K (subtreeComparisonEnergy source target hM U N P F A hP T root rootQ)
  have heq : (∑ d ∈ range K, ∑ path : TreeLayer M d,
      ((∑ i : Fin M, subtreeComparisonEnergy source target hM U N P F A hP T root rootQ (d + 1) (path, i)) -
        subtreeComparisonEnergy source target hM U N P F A hP T root rootQ d path)) =
      (∑ path : TreeLayer M K, subtreeComparisonEnergy source target hM U N P F A hP T root rootQ K path) -
        subtreeComparisonEnergy source target hM U N P F A hP T root rootQ 0 PUnit.unit := by
    have h := congrArg Neg.neg htel
    simp only [← sum_neg_distrib, neg_sub] at h
    exact h
  rw [heq]
  have hroot := (subtreeComparisonEnergy_bounds source target hM U N P F A hsize hP hF hA hseed T hT root rootQ
    0 (by omega) PUnit.unit).1
  have hterminal := sum_le_sum (fun path (_ : path ∈ (univ : Finset (TreeLayer M K))) =>
    (subtreeComparisonEnergy_bounds source target hM U N P F A hsize hP hF hA hseed T hT root rootQ K (by omega) path).2)
  simp_rw [subtreeComparisonMass_terminal source target hM U N P F A hP T root rootQ K hheight hcapacity] at hterminal
  have hcost := comparison_frontier_cost_le_twice source target hM P hP
    (some (physicalSourceInterval source.length root, rootQ)) K K le_rfl hsmall
  linarith only [hroot, hterminal, hcost]

end Warmup

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_StageComparisonCharges
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.scheduledSeedDrawFintype
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

theorem comparisonMovement_nonneg {β : Type*} (x y : List β) (P : ℕ)
    (state : ComparisonState x.length y.length) : 0 ≤ comparisonMovement x y P state := by
  classical
  cases state with
  | none => exact le_rfl
  | some state =>
    rcases state with ⟨parent, q⟩
    unfold comparisonMovement
    dsimp only
    split_ifs
    · exact le_rfl
    · exact Nat.cast_nonneg _

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSubtreeCharges
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.physicalMedianUpdateTable_value _root_.OAI.EditApproximation.physicalNodeCodeWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.treeLayerCodeWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
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
 theorem subtreeComparisonCharges_total_oai (hscale : 2 * (refinementFactor A F : ℝ) ≤ P)
    (hcapacity : source.length ≤ M ^ J)
    (hsmall : (K : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) :
    (∑ v : (Σ d : Fin K, TreeLayer M d.val),
      ((subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ v.1 v.2).1 +
        (subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ v.1 v.2).2)) ≤
      5000 * F * (1 + (K : ℝ) / P + (K : ℝ) / T) *
        comparisonStateCost source target (some (physicalSourceInterval source.length root, rootQ)) := by
  let ι := Σ d : Fin K, TreeLayer M d.val
  let D := comparisonStateCost source target (some (physicalSourceInterval source.length root, rootQ))
  let curvatures : ι → ℝ := fun v => (subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ v.1 v.2).1
  let G : ι → ℝ := fun v => (subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ v.1 v.2).2
  let R : ι → ℝ := fun v => mass v.1.val v.2 - ∑ i : Fin M, mass (v.1.val + 1) (v.2, i)
  let E : ι → ℝ := fun v => (∑ i : Fin M, energy (v.1.val + 1) (v.2, i)) - energy v.1.val v.2
  let movement : ι → ℝ := fun v => comparisonMovement source target P (frontier v.1.val v.2)
  let slack : ι → ℝ := fun v => (128 * (F : ℝ)) * movement v +
    (2 * F / (T : ℝ)) * comparisonActiveCost source target (frontier v.1.val v.2)
  have hlocal (v : ι) := subtreeComparisonCharges_local source target hM U N P F A hsize hP hF hA hseed
    T hT root K hheight rootQ hscale v.1 v.2
  have hroot := (subtreeComparisonMass_bounds source target hM U N P F A hsize hP hF hA hseed T hT root rootQ
    0 PUnit.unit).1
  have hterminal : (∑ path : TreeLayer M K, mass K path) ≤ 2 * D := by
    simp_rw [subtreeComparisonMass_terminal source target hM U N P F A hP T root rootQ K hheight hcapacity]
    exact comparison_frontier_cost_le_twice source target hM P hP _ K K le_rfl hsmall
  have hconservation : (∑ v : ι, R v) = mass 0 PUnit.unit - ∑ path : TreeLayer M K, mass K path := by
    dsimp only [R, ι]
    have h := treeLayer_sigma_sum M K (fun d path => mass d path - ∑ i : Fin M, mass (d + 1) (path, i))
    exact h.trans (tree_frontier_telescope M K mass)
  have henergy : (∑ v : ι, E v) ≤ 2 * D := by
    dsimp only [E, ι]
    have h := treeLayer_sigma_sum M K (fun d path => (∑ i : Fin M, energy (d + 1) (path, i)) - energy d path)
    apply h.le.trans
    exact subtreeComparisonEnergy_telescope source target hM U N P F A hsize hP hF hA hseed T hT root rootQ
      K hheight hcapacity hsmall
  have hF0 : (0 : ℝ) ≤ F := Nat.cast_nonneg _
  have hslack (v : ι) : 0 ≤ slack v := by
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hF0)
      (comparisonMovement_nonneg source target P _))
      (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hF0) (Nat.cast_nonneg _))
        (comparisonActiveCost_bounds source target _).1)
  have htotal := curvature_total_from_telescope (univ : Finset ι) curvatures G R movement slack E D
    (mass 0 PUnit.unit) (∑ path : TreeLayer M K, mass K path) hroot hterminal hconservation henergy
    (fun v _ => (hlocal v).2.1) (fun v _ => hslack v)
    (fun v _ => (hlocal v).2.2.1) (fun v _ => (hlocal v).2.2.2)
  have hmove : (∑ v : ι, movement v) ≤ 4 * ((K : ℝ) / P) * D := by
    dsimp only [movement, ι]
    have heq := treeLayer_sigma_sum M K (fun d path => comparisonMovement source target P (frontier d path))
    apply heq.le.trans
    have h := comparison_total_movement_bound source target hM P hP
      (some (physicalSourceInterval source.length root, rootQ)) K hsmall
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hactive : (∑ v : ι, comparisonActiveCost source target (frontier v.1.val v.2)) ≤ 2 * K * D := by
    dsimp only [ι]
    have heq := treeLayer_sigma_sum M K (fun d path => comparisonActiveCost source target (frontier d path))
    apply heq.le.trans
    exact comparison_total_active_cost_bound source target hM P hP _ K hsmall
  have hslackSum : (∑ v : ι, slack v) ≤
      512 * F * ((K : ℝ) / P) * D + 4 * F * ((K : ℝ) / T) * D := by
    dsimp only [slack]
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    have hm := mul_le_mul_of_nonneg_left hmove (show 0 ≤ 128 * (F : ℝ) from mul_nonneg (by norm_num) hF0)
    have ha := mul_le_mul_of_nonneg_left hactive (show 0 ≤ 2 * (F : ℝ) / (T : ℝ) from
      div_nonneg (mul_nonneg (by norm_num) hF0) (Nat.cast_nonneg _))
    calc
      _ ≤ (128 * (F : ℝ)) * (4 * ((K : ℝ) / P) * D) + (2 * F / (T : ℝ)) * (2 * K * D) := add_le_add hm ha
      _ = _ := by ring
  exact curvature_total_parameter_bound (comparisonStateCost_nonneg source target _)
    (by exact_mod_cast hF) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) htotal hmove hslackSum

end Stage

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.subtreeComparisonCharges_total_oai.{u_1} := @OAI.EditApproximation.subtreeComparisonCharges_total_oai.{u_1}
