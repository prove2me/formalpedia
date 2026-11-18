-- Prove2me | solution 1 for OAI.EditApproximation.stageComparisonCharges_total
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:46:58.733525+00:00
-- url     : https://prove2.me/submissions/c24b6086-cc30-407e-86b2-c20dfbd0fc5b

import Mathlib
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_stageComparisonCharges_local
import Theorems.Thm_OAI_EditApproximation_stageWarmup_invariants

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

theorem comparisonFrontier_active_source {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P) (rootQ : TargetInterval target.length)
    (d : ℕ) (path : TreeLayer M d) (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (heq : comparisonFrontier source target hM P hP
      (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) d path = some (parent, q))
    (hactive : ¬ comparisonStopped source target parent q) :
    parent = sourceIntervalAt M source.length d path := by
  induction d generalizing parent q with
  | zero =>
    have hpq := Option.some.inj heq
    exact (congrArg Prod.fst hpq).symm
  | succ d ih =>
    obtain ⟨previousParent, previousQ, hprevious, hpreviousActive, hchild⟩ :=
      comparisonStep_active_parent source target hM P hP _ path.2 parent q heq hactive
    have hp := ih path.1 previousParent previousQ hprevious hpreviousActive
    rw [hp] at hchild
    exact hchild

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ComparisonLiftBounds
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual stopped-tree warmup masses and their energy telescope bounds. -/

namespace EditApproximation

open Finset

theorem comparisonPhysicalLift_bounds {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P) (F : ℝ) (hF : 1 ≤ F)
    (table : PhysicalEntry M J target.length → ℝ)
    (htable : ∀ state, 0 ≤ table state ∧ table state ≤
      2 * F * stateEditCost (physicalSource source state.1) target state.2)
    (rootQ : TargetInterval target.length) (d : ℕ) (path : TreeLayer M d) :
    0 ≤ comparisonPhysicalLift source target hM P hP table rootQ d path ∧
      comparisonPhysicalLift source target hM P hP table rootQ d path ≤
        2 * F * comparisonStateCost source target (comparisonFrontier source target hM P hP
          (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) d path) := by
  classical
  unfold comparisonPhysicalLift
  generalize heq : comparisonFrontier source target hM P hP
    (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) d path = state
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
      · have hp := comparisonFrontier_active_source source target hM P hP rootQ d path parent q heq hstop
        have h := htable (⟨⟨d, by omega⟩, path⟩, q)
        simpa only [physicalSource, physicalSourceInterval, ← hp] using h
      · exact ⟨le_rfl, mul_nonneg (by linarith) (Nat.cast_nonneg _)⟩

theorem comparisonPhysicalLift_gap {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (table : PhysicalEntry M J target.length → ℝ)
    (htable : ∀ state, |stateLengthGap (physicalSource source state.1) target state.2| ≤ table state)
    (rootQ : TargetInterval target.length) (d : ℕ) (hd : d ≤ J) (path : TreeLayer M d) :
    |comparisonStateGap source target (comparisonFrontier source target hM P hP
      (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) d path)| ≤
        comparisonPhysicalLift source target hM P hP table rootQ d path := by
  classical
  unfold comparisonPhysicalLift
  rw [dite_eq_left hd]
  generalize heq : comparisonFrontier source target hM P hP
    (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) d path = state
  cases state with
  | none => simp only [comparisonStateGap, stoppedComparisonValue, abs_zero, le_refl]
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hstop : comparisonStopped source target parent q
    · simp only [stoppedComparisonValue, ite_eq_left hstop, comparisonStateGap]
      exact stateEditCost_length_lower (substring source parent.lo parent.hi) target q
    · simp only [stoppedComparisonValue, ite_eq_right hstop, comparisonStateGap]
      have hp := comparisonFrontier_active_source source target hM P hP rootQ d path parent q heq hstop
      have h := htable (⟨⟨d, by omega⟩, path⟩, q)
      simpa only [physicalSource, physicalSourceInterval, ← hp] using h

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

section Warmup

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (rootQ : TargetInterval target.length)

include hsize hF hA hseed hT in
 theorem stageComparisonMass_bounds (d : ℕ) (path : TreeLayer M d) :
    0 ≤ stageComparisonMass source target hM U N P F A hP T rootQ d path ∧
      stageComparisonMass source target hM U N P F A hP T rootQ d path ≤
        2 * F * comparisonStateCost source target (comparisonFrontier source target hM P hP
          (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) d path) := by
  exact comparisonPhysicalLift_bounds source target hM P hP F (by exact_mod_cast hF) _
    (fun state => by
      have h := stageWarmup_invariants source target hM U N P F A hsize hP hF hA hseed T hT state
      have hlower := ((le_max_right _ _).trans h.1).trans (Rat.cast_le.mpr h.2.1)
      have hupper : (stageWarmupMass source target U N P F A T state : ℝ) ≤
          ((2 * F * stateEditCost (physicalSource source state.1) target state.2 : ℚ) : ℝ) :=
        Rat.cast_le.mpr (h.2.2.1.trans h.2.2.2)
      exact ⟨(abs_nonneg _).trans hlower, by simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using hupper⟩)
    rootQ d path

include hsize hF hA hseed hT in
 theorem stageComparisonEnergy_bounds (d : ℕ) (hd : d ≤ J) (path : TreeLayer M d) :
    0 ≤ stageComparisonEnergy source target hM U N P F A hP T rootQ d path ∧
      stageComparisonEnergy source target hM U N P F A hP T rootQ d path ≤
        stageComparisonMass source target hM U N P F A hP T rootQ d path := by
  apply gap_energy_bounds
  exact comparisonPhysicalLift_gap source target hM P hP _
    (fun state => by
      have h := stageWarmup_invariants source target hM U N P F A hsize hP hF hA hseed T hT state
      exact ((le_max_right _ _).trans h.1).trans (Rat.cast_le.mpr h.2.1)) rootQ d hd path

 theorem stageComparisonMass_terminal (hcapacity : source.length ≤ M ^ J) (path : TreeLayer M J) :
    stageComparisonMass source target hM U N P F A hP T rootQ J path =
      comparisonStateCost source target (comparisonFrontier source target hM P hP
        (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) J path) := by
  exact comparisonPhysicalLift_terminal source target hM P hP _ rootQ hcapacity path

include hsize hF hA hseed hT in
 theorem stageComparisonEnergy_telescope (hcapacity : source.length ≤ M ^ J)
    (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) :
    (∑ d ∈ range J, ∑ path : TreeLayer M d,
      ((∑ i : Fin M, stageComparisonEnergy source target hM U N P F A hP T rootQ (d + 1) (path, i)) -
        stageComparisonEnergy source target hM U N P F A hP T rootQ d path)) ≤
      2 * comparisonStateCost source target (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) := by
  have htel := tree_frontier_telescope M J (stageComparisonEnergy source target hM U N P F A hP T rootQ)
  have heq : (∑ d ∈ range J, ∑ path : TreeLayer M d,
      ((∑ i : Fin M, stageComparisonEnergy source target hM U N P F A hP T rootQ (d + 1) (path, i)) -
        stageComparisonEnergy source target hM U N P F A hP T rootQ d path)) =
      (∑ path : TreeLayer M J, stageComparisonEnergy source target hM U N P F A hP T rootQ J path) -
        stageComparisonEnergy source target hM U N P F A hP T rootQ 0 PUnit.unit := by
    have h := congrArg Neg.neg htel
    simp only [← sum_neg_distrib, neg_sub] at h
    exact h
  rw [heq]
  have hroot := (stageComparisonEnergy_bounds source target hM U N P F A hsize hP hF hA hseed T hT rootQ
    0 (Nat.zero_le J) PUnit.unit).1
  have hterminal := sum_le_sum (fun path (_ : path ∈ (univ : Finset (TreeLayer M J))) =>
    (stageComparisonEnergy_bounds source target hM U N P F A hsize hP hF hA hseed T hT rootQ J le_rfl path).2)
  simp_rw [stageComparisonMass_terminal source target hM U N P F A hP T rootQ hcapacity] at hterminal
  have hcost := comparison_frontier_cost_le_twice source target hM P hP
    (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) J J le_rfl hsmall
  linarith only [hroot, hterminal, hcost]

end Warmup

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_StageComparisonCharges
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.physicalMedianUpdateTable_value _root_.OAI.EditApproximation.physicalNodeCodeWithWork_value _root_.OAI.EditApproximation.physicalSubtreeNode_zero _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.treeLayerCodeWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
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

local notation "mass" => stageComparisonMass source target hM U N P F A hP T rootQ
local notation "energy" => stageComparisonEnergy source target hM U N P F A hP T rootQ
local notation "frontier" => comparisonFrontier source target hM P hP
  (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))

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

include hsize hF hA hseed hT in
 theorem stageComparisonCharges_total_oai (hscale : 2 * (refinementFactor A F : ℝ) ≤ P)
    (hcapacity : source.length ≤ M ^ J)
    (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) :
    (∑ v : (Σ d : Fin J, TreeLayer M d.val),
      ((stageComparisonCharges source target hM U N P F A hP T rootQ v.1 v.2).1 +
        (stageComparisonCharges source target hM U N P F A hP T rootQ v.1 v.2).2)) ≤
      5000 * F * (1 + (J : ℝ) / P + (J : ℝ) / T) *
        comparisonStateCost source target (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) := by
  let ι := Σ d : Fin J, TreeLayer M d.val
  let D := comparisonStateCost source target (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))
  let K : ι → ℝ := fun v => (stageComparisonCharges source target hM U N P F A hP T rootQ v.1 v.2).1
  let G : ι → ℝ := fun v => (stageComparisonCharges source target hM U N P F A hP T rootQ v.1 v.2).2
  let R : ι → ℝ := fun v => mass v.1.val v.2 - ∑ i : Fin M, mass (v.1.val + 1) (v.2, i)
  let E : ι → ℝ := fun v => (∑ i : Fin M, energy (v.1.val + 1) (v.2, i)) - energy v.1.val v.2
  let movement : ι → ℝ := fun v => comparisonMovement source target P (frontier v.1.val v.2)
  let slack : ι → ℝ := fun v => (128 * (F : ℝ)) * movement v +
    (2 * F / (T : ℝ)) * comparisonActiveCost source target (frontier v.1.val v.2)
  have hlocal (v : ι) := stageComparisonCharges_local source target hM U N P F A hsize hP hF hA hseed
    T hT rootQ hscale v.1 v.2
  have hroot := (stageComparisonMass_bounds source target hM U N P F A hsize hP hF hA hseed T hT rootQ
    0 PUnit.unit).1
  have hterminal : (∑ path : TreeLayer M J, mass J path) ≤ 2 * D := by
    simp_rw [stageComparisonMass_terminal source target hM U N P F A hP T rootQ hcapacity]
    exact comparison_frontier_cost_le_twice source target hM P hP _ J J le_rfl hsmall
  have hconservation : (∑ v : ι, R v) = mass 0 PUnit.unit - ∑ path : TreeLayer M J, mass J path := by
    dsimp only [R, ι]
    have h := treeLayer_sigma_sum M J (fun d path => mass d path - ∑ i : Fin M, mass (d + 1) (path, i))
    exact h.trans (tree_frontier_telescope M J mass)
  have henergy : (∑ v : ι, E v) ≤ 2 * D := by
    dsimp only [E, ι]
    have h := treeLayer_sigma_sum M J (fun d path => (∑ i : Fin M, energy (d + 1) (path, i)) - energy d path)
    apply h.le.trans
    exact stageComparisonEnergy_telescope source target hM U N P F A hsize hP hF hA hseed T hT rootQ
      hcapacity hsmall
  have hF0 : (0 : ℝ) ≤ F := Nat.cast_nonneg _
  have hslack (v : ι) : 0 ≤ slack v := by
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hF0)
      (comparisonMovement_nonneg source target P _))
      (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hF0) (Nat.cast_nonneg _))
        (comparisonActiveCost_bounds source target _).1)
  have htotal := curvature_total_from_telescope (univ : Finset ι) K G R movement slack E D
    (mass 0 PUnit.unit) (∑ path : TreeLayer M J, mass J path) hroot hterminal hconservation henergy
    (fun v _ => (hlocal v).2.1) (fun v _ => hslack v)
    (fun v _ => (hlocal v).2.2.1) (fun v _ => (hlocal v).2.2.2)
  have hmove : (∑ v : ι, movement v) ≤ 4 * ((J : ℝ) / P) * D := by
    dsimp only [movement, ι]
    have heq := treeLayer_sigma_sum M J (fun d path => comparisonMovement source target P (frontier d path))
    apply heq.le.trans
    have h := comparison_total_movement_bound source target hM P hP
      (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) J hsmall
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hactive : (∑ v : ι, comparisonActiveCost source target (frontier v.1.val v.2)) ≤ 2 * J * D := by
    dsimp only [ι]
    have heq := treeLayer_sigma_sum M J (fun d path => comparisonActiveCost source target (frontier d path))
    apply heq.le.trans
    exact comparison_total_active_cost_bound source target hM P hP _ J hsmall
  have hslackSum : (∑ v : ι, slack v) ≤
      512 * F * ((J : ℝ) / P) * D + 4 * F * ((J : ℝ) / T) * D := by
    dsimp only [slack]
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    have hm := mul_le_mul_of_nonneg_left hmove (show 0 ≤ 128 * (F : ℝ) from mul_nonneg (by norm_num) hF0)
    have ha := mul_le_mul_of_nonneg_left hactive (show 0 ≤ 2 * (F : ℝ) / (T : ℝ) from
      div_nonneg (mul_nonneg (by norm_num) hF0) (Nat.cast_nonneg _))
    calc
      _ ≤ (128 * (F : ℝ)) * (4 * ((J : ℝ) / P) * D) + (2 * F / (T : ℝ)) * (2 * J * D) := add_le_add hm ha
      _ = _ := by ring
  exact curvature_total_parameter_bound (comparisonStateCost_nonneg source target _)
    (by exact_mod_cast hF) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) htotal hmove hslackSum

end Stage

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.stageComparisonCharges_total_oai.{u_1} := @OAI.EditApproximation.stageComparisonCharges_total_oai.{u_1}
