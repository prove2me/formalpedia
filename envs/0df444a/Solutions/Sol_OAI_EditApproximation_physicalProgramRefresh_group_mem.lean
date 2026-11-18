-- Prove2me | solution 1 for OAI.EditApproximation.physicalProgramRefresh_group_mem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:45:32.591962+00:00
-- url     : https://prove2.me/submissions/b0997883-335f-4b51-8c8e-bdc186bf74c9

import Mathlib
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea004

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

theorem physicalRefinement_at_last_level {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J) (hlast : node.1.val = J) (t : ℕ) (q : TargetInterval target.length) :
    physicalRefinement source target U N P F A T delta choices node t q =
      stageInitial source target U N P F A (node, q) := by
  rw [physicalRefinement]
  rw [dite_eq_right (by omega : ¬ node.1.val < J)]

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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRefinementLocality
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Locality of the complete physical refinement

Changing selection streams above a fixed level cannot alter histories at
that level or below. This proves the fixed-child environment under
parent-only resampling directly from the executable recurrence.
-/

namespace EditApproximation

/-- The complete history depends only on selection functions at its own
physical level and deeper levels. -/
theorem physicalRefinement_congr_from_level {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (first second : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (d : ℕ) (hgroups : ∀ node, d ≤ node.1.val → first.groups node = second.groups node)
    (honline : ∀ node, d ≤ node.1.val → first.online node = second.online node)
    (node : PhysicalNode M J) (hnode : d ≤ node.1.val) (t : ℕ) (q : TargetInterval target.length) :
    physicalRefinement source target U N P F A T delta first node t q =
      physicalRefinement source target U N P F A T delta second node t q := by
  by_cases hbelow : node.1.val < J
  · by_cases hleaf : (physicalSourceInterval source.length node).hi -
        (physicalSourceInterval source.length node).lo ≤ 1
    · rw [physicalRefinement_at_leaf source target U N P F A T delta first node hleaf,
        physicalRefinement_at_leaf source target U N P F A T delta second node hleaf]
    · have hchildren (i : Fin M) :
          physicalRefinement source target U N P F A T delta first (physicalChild node hbelow i) =
            physicalRefinement source target U N P F A T delta second (physicalChild node hbelow i) := by
        funext t q
        exact physicalRefinement_congr_from_level source target U N P F A T delta first second d hgroups honline
          (physicalChild node hbelow i) (by change d ≤ node.1.val + 1; omega) t q
      cases t with
      | zero =>
        rw [physicalRefinement_zero source target U N P F A T delta first,
          physicalRefinement_zero source target U N P F A T delta second]
      | succ t =>
        rw [physicalRefinement_succ source target U N P F A T delta first node hbelow hleaf,
          physicalRefinement_succ source target U N P F A T delta second node hbelow hleaf]
        simp only [hchildren, hgroups node hnode, honline node hnode]
  · have hlast : node.1.val = J := by have hbound := node.1.isLt; omega
    rw [physicalRefinement_at_last_level source target U N P F A T delta first node hlast,
      physicalRefinement_at_last_level source target U N P F A T delta second node hlast]
termination_by J - node.1.val
decreasing_by
  unfold physicalChild
  dsimp only
  omega

/-- Parent-only resampling fixes every child table, at every refinement
index and target state, without independence assumptions about children. -/
theorem physicalRefinement_children_fixed {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (first second : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (hgroups : ∀ label, node.1.val < label.1.val → first.groups label = second.groups label)
    (honline : ∀ label, node.1.val < label.1.val → first.online label = second.online label) :
    (fun i : Fin M => physicalRefinement source target U N P F A T delta first (physicalChild node hbelow i)) =
      fun i : Fin M => physicalRefinement source target U N P F A T delta second (physicalChild node hbelow i) := by
  funext i t q
  apply physicalRefinement_congr_from_level source target U N P F A T delta first second (node.1.val + 1)
  · intro label hlabel
    exact hgroups label (by omega)
  · intro label hlabel
    exact honline label (by omega)
  · change node.1.val + 1 ≤ node.1.val + 1
    rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSelectionProgram
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.dyadicScalesWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.physicalMedianUpdateTable_value _root_.OAI.EditApproximation.physicalNodeCodeWithWork_value _root_.OAI.EditApproximation.physicalSubtreeNode_zero _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryScaleDispatchWithWork_value _root_.OAI.EditApproximation.queryScalePresentWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.treeLayerCodeWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Finite online and whole-cell candidate programs

Physical selections use the representative and guarded band lists. Each
band has its own finite optimizer stream; every whole cell has shared
per-scale child streams. These streams define coherent finite tables.
-/

namespace EditApproximation

open Finset



section Program

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T thetaExponent H Q : ℕ) (tau η κ : ℚ)

/-- Whole-cell sampling uses the same per-scale arrays for all its members;
the literal selected member is included in the parent candidate list. -/
theorem physicalProgramGroups_contains_selected {R : ℕ} [NeZero R]
    (stream : PhysicalGroupStreams source target U N P F A thetaExponent Q R)
    (node : PhysicalInternalNode M J) (scale : Fin (dyadicScales N).length)
    (cell : Fin (physicalProgramCells source target U N P F A thetaExponent node.1
      ((dyadicScales N).get scale)).length)
    (hnonempty : physicalNodeCellBands source target U N P F A T node.1 node.2
      ((dyadicScales N).get scale) thetaExponent tau
      ((physicalProgramCells source target U N P F A thetaExponent node.1
        ((dyadicScales N).get scale)).get cell) ≠ [])
    (children : PhysicalChildTables M target.length) (t : ℕ) :
    (chooseUnskippedGroup Q (fun i q => children i (t + 1) q)
      (physicalNodeCellBands source target U N P F A T node.1 node.2
        ((dyadicScales N).get scale) thetaExponent tau
        ((physicalProgramCells source target U N P F A thetaExponent node.1
          ((dyadicScales N).get scale)).get cell)) hnonempty
      (stream node scale cell (Fin.ofNat R t))).rationalAction ∈
      physicalProgramGroups source target U N P F A T thetaExponent Q tau stream node.1 children (t + 1) := by
  rw [physicalProgramGroups, dite_eq_left node.2]
  apply List.mem_flatMap.mpr
  refine ⟨scale, by simp, List.mem_filterMap.mpr ⟨cell, by simp, ?_⟩⟩
  unfold physicalNodeCellBands at hnonempty
  simp only [chooseCellGroupAction, Nat.add_sub_cancel, dite_eq_right hnonempty]
  rfl


end Program

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSelectionResampling
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal parent-coordinate replacement in the finite selection program. -/

namespace EditApproximation

section Resampling

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T thetaExponent H Q : ℕ) (tau η κ : ℚ)

local notation "Online" => PhysicalOnlineStreams source target U N P F A T thetaExponent H tau R
local notation "Groups" => PhysicalGroupStreams source target U N P F A thetaExponent Q R
local notation "program" => physicalProgramSelections source target U N P F A T thetaExponent H Q tau η κ

variable [NeZero R]

theorem physicalProgramSelections_online_congr_at (online first : Online) (groups : Groups)
    (node : PhysicalNode M J)
    (hlocal : ∀ hbelow : node.1.val < J, online ⟨node, hbelow⟩ = first ⟨node, hbelow⟩) :
    (program online groups).online node = (program first groups).online node := by
  funext children t q
  dsimp only [physicalProgramSelections]
  unfold physicalProgramOnline
  split_ifs with hbelow
  · rw [hlocal hbelow]
  · rfl

theorem physicalProgramSelections_groups_congr_at (online : Online) (groups first : Groups)
    (node : PhysicalNode M J)
    (hlocal : ∀ hbelow : node.1.val < J, groups ⟨node, hbelow⟩ = first ⟨node, hbelow⟩) :
    (program online groups).groups node = (program online first).groups node := by
  funext children t
  dsimp only [physicalProgramSelections]
  unfold physicalProgramGroups
  split_ifs with hbelow
  · rw [hlocal hbelow]
  · rfl

theorem physicalProgram_group_action_mem (online : Online) (groups : Groups) (delta : ℚ)
    (node : PhysicalInternalNode M J) (scale : Fin (dyadicScales N).length)
    (cell : Fin (physicalProgramCells source target U N P F A thetaExponent node.1
      ((dyadicScales N).get scale)).length)
    (hnonempty : physicalNodeCellBands source target U N P F A T node.1 node.2
      ((dyadicScales N).get scale) thetaExponent tau
      ((physicalProgramCells source target U N P F A thetaExponent node.1
        ((dyadicScales N).get scale)).get cell) ≠ []) (t : ℕ) :
    (physicalNodeSelectedGroup source target U N P F A T delta (program online groups) node.1 node.2
      ((dyadicScales N).get scale) thetaExponent Q tau
      ((physicalProgramCells source target U N P F A thetaExponent node.1
        ((dyadicScales N).get scale)).get cell) hnonempty t
      (groups node scale cell (Fin.ofNat R t))).rationalAction ∈
      physicalNodeGroups source target U N P F A T delta (program online groups) node.1 node.2 t := by
  exact physicalProgramGroups_contains_selected source target U N P F A T thetaExponent Q tau groups
    node scale cell hnonempty
    (physicalNodeChildren source target U N P F A T delta (program online groups) node.1 node.2) t


end Resampling

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalProgramLaw
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The global finite product of actual selection streams

Online slots and whole-cell slots form a finite disjoint union. Each slot
contains its complete finite time array with the prescribed product law.
Mapping the flattened product produces
the actual online/group stream pair without independence hypotheses.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

section GlobalLaw

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T thetaExponent H Q : ℕ) (tau : ℚ)
  [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem physicalProgramRefresh_group
    (draw : PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau)
    (online : PhysicalOnlineKey source target U N P F A)
    (group : PhysicalGroupKey source target U N P F A thetaExponent) (fresh) :
    (physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau
      (physicalProgramRefresh source target U N P F A T thetaExponent H Q tau draw online group fresh)).2
        group.1 group.2.1 group.2.2 = fresh.2 := by
  classical
  rcases group with ⟨node, scale, cell⟩
  dsimp only [physicalProgramDrawStreams, physicalProgramRefresh]
  exact Function.update_self _ _ _

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem physicalProgramRefresh_online_other
    (draw : PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau)
    (online : PhysicalOnlineKey source target U N P F A)
    (group : PhysicalGroupKey source target U N P F A thetaExponent) (fresh)
    (label : PhysicalInternalNode M J) (hne : label ≠ online.1) :
    (physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau
      (physicalProgramRefresh source target U N P F A T thetaExponent H Q tau draw online group fresh)).1 label =
      (physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau draw).1 label := by
  classical
  funext representative
  have hkey : (Sum.inl ⟨label, representative⟩ : PhysicalProgramKey source target U N P F A thetaExponent) ≠
      Sum.inl online := by
    intro heq
    exact hne (congrArg Sigma.fst (Sum.inl.inj heq))
  dsimp only [physicalProgramDrawStreams, physicalProgramRefresh]
  rw [Function.update_of_ne (show (Sum.inl ⟨label, representative⟩ :
    PhysicalProgramKey source target U N P F A thetaExponent) ≠ Sum.inr group from Sum.inl_ne_inr),
    Function.update_of_ne hkey]

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem physicalProgramRefresh_group_other
    (draw : PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau)
    (online : PhysicalOnlineKey source target U N P F A)
    (group : PhysicalGroupKey source target U N P F A thetaExponent) (fresh)
    (label : PhysicalInternalNode M J) (hne : label ≠ group.1) :
    (physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau
      (physicalProgramRefresh source target U N P F A T thetaExponent H Q tau draw online group fresh)).2 label =
      (physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau draw).2 label := by
  classical
  funext scale cell
  have hkey : (Sum.inr ⟨label, scale, cell⟩ : PhysicalProgramKey source target U N P F A thetaExponent) ≠
      Sum.inr group := by
    intro heq
    exact hne (congrArg Sigma.fst (Sum.inr.inj heq))
  dsimp only [physicalProgramDrawStreams, physicalProgramRefresh]
  rw [Function.update_of_ne hkey,
    Function.update_of_ne (show (Sum.inr ⟨label, scale, cell⟩ :
      PhysicalProgramKey source target U N P F A thetaExponent) ≠ Sum.inl online from Sum.inr_ne_inl)]

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
/-- Refreshing a parent's chosen band/cell coordinates leaves every
strictly deeper raw selection function unchanged. -/
theorem physicalProgramDrawSelections_refresh_deeper [NeZero R] (η κ : ℚ)
    (draw : PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau)
    (online : PhysicalOnlineKey source target U N P F A)
    (group : PhysicalGroupKey source target U N P F A thetaExponent) (fresh)
    (label : PhysicalNode M J)
    (honline : online.1.1.1.val < label.1.val) (hgroup : group.1.1.1.val < label.1.val) :
    (physicalProgramDrawSelections source target U N P F A T thetaExponent H Q tau η κ
      (physicalProgramRefresh source target U N P F A T thetaExponent H Q tau draw online group fresh)).groups label =
        (physicalProgramDrawSelections source target U N P F A T thetaExponent H Q tau η κ draw).groups label ∧
    (physicalProgramDrawSelections source target U N P F A T thetaExponent H Q tau η κ
      (physicalProgramRefresh source target U N P F A T thetaExponent H Q tau draw online group fresh)).online label =
        (physicalProgramDrawSelections source target U N P F A T thetaExponent H Q tau η κ draw).online label := by
  have hneOnline (hbelow : label.1.val < J) : (⟨label, hbelow⟩ : PhysicalInternalNode M J) ≠ online.1 := by
    intro heq
    have hdepth := congrArg (fun node : PhysicalInternalNode M J => node.1.1.val) heq
    change label.1.val = online.1.1.1.val at hdepth
    omega
  have hneGroup (hbelow : label.1.val < J) : (⟨label, hbelow⟩ : PhysicalInternalNode M J) ≠ group.1 := by
    intro heq
    have hdepth := congrArg (fun node : PhysicalInternalNode M J => node.1.1.val) heq
    change label.1.val = group.1.1.1.val at hdepth
    omega
  let oldStreams := physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau draw
  let nextStreams := physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau
    (physicalProgramRefresh source target U N P F A T thetaExponent H Q tau draw online group fresh)
  constructor
  · exact physicalProgramSelections_groups_congr_at source target U N P F A T thetaExponent H Q tau η κ
      oldStreams.1 nextStreams.2 oldStreams.2 label (fun hbelow => physicalProgramRefresh_group_other source target U N P F A T thetaExponent H Q tau
        draw online group fresh ⟨label, hbelow⟩ (hneGroup hbelow))
  · exact physicalProgramSelections_online_congr_at source target U N P F A T thetaExponent H Q tau η κ
      nextStreams.1 oldStreams.1 oldStreams.2 label (fun hbelow => physicalProgramRefresh_online_other source target U N P F A T thetaExponent H Q tau
        draw online group fresh ⟨label, hbelow⟩ (hneOnline hbelow))


end GlobalLaw

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalProgramRefreshWiring
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact candidate wiring and complete-child locality under actual two-key refresh. -/

namespace EditApproximation

section RefreshWiring

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T thetaExponent H Q : ℕ) (tau delta η κ : ℚ)
  (node : PhysicalInternalNode M J)
  (representative : Fin (stageRepresentatives source target U N P F A node.1).length)
  (scale : Fin (dyadicScales N).length)
  (cell : Fin (physicalProgramCells source target U N P F A thetaExponent node.1
    ((dyadicScales N).get scale)).length)

local notation "onlineKey" => (Sigma.mk node representative : PhysicalOnlineKey source target U N P F A)
local notation "groupKey" => (Sigma.mk node (Sigma.mk scale cell) : PhysicalGroupKey source target U N P F A thetaExponent)
local notation "b" => List.get (dyadicScales N) scale
local notation "groupCell" => List.get (physicalProgramCells source target U N P F A thetaExponent (Subtype.val node) b) cell
local notation "Draw" => PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau
local notation "Fresh" => PhysicalOnlineArray (R := R) source target U N P F A T thetaExponent H tau onlineKey ×
  PhysicalGroupArray (R := R) source target U N P F A thetaExponent Q groupKey
local notation "choices" => physicalProgramDrawSelections source target U N P F A T thetaExponent H Q tau η κ
local notation "refresh" => physicalProgramRefresh source target U N P F A T thetaExponent H Q tau

/-- Complete child histories remain fixed under replacement of the two
actual random arrays at this parent. -/
theorem physicalProgramRefresh_history (draw : Draw) (fresh : Fresh) :
    physicalBandHistory source target U N P F A T delta (choices (refresh draw onlineKey groupKey fresh)) node.1 node.2 =
      physicalBandHistory source target U N P F A T delta (choices draw) node.1 node.2 := by
  have hchildren := physicalRefinement_children_fixed source target U N P F A T delta
    (choices (refresh draw onlineKey groupKey fresh)) (choices draw) node.1 node.2
    (fun label hdeeper => (physicalProgramDrawSelections_refresh_deeper source target U N P F A T thetaExponent H Q tau η κ
      draw onlineKey groupKey fresh label hdeeper hdeeper).1)
    (fun label hdeeper => (physicalProgramDrawSelections_refresh_deeper source target U N P F A T thetaExponent H Q tau η κ
      draw onlineKey groupKey fresh label hdeeper hdeeper).2)
  funext t coordinate
  exact congrFun (congrFun (congrFun hchildren coordinate.1) t) coordinate.2

/-- The literal whole-cell slot supplies the selected group computed from
the unchanged complete child environment and refreshed shared arrays. -/
theorem physicalProgramRefresh_group_mem_oai (draw : Draw) (fresh : Fresh)
    (hnonempty : physicalNodeCellBands source target U N P F A T node.1 node.2 b thetaExponent tau groupCell ≠ [])
    (t : ℕ) :
    (physicalNodeSelectedGroup source target U N P F A T delta (choices draw) node.1 node.2
      b thetaExponent Q tau groupCell hnonempty t (parentGroupDraw fresh t)).rationalAction ∈
      physicalNodeGroups source target U N P F A T delta
        (choices (refresh draw onlineKey groupKey fresh)) node.1 node.2 t := by
  let streams := physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau
    (refresh draw onlineKey groupKey fresh)
  have hmem := physicalProgram_group_action_mem source target U N P F A T thetaExponent H Q tau η κ
    streams.1 streams.2 delta node scale cell hnonempty t
  have hhistory := physicalProgramRefresh_history source target U N P F A T thetaExponent H Q tau delta η κ
    node representative scale cell draw fresh
  have hdraw := congrFun (physicalProgramRefresh_group source target U N P F A T thetaExponent H Q tau
    draw onlineKey groupKey fresh) (Fin.ofNat R t)
  change streams.2 node scale cell (Fin.ofNat R t) = parentGroupDraw fresh t at hdraw
  change (physicalNodeSelectedGroup source target U N P F A T delta
    (choices (refresh draw onlineKey groupKey fresh)) node.1 node.2 b thetaExponent Q tau groupCell hnonempty t
    (streams.2 node scale cell (Fin.ofNat R t))).rationalAction ∈
      physicalNodeGroups source target U N P F A T delta
        (choices (refresh draw onlineKey groupKey fresh)) node.1 node.2 t at hmem
  simpa only [physicalNodeSelectedGroup, hhistory, hdraw] using hmem

end RefreshWiring

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.physicalProgramRefresh_group_mem_oai.{u_1} := @OAI.EditApproximation.physicalProgramRefresh_group_mem_oai.{u_1}
