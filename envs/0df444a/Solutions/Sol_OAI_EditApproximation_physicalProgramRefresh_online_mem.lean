-- Prove2me | solution 1 for OAI.EditApproximation.physicalProgramRefresh_online_mem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:45:01.734231+00:00
-- url     : https://prove2.me/submissions/b88c82f0-03b6-4032-ad12-0cfb8fa7a7e9

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
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.reduceOnlineIntegerWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.physicalMedianUpdateTable_value _root_.OAI.EditApproximation.physicalNodeCodeWithWork_value _root_.OAI.EditApproximation.physicalSubtreeNode_zero _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.treeLayerCodeWithWork_value _root_.OAI.EditApproximation.triangularChoiceWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
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

local notation "representatives" => stageRepresentatives source target U N P F A

/-- An accepted literal band is retained in its online representative slot. -/
theorem physicalProgramOnlineCandidate_accepted (node : PhysicalInternalNode M J)
    (representative : Fin (representatives node.1).length) (b : ℕ)
    (member : UnskippedBand source target (physicalSourceInterval source.length node.1)
      b P thetaExponent tau F
      (physicalBandChildMassTable source target U N P F A T node.1 node.2)
      (physicalBandChildInitial source target U N P F A node.1 node.2))
    (hget : (representatives node.1).get representative = (b, member.center))
    (children : PhysicalChildTables M target.length) (t : ℕ)
    (integer : Fin (optimizerTriangularMass
      (physicalProgramBandK source target U N P F A T thetaExponent H tau node representative))) :
    physicalProgramOnlineCandidate source target U N P F A T thetaExponent H tau η κ
      node representative children t integer = some (sharedBandRationalAction member.center
      (finiteOptimizerActionDraw member.actions member.nonempty member.envelope
        (rationalOnlineLinear η κ (childGain member.envelope
          (fun t coordinate => children coordinate.1 t coordinate.2))
          (childDecrement member.envelope (fun t coordinate => children coordinate.1 t coordinate.2)) t)
        (physicalProgramBandG source target U N P F A T thetaExponent H tau node representative)
        (physicalProgramBandK source target U N P F A T thetaExponent H tau node representative) integer)) := by
  unfold physicalProgramOnlineCandidate
  rw [hget]
  simp only [physicalBandOnlineCandidate, physicalBandActions,
    testUnskippedBand_accept member, dite_eq_right member.nonempty]
  rfl


/-- The candidate list contains the sampled shared action at every accepted
representative slot, with the supplied child history and current integer. -/
theorem physicalProgramOnline_contains_accepted {R : ℕ} [NeZero R]
    (stream : PhysicalOnlineStreams source target U N P F A T thetaExponent H tau R)
    (node : PhysicalInternalNode M J)
    (representative : Fin (representatives node.1).length) (b : ℕ)
    (member : UnskippedBand source target (physicalSourceInterval source.length node.1)
      b P thetaExponent tau F
      (physicalBandChildMassTable source target U N P F A T node.1 node.2)
      (physicalBandChildInitial source target U N P F A node.1 node.2))
    (hget : (representatives node.1).get representative = (b, member.center))
    (children : PhysicalChildTables M target.length) (t : ℕ) (q : TargetInterval target.length)
    (hquery : physicalProgramOnlineGuard source target U N P F A node.1 q (b, member.center)) :
    sharedBandRationalAction member.center
      (finiteOptimizerActionDraw member.actions member.nonempty member.envelope
        (rationalOnlineLinear η κ (childGain member.envelope
          (fun t coordinate => children coordinate.1 t coordinate.2))
          (childDecrement member.envelope (fun t coordinate => children coordinate.1 t coordinate.2)) t)
        (physicalProgramBandG source target U N P F A T thetaExponent H tau node representative)
        (physicalProgramBandK source target U N P F A T thetaExponent H tau node representative)
        (stream node representative (Fin.ofNat R t))) ∈
      physicalProgramOnline source target U N P F A T thetaExponent H tau η κ
        stream node.1 children (t + 1) q := by
  rw [physicalProgramOnline, dite_eq_left node.2]
  apply List.mem_filterMap.mpr
  refine ⟨representative, List.mem_filter.mpr ⟨by simp, ?_⟩, ?_⟩
  · simpa only [hget, decide_eq_true_eq] using hquery
  · simpa only [Nat.add_sub_cancel] using
      physicalProgramOnlineCandidate_accepted source target U N P F A T thetaExponent H tau η κ
        node representative b member hget children t (stream node representative (Fin.ofNat R t))


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

/-- Literal query-filtered selections contain the accepted physical sampler
using the same complete child history. -/
theorem physicalProgram_online_action_mem (online : Online) (groups : Groups) (delta : ℚ)
    (node : PhysicalInternalNode M J)
    (representative : Fin (stageRepresentatives source target U N P F A node.1).length) (b : ℕ)
    (member : UnskippedBand source target (physicalSourceInterval source.length node.1)
      b P thetaExponent tau F
      (physicalBandChildMassTable source target U N P F A T node.1 node.2)
      (physicalBandChildInitial source target U N P F A node.1 node.2))
    (hget : (stageRepresentatives source target U N P F A node.1).get representative = (b, member.center))
    (t : ℕ) (q : TargetInterval target.length)
    (hquery : physicalProgramOnlineGuard source target U N P F A node.1 q (b, member.center)) :
    sharedBandRationalAction member.center
      (physicalBandOnlineDraw source target U N P F A T delta (program online groups) node.1 node.2
        b thetaExponent tau member.center member.nonempty η κ
        (physicalProgramBandG source target U N P F A T thetaExponent H tau node representative)
        (physicalProgramBandK source target U N P F A T thetaExponent H tau node representative) t
        (online node representative (Fin.ofNat R t))) ∈
      physicalNodeOnline source target U N P F A T delta (program online groups) node.1 node.2 t q := by
  exact physicalProgramOnline_contains_accepted source target U N P F A T thetaExponent H tau η κ
    online node representative b member hget
    (physicalNodeChildren source target U N P F A T delta (program online groups) node.1 node.2) t q hquery


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
theorem physicalProgramRefresh_online
    (draw : PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau)
    (online : PhysicalOnlineKey source target U N P F A)
    (group : PhysicalGroupKey source target U N P F A thetaExponent) (fresh) :
    (physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau
      (physicalProgramRefresh source target U N P F A T thetaExponent H Q tau draw online group fresh)).1
        online.1 online.2 = fresh.1 := by
  classical
  rcases online with ⟨node, representative⟩
  rcases group with ⟨groupNode, scale, cell⟩
  dsimp only [physicalProgramDrawStreams, physicalProgramRefresh]
  rw [Function.update_of_ne (show (Sum.inl ⟨node, representative⟩ :
    PhysicalProgramKey source target U N P F A thetaExponent) ≠ Sum.inr ⟨groupNode, scale, cell⟩ from Sum.inl_ne_inr)]
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
local notation "G" => physicalProgramBandG source target U N P F A T thetaExponent H tau node representative
local notation "K" => physicalProgramBandK source target U N P F A T thetaExponent H tau node representative
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

/-- The literal online slot supplies the reference-environment sampler
at the refreshed integer; no candidate-list premise remains. -/
theorem physicalProgramRefresh_online_mem_oai (draw : Draw) (fresh : Fresh)
    (member : UnskippedBand source target (physicalSourceInterval source.length node.1)
      b P thetaExponent tau F
      (physicalBandChildMassTable source target U N P F A T node.1 node.2)
      (physicalBandChildInitial source target U N P F A node.1 node.2))
    (hget : (stageRepresentatives source target U N P F A node.1).get representative = (b, member.center))
    (t : ℕ) (q : TargetInterval target.length)
    (hquery : physicalProgramOnlineGuard source target U N P F A node.1 q (b, member.center)) :
    sharedBandRationalAction member.center
      (physicalBandOnlineDraw source target U N P F A T delta (choices draw) node.1 node.2
        b thetaExponent tau member.center member.nonempty η κ G K t (parentOnlineDraw fresh t)) ∈
      physicalNodeOnline source target U N P F A T delta
        (choices (refresh draw onlineKey groupKey fresh)) node.1 node.2 t q := by
  let streams := physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau
    (refresh draw onlineKey groupKey fresh)
  have hmem := physicalProgram_online_action_mem source target U N P F A T thetaExponent H Q tau η κ
    streams.1 streams.2 delta node representative b member hget t q hquery
  have hhistory := physicalProgramRefresh_history source target U N P F A T thetaExponent H Q tau delta η κ
    node representative scale cell draw fresh
  have hinteger := congrFun (physicalProgramRefresh_online source target U N P F A T thetaExponent H Q tau
    draw onlineKey groupKey fresh) (Fin.ofNat R t)
  change streams.1 node representative (Fin.ofNat R t) = parentOnlineDraw fresh t at hinteger
  change sharedBandRationalAction member.center
    (physicalBandOnlineDraw source target U N P F A T delta
      (choices (refresh draw onlineKey groupKey fresh)) node.1 node.2 b thetaExponent tau member.center
      member.nonempty η κ G K t (streams.1 node representative (Fin.ofNat R t))) ∈
      physicalNodeOnline source target U N P F A T delta
        (choices (refresh draw onlineKey groupKey fresh)) node.1 node.2 t q at hmem
  simpa only [physicalBandOnlineDraw, hhistory, hinteger] using hmem

end RefreshWiring

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.physicalProgramRefresh_online_mem_oai.{u_1} := @OAI.EditApproximation.physicalProgramRefresh_online_mem_oai.{u_1}
