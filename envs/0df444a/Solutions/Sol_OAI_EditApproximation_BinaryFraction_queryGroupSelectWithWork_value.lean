-- Prove2me | solution 1 for OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWork_value
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:23:19.529058+00:00
-- url     : https://prove2.me/submissions/e50aa8c6-eebf-4d37-8bc2-9335624c7edc

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_07
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea000

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryFractionWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Unreduced fractions stored as Boolean words. Every numerator operation
below runs the literal signed ripple/shift-add code; denominator products
run the literal Boolean multiplication routine. -/

namespace EditApproximation



namespace BinaryFraction







theorem neg_value (a : BinaryFraction) : a.neg.value = -a.value := by
  simp [neg, value, neg_div]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRawOptimizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Complete materialized entropy optimizer on Boolean fraction storage.
Every arithmetic operation invokes the counted Boolean implementation. -/

namespace EditApproximation
namespace BinaryFraction

open Finset



theorem scoredArgmaxWithWork_value {α : Type*} (score : α → BinaryFraction × ℕ) (values : List α) :
    (scoredArgmaxWithWork score values).1 =
      (values.argmax (fun a => (score a).1.value)).map (fun a => (a, (score a).1)) := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
    simp only [scoredArgmaxWithWork, ih, List.argmax_cons]
    cases h : rest.argmax (fun a => (score a).1.value) with
    | none => rfl
    | some best => simp only [Option.map_some, ltWithWork_value]; split_ifs <;> rfl



end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryOnlineInputs
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The actual optimistic linear objective constructed from stored Boolean
fractions, using counted sums, products and divisions. No reduced-rational
conversion is used between the table inputs and the optimizer. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

@[simp] theorem gainWithWork_value {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (s : ℕ) (i : β × σ) :
    (gainWithWork mass table s i).1.value =
      childGain (fun j => (mass j).value) (fun t j => (table t j).value) s i := by
  simp only [gainWithWork, divWithWork_value, neg_value, childGain]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupKernel
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal group estimates on gathered stored fractions. Each child/scale
comparison is executed, the supplied draw indices are reused, and ordered
selection uses the same tie rule as the mathematical group program. -/

namespace EditApproximation
namespace BinaryFraction

open Finset



@[simp] theorem selectGroupWithWork_value {ι : Type*} (members : List ι) (hne : members ≠ [])
    (estimate : ι → BinaryFraction × ℕ) :
    (selectGroupWithWork members hne estimate).1 =
      selectGroupMember members hne (fun member => (estimate member).1.value) := by
  simp only [selectGroupWithWork, scoredArgmaxWithWork_value, neg_value,
    Option.map_map, Function.comp_def, selectGroupMember]
  congr 1
  cases members.argmax (fun member => -(estimate member).1.value) <;> rfl

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCountedGroup
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Group evaluation reads the exact finite sampler indexed by the count
computed from the stored rational scale. Casting indices below is proof
transport only; the emitted natural count is used by the executed loop. -/

namespace EditApproximation
namespace BinaryFraction

theorem groupMemberWithWork_transport {M T : ℕ}
    (scales : Fin T → BinaryFraction) (left right : Fin T → ℕ) (h : ∀ t, left t = right t)
    (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ t, Fin (right t) → Fin M) :
    groupMemberWithWork scales left connection envelope values (fun t j => draw t (Fin.cast (h t) j)) =
      groupMemberWithWork scales right connection envelope values draw := by
  have heq : left = right := funext h
  subst right
  rfl

@[simp] theorem countedGroupMemberWithWork_value {M T : ℕ} (Q b : ℕ) (scales : Fin T → BinaryFraction)
    (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M) :
    (countedGroupMemberWithWork Q b scales connection envelope values draw).1.value =
      groupMemberEstimate (fun t => (scales t).value) (fun t => groupSampleCount M Q b (scales t).value)
        connection.value (fun i => (envelope.get i).value) (fun i => (values.get i).value) draw := by
  unfold countedGroupMemberWithWork
  dsimp only
  rw [groupMemberWithWork_transport]
  exact groupMemberWithWork_value _ _ _ _ _ _

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySampledGroups
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sampled group continuation uses the executed envelopes, rounded
states, exact finite sample counts, and ordered minimizing scan. Its output
is the same physical action as the group program used by the accuracy proof. -/

namespace EditApproximation
namespace BinaryFraction

section Group
variable {α : Type*} (source target : List α) {M T : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ) (hb : 0 < b)
  (tau F : BinaryFraction)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
  (scales : Fin T → BinaryFraction)
  (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)

local notation "Member" => UnskippedBand source target parent b P exponent
  (BinaryFraction.value tau) (BinaryFraction.value F)
  (fun i q => BinaryFraction.value (child i q)) (fun i q => BinaryFraction.value (initial i q))

include hb in
theorem unskippedEstimateWithWork_value (member : Member) :
    (unskippedEstimateWithWork source target parent b P exponent Q tau F child initial current scales draw member).1.value =
      unskippedGroupEstimate (fun t => (scales t).value)
        (fun t => groupSampleCount M Q b (scales t).value)
        (fun i q => (current i q).value) member draw := by
  have hround : (roundedBandWithWork exponent b member.actions member.nonempty initial).1.get =
      member.rounded := roundedBandWithWork_value exponent b member.actions member.nonempty initial hb
  have hmass (i : Fin M) : ((envelopeVectorWithWork b member.actions initial).1.get i).value =
      member.envelope i := envelopeVectorWithWork_value b member.actions initial hb i
  simp only [unskippedEstimateWithWork, countedGroupMemberWithWork_value,
    endpointConnectionWithWork_value, vectorMapWithWork_value, hround, hmass, unskippedGroupEstimate]

include hb in
theorem chooseBinaryUnskippedWithWork_value (members : List Member) (hne : members ≠ []) :
    (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).1 = selectGroupMember members hne (fun member =>
        unskippedGroupEstimate (fun t => (scales t).value)
          (fun t => groupSampleCount M Q b (scales t).value)
          (fun i q => (current i q).value) member draw) := by
  simp only [chooseBinaryUnskippedWithWork, selectGroupWithWork_value,
    unskippedEstimateWithWork_value source target parent b P exponent Q hb tau F child initial current scales draw]

include hb in
theorem sampledGroupActionWithWork_value (members : List Member) (hne : members ≠ []) :
    (sampledGroupActionWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).1.decode =
      (selectGroupMember members hne (fun member =>
        unskippedGroupEstimate (fun t => (scales t).value)
          (fun t => groupSampleCount M Q b (scales t).value)
          (fun i q => (current i q).value) member draw)).rationalAction := by
  let selected : Member := (chooseBinaryUnskippedWithWork source target parent b P exponent Q
    tau F child initial current scales draw members hne).1
  have hround := roundedBandWithWork_value exponent b selected.actions selected.nonempty initial hb
  have haction : (endpointActionWithWork selected.center
      (roundedBandWithWork exponent b selected.actions selected.nonempty initial).1.get).1.decode =
      selected.rationalAction := by
    exact (endpointActionWithWork_decode _ _).trans (congrArg
      (fun states : Fin M → TargetInterval target.length =>
        (⟨selected.center, endpointActionConnection selected.center states, fun i => (i, states i)⟩ :
          PhysicalRationalAction M target.length)) hround)
  exact haction.trans (congrArg UnskippedBand.rationalAction
    (chooseBinaryUnskippedWithWork_value source target parent b P exponent Q hb tau F
      child initial current scales draw members hne))

end Group
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryDyadicSampledGroups
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The generated binary scale list is reindexed into the finite
draw domain. Only proof transport is used: the accepted draw count is the
same natural computed by `groupSampleCountWithWork`. -/

namespace EditApproximation
namespace BinaryFraction



theorem unskippedEstimate_scale_transport {α : Type*} {source target : List α} {M T : ℕ}
    {parent : TargetInterval source.length} {b P exponent Q : ℕ} {tau F : ℚ}
    {child initial : Fin M → TargetInterval target.length → ℚ}
    (left right : Fin T → ℚ) (h : left = right)
    (current : Fin M → TargetInterval target.length → ℚ)
    (member : UnskippedBand source target parent b P exponent tau F child initial)
    (draw : ∀ t, Fin (groupSampleCount M Q b (right t)) → Fin M) :
    unskippedGroupEstimate left (fun t => groupSampleCount M Q b (left t)) current member
      (fun t j => draw t (Fin.cast (congrArg (groupSampleCount M Q b) (congrFun h t)) j)) =
      unskippedGroupEstimate right (fun t => groupSampleCount M Q b (right t)) current member draw := by
  cases h
  rfl

section Physical
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ)
  (tau F : BinaryFraction)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
  (raw : List BinaryFraction) (hraw : raw.map value = groupDyadicScales M b F.value)
  (draw : ∀ t : Fin (groupDyadicScales M b F.value).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F.value t)) → Fin M)

local notation "Member" => UnskippedBand source target parent b P exponent
  (BinaryFraction.value tau) (BinaryFraction.value F)
  (fun i q => BinaryFraction.value (child i q)) (fun i q => BinaryFraction.value (initial i q))

theorem dyadicSampledGroupActionWithWork_value (members : List Member) (hne : members ≠ [])
    (hb : 0 < b) :
    (dyadicSampledGroupActionWithWork source target parent b P exponent Q tau F child initial current
      raw hraw draw members hne).1.decode =
      (chooseUnskippedGroup Q (fun i q => (current i q).value) members hne draw).rationalAction := by
  unfold dyadicSampledGroupActionWithWork
  rw [sampledGroupActionWithWork_value source target parent b P exponent Q hb]
  unfold chooseUnskippedGroup dyadicUnskippedGroupEstimate
  congr 2
  funext member
  exact unskippedEstimate_scale_transport _ _
    (funext (indexedGroupScales_value raw M b F.value hraw)) _ member draw

end Physical
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCellGroupKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One complete whole-cell group: enumerate its eligible centers, execute
every band guard, estimate all surviving members with the original finite
draws, and select the same ordered minimum. -/

namespace EditApproximation
namespace BinaryFraction

theorem cellReferenceAction_transport {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (tau a f g : ℚ) (h : f = g)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial current : Fin M → TargetInterval target.length → ℚ)
    (cell : ℕ × ℕ) (draw : cellScaleDraw M b Q f) :
    cellReferenceAction source target parent b P F exponent Q tau a f parentInitial child initial current cell draw =
      cellReferenceAction source target parent b P F exponent Q tau a g parentInitial child initial current cell
        (Eq.mp (congrArg (cellScaleDraw M b Q) h) draw) := by
  cases h
  rfl

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryReadComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Callback work is retained when a finite loop is supplied with a
costed reader. These lemmas compare the literal loop counters, so a
lookup cannot disappear when its returned word is passed to arithmetic. -/

namespace EditApproximation

theorem sum_map_le_length_mul {α : Type*} (xs : List α) (f : α → ℕ) (C : ℕ)
    (h : ∀ x ∈ xs, f x ≤ C) : (xs.map f).sum ≤ xs.length * C := by
  induction xs with
  | nil => simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.zero_mul, le_refl]
  | cons x xs ih =>
    have hh := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem filterWithWork_length_le_cost {α : Type*} (test : α → Bool × ℕ) (xs : List α) :
    xs.length ≤ (filterWithWork test xs).2 := by
  induction xs with
  | nil => simp only [List.length_nil, Nat.zero_le]
  | cons x xs ih => simp only [List.length_cons, filterWithWork]; omega

theorem filterWithWork_add_read {α : Type*} (test : α → Bool × ℕ)
    (readCost : α → ℕ) (xs : List α) (R : ℕ) (hR : ∀ x ∈ xs, readCost x ≤ R) :
    (filterWithWork (fun x => ((test x).1, (test x).2 + readCost x)) xs).1 =
      (filterWithWork test xs).1 ∧
    (filterWithWork (fun x => ((test x).1, (test x).2 + readCost x)) xs).2 ≤
      (filterWithWork test xs).2 * (R + 1) := by
  have h := filterWithWork_extra (fun x => ((test x).1, (test x).2 + readCost x))
    test readCost xs (fun _ _ => rfl) (fun _ _ => le_rfl)
  have hs := sum_map_le_length_mul xs readCost R hR
  have hl := filterWithWork_length_le_cost test xs
  refine ⟨h.1, ?_⟩
  nlinarith only [h.2, hs, hl]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Group estimates and the ordered minimizing scan retain finite-table
lookup costs, using Fin-indexed source arrays. -/

namespace EditApproximation
namespace BinaryFraction

theorem scoredArgmaxWithWork_extra {α : Type*} (read plain : α → BinaryFraction × ℕ)
    (extra : α → ℕ) (xs : List α)
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 + extra x) :
    (scoredArgmaxWithWork read xs).1 = (scoredArgmaxWithWork plain xs).1 ∧
    (scoredArgmaxWithWork read xs).2 ≤
      (scoredArgmaxWithWork plain xs).2 + (xs.map extra).sum := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [scoredArgmaxWithWork, List.map_nil, List.sum_nil,
      Nat.add_zero, le_refl]⟩
  | cons x xs ih =>
    have hx := hv x List.mem_cons_self
    have hcx := hc x List.mem_cons_self
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    simp only [scoredArgmaxWithWork, ht.1, hx, List.map_cons, List.sum_cons]
    cases (scoredArgmaxWithWork plain xs).1 with
    | none => exact ⟨rfl, by dsimp only; omega⟩
    | some best => exact ⟨rfl, by dsimp only; omega⟩

theorem selectGroupWithWork_extra {α : Type*} (read plain : α → BinaryFraction × ℕ)
    (extra : α → ℕ) (xs : List α) (hne : xs ≠ [])
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 + extra x) :
    (selectGroupWithWork xs hne read).1 = (selectGroupWithWork xs hne plain).1 ∧
    (selectGroupWithWork xs hne read).2 ≤
      (selectGroupWithWork xs hne plain).2 + (xs.map extra).sum := by
  have h := scoredArgmaxWithWork_extra
    (fun x => ((read x).1.neg, (read x).2 + 1))
    (fun x => ((plain x).1.neg, (plain x).2 + 1)) extra xs
    (fun x hx => by rw [hv x hx]) (fun x hx => by have := hc x hx; omega)
  unfold selectGroupWithWork
  dsimp only
  rw [h.1]
  exact ⟨rfl, by omega⟩

section Group
variable {α : Type*} (source target : List α) {M T : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ)
  (tau F : BinaryFraction)
  (child : Fin M → TargetInterval target.length → BinaryFraction)
  (initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (scales : Fin T → BinaryFraction)
  (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)

local notation "Member" => UnskippedBand source target parent b P exponent
  (BinaryFraction.value tau) (BinaryFraction.value F)
  (fun i q => BinaryFraction.value (child i q))
  (fun i q => BinaryFraction.value (Prod.fst (initial i q)))

theorem unskippedEstimateReadWithWork_eq_cost (member : Member) (R C : ℕ)
    (hi : ∀ i q, (initial i q).2 ≤ C) (hr : ∀ i q, (current i q).2 ≤ R) :
    (unskippedEstimateReadWithWork source target parent b P exponent Q tau F child initial current
      scales draw member).1 =
      (unskippedEstimateWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw member).1 ∧
    (unskippedEstimateReadWithWork source target parent b P exponent Q tau F child initial current
      scales draw member).2 ≤
      (unskippedEstimateWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw member).2 +
      M * (member.actions.length * (C + 3)) + M * (member.actions.length * (C + 3)) + M * R := by
  have hm := envelopeVectorReadWithWork_eq_cost b member.actions initial C hi
  have hp := roundedBandReadWithWork_eq_cost exponent b member.actions member.nonempty initial C hi
  have hv := vectorMapWithWork_extra M
    (fun i => current i ((roundedBandWithWork exponent b member.actions member.nonempty
      (fun j q => (initial j q).1)).1.get i))
    (fun i => ((current i ((roundedBandWithWork exponent b member.actions member.nonempty
      (fun j q => (initial j q).1)).1.get i)).1, 1)) R (fun _ => rfl)
    (fun i => by have := hr i ((roundedBandWithWork exponent b member.actions member.nonempty
      (fun j q => (initial j q).1)).1.get i); omega)
  unfold unskippedEstimateReadWithWork unskippedEstimateWithWork
  dsimp only
  rw [hm.1, hp.1, hv.1]
  exact ⟨rfl, by omega⟩

theorem chooseUnskippedReadWithWork_eq_cost (members : List Member) (hne : members ≠ []) (R C : ℕ)
    (hi : ∀ i q, (initial i q).2 ≤ C) (hr : ∀ i q, (current i q).2 ≤ R) :
    (chooseUnskippedReadWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).1 =
      (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).1 ∧
    (chooseUnskippedReadWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).2 ≤
      (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).2 +
      (members.map fun member => M * (member.actions.length * (C + 3)) +
        M * (member.actions.length * (C + 3)) + M * R).sum := by
  exact selectGroupWithWork_extra _ _ _ members hne
    (fun member _ => (unskippedEstimateReadWithWork_eq_cost source target parent b P exponent Q
      tau F child initial current scales draw member R C hi hr).1)
    (fun member _ => by
      simpa only [Nat.add_assoc] using
        (unskippedEstimateReadWithWork_eq_cost source target parent b P exponent Q
          tau F child initial current scales draw member R C hi hr).2)

end Group
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupActionReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected group action uses the same minimizing member and rounded
endpoints, while charging both the initial and current-table readers. -/

namespace EditApproximation
namespace BinaryFraction

section Group
variable {α : Type*} (source target : List α) {M T : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ)
  (tau F : BinaryFraction)
  (child : Fin M → TargetInterval target.length → BinaryFraction)
  (initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (scales : Fin T → BinaryFraction)
  (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)

local notation "Member" => UnskippedBand source target parent b P exponent
  (BinaryFraction.value tau) (BinaryFraction.value F)
  (fun i q => BinaryFraction.value (child i q))
  (fun i q => BinaryFraction.value (Prod.fst (initial i q)))

theorem sampledGroupActionReadWithWork_eq_cost (members : List Member) (hne : members ≠ []) (R C : ℕ)
    (hi : ∀ i q, (initial i q).2 ≤ C) (hr : ∀ i q, (current i q).2 ≤ R) :
    (sampledGroupActionReadWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).1 =
      (sampledGroupActionWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).1 ∧
    (sampledGroupActionReadWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).2 ≤
      (sampledGroupActionWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).2 +
      (members.map fun member => M * (member.actions.length * (C + 3)) +
        M * (member.actions.length * (C + 3)) + M * R).sum +
      M * (((chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).1.actions).length *
        (C + 3)) := by
  have hs := chooseUnskippedReadWithWork_eq_cost source target parent b P exponent Q tau F
    child initial current scales draw members hne R C hi hr
  have hp := roundedBandReadWithWork_eq_cost exponent b
    (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child
      (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).1.actions
    (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child
      (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).1.nonempty initial C hi
  unfold sampledGroupActionReadWithWork sampledGroupActionWithWork
  dsimp only
  simp only [hs.1, hp.1]
  exact ⟨trivial, by omega⟩

end Group

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedCellGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Whole-cell selection with the prepared-grid band constructor. -/

namespace EditApproximation
namespace BinaryFraction

section Cell
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (hb : 0 < b)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
  (raw : List BinaryFraction)
  (hraw : raw.map value = groupDyadicScales M b (nat F).value)
  (draw : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → Fin M)

theorem preparedCellGroupWithWork_reference (cell : ℕ × ℕ) (hP : 0 < P) :
    ((preparedCellGroupWithWork source target parent b P F exponent Q hb tau a parentInitial child initial current
      raw hraw draw hP cell).1.map BinaryBellmanAction.decode) =
      cellReferenceAction source target parent b P F exponent Q tau.value a.value (nat F).value
        (fun q => (parentInitial q).value) (fun i q => (child i q).value)
        (fun i q => (initial i q).value) (fun i q => (current i q).value) cell draw := by
  have hcenters := cellCentersWithWork_value P F b a (inversePowerTwo exponent) parentInitial cell hP
  simp only [inversePowerTwo_value] at hcenters
  have hmembers : (filterMapWithWork
      (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau (nat F) child initial)
      (cellCentersWithWork P F b a (inversePowerTwo exponent) parentInitial cell).1).1 =
      unskippedBandList source target parent b P exponent tau.value (nat F).value
        (fun i q => (child i q).value) (fun i q => (initial i q).value)
        (cellRepresentativeStates target.length P F b a.value
          (fun q => (parentInitial q).value) ((2 : ℚ) ^ (-(exponent : ℤ))) cell) := by
    simp only [filterMapWithWork_value, preparedUnskippedCandidateWithWork_value, hcenters, unskippedBandList]
  unfold preparedCellGroupWithWork
  dsimp only
  split_ifs with hempty
  · have hnil := hempty
    rw [hmembers] at hnil
    simp only [Option.map_none, cellReferenceAction, dite_eq_left hnil]
  · rw [Option.map_some, dyadicSampledGroupActionWithWork_value source target parent b P exponent Q
      tau (nat F) child initial current raw hraw draw _ hempty hb]
    have hnonempty := hempty
    rw [hmembers] at hnonempty
    simp only [hmembers, cellReferenceAction, dite_eq_right hnonempty]

/-- The rational cell-group program at the exact natural parameter.
Transport preserves its values and changes only proof indices. -/
theorem preparedCellGroupWithWork_value (cell : ℕ × ℕ) (hP : 0 < P) :
    ((preparedCellGroupWithWork source target parent b P F exponent Q hb tau a parentInitial child initial current
      raw hraw draw hP cell).1.map BinaryBellmanAction.decode) =
      chooseCellGroupAction source target parent b P F exponent Q tau.value a.value
        (fun q => (parentInitial q).value) (fun i q => (child i q).value)
        (fun i q => (initial i q).value) (fun i q => (current i q).value) cell
        (Eq.mp (congrArg (cellScaleDraw M b Q) (nat_value F)) draw) := by
  exact (preparedCellGroupWithWork_reference source target parent b P F exponent Q hb tau a parentInitial
    child initial current raw hraw draw cell hP).trans
      (cellReferenceAction_transport source target parent b P F exponent Q tau.value a.value _ _
        (nat_value F) _ _ _ _ cell draw)

end Cell
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryUnskippedReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The accepted-band record is built from the reader-aware tests.
Only proof fields are erased; numerical tests and reads remain charged. -/

namespace EditApproximation
namespace BinaryFraction

theorem preparedUnskippedReadWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau F : BinaryFraction)
    (read initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (R C : ℕ) (hr : ∀ i q, (read i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ C)
    (center : TargetInterval target.length) :
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau F read initial R C hr hi center).1 =
      (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau F
        (fun i q => (read i q).1) (fun i q => (initial i q).1) center).1 := by
  have hband := (preparedRepresentativeReadWithWork_eq_cost parent center (parent.hi - parent.lo)
    b P tau (inversePowerTwo exponent) read R hr).1
  unfold preparedUnskippedReadWithWork preparedUnskippedCandidateWithWork
  dsimp only
  simp only [hband]
  split_ifs with hempty hguard
  · rfl
  · rfl
  · rename_i hplain
    have hg := (unskippedGuardReadWithWork_eq_cost parent center b exponent F _ ((wideActionGridWithWork M parent center b P).1.map Vector.get) hempty initial C hi).1
    exact False.elim (hplain (hg.symm.trans hguard))
  · rename_i hplain
    have hg := (unskippedGuardReadWithWork_eq_cost parent center b exponent F _ ((wideActionGridWithWork M parent center b P).1.map Vector.get) hempty initial C hi).1
    exact False.elim (hguard (hg.trans hplain))
  · rfl


end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCellReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Reader-aware whole-cell construction. Every eligibility test reads its
initial word, and every accepted band and selected action uses the counted
reader kernels. -/

namespace EditApproximation

namespace BinaryFraction



theorem cellCentersReadWithWork_eq_cost {n : ℕ} (P F b : ℕ) (a theta : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction × ℕ) (cell : ℕ × ℕ)
    (R : ℕ) (hr : ∀ r, (initial r).2 ≤ R) :
    (cellCentersReadWithWork P F b a theta initial cell).1 =
      (cellCentersWithWork P F b a theta (fun r => (initial r).1) cell).1 ∧
    (cellCentersReadWithWork P F b a theta initial cell).2 ≤
      (cellCentersWithWork P F b a theta (fun r => (initial r).1) cell).2 * (R + 1) := by
  have hs := filterWithWork_add_read
    (fun r => centerEligibilityWithWork b F a (initial r).1) (fun r => (initial r).2)
    (cellStatesWithWork n (bitWordValue (seedGridSpacingWithWork b P).1)
      (canonicalMulWithWork theta (nat b)).1 cell).1 R (fun r _ => hr r)
  unfold cellCentersReadWithWork cellCentersWithWork
  dsimp only
  have he : (fun r => let word := initial r; let tested := centerEligibilityWithWork b F a word.1;
      (tested.1, word.2 + tested.2)) =
      (fun r => ((centerEligibilityWithWork b F a (initial r).1).1,
        (centerEligibilityWithWork b F a (initial r).1).2 + (initial r).2)) := by
    funext r
    simp only [Nat.add_comm]
  rw [he, hs.1]
  exact ⟨rfl, by nlinarith only [hs.2]⟩

section Cell
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (hb : 0 < b) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R C : ℕ) (hr : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ C)
  (raw : List BinaryFraction) (hraw : raw.map value = groupDyadicScales M b (nat F).value)
  (draw : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → Fin M)

theorem preparedCellGroupReadWithWork_eq (cell : ℕ × ℕ) (Rp Rc : ℕ)
    (hp : ∀ r, (parentInitial r).2 ≤ Rp) (hc : ∀ i q, (current i q).2 ≤ Rc) :
    (preparedCellGroupReadWithWork source target parent b P F exponent Q hb hP tau a
      parentInitial child initial current R C hr hi raw hraw draw cell).1 =
    (preparedCellGroupWithWork source target parent b P F exponent Q hb tau a
      (fun r => (parentInitial r).1) (fun i q => (child i q).1)
      (fun i q => (initial i q).1) (fun i q => (current i q).1) raw hraw draw hP cell).1 := by
  have hcenters := (cellCentersReadWithWork_eq_cost P F b a (inversePowerTwo exponent)
    parentInitial cell Rp hp).1
  have hm : (filterMapWithWork
      (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
        child initial R C hr hi)
      (cellCentersWithWork P F b a (inversePowerTwo exponent) (fun r => (parentInitial r).1) cell).1).1 =
    (filterMapWithWork
      (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau (nat F)
        (fun i q => (child i q).1) (fun i q => (initial i q).1))
      (cellCentersWithWork P F b a (inversePowerTwo exponent) (fun r => (parentInitial r).1) cell).1).1 := by
    simp only [filterMapWithWork_value, preparedUnskippedReadWithWork_value]
  unfold preparedCellGroupReadWithWork preparedCellGroupWithWork
  dsimp only
  simp only [hcenters, hm]
  split_ifs with hempty
  · rfl
  · apply congrArg some
    exact (sampledGroupActionReadWithWork_eq_cost source target parent b P exponent Q tau (nat F)
      (fun i q => (child i q).1) initial current _ _ _ hempty Rc C hi hc).1

end Cell
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupSourcePort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Exact finite-count source reads inside a sampled group estimator.
A source read is executed only in the sampled branch; an exact scale
uses the complete child array and makes no random-source lookup. -/

namespace EditApproximation.BinaryFraction



theorem groupScaleSourceWithWork_value {M : ℕ} (k : ℕ) (h : BinaryFraction)
    (envelope values : Vector BinaryFraction M) (draw : Fin k → Fin M × ℕ) :
    (groupScaleSourceWithWork k h envelope values draw).1 =
      (groupScaleWithWork k h envelope values (fun i => (draw i).1)).1 := by
  unfold groupScaleSourceWithWork groupScaleWithWork
  split_ifs <;> simp only [arithmeticMapWithWork_value]

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupMemberSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

namespace BinaryFraction



theorem groupMemberSourceWithWork_value {M T : ℕ} (scales : Fin T → BinaryFraction)
    (count : Fin T → ℕ) (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ s : Fin T, Fin (count s) → Fin M × ℕ) :
    (groupMemberSourceWithWork scales count connection envelope values draw).1 =
      (groupMemberWithWork scales count connection envelope values (fun s i => (draw s i).1)).1 := by
  simp only [groupMemberSourceWithWork, groupMemberWithWork, arithmeticMapWithWork_value,
    groupScaleSourceWithWork_value]

theorem countedGroupMemberSourceWithWork_value {M T : ℕ} (Q b : ℕ)
    (scales : Fin T → BinaryFraction) (connection : BinaryFraction)
    (envelope values : Vector BinaryFraction M)
    (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M × ℕ) :
    (countedGroupMemberSourceWithWork Q b scales connection envelope values draw).1 =
      (countedGroupMemberWithWork Q b scales connection envelope values (fun t i => (draw t i).1)).1 := by
  let counts := vectorMapWithWork T fun t => groupSampleCountWithWork M Q b (scales t)
  let count := fun t => bitWordValue (counts.1.get t)
  have heq : ∀ t, count t = groupSampleCount M Q b (scales t).value := by
    intro t
    simp only [count, counts, vectorMapWithWork_value, groupSampleCountWithWork_value]
  exact groupMemberSourceWithWork_value scales count connection envelope values
    (fun t j => draw t (Fin.cast (heq t) j))

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySampledSourcePort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Table-reader and random-source costs are retained together through
member estimation, tie-broken selection, and rounded action return. -/

namespace EditApproximation.BinaryFraction

section Group
variable {α : Type*} (source target : List α) {M T : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ)
  (tau F : BinaryFraction)
  (child : Fin M → TargetInterval target.length → BinaryFraction)
  (initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (scales : Fin T → BinaryFraction)
  (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M × ℕ)

local notation "Member" => UnskippedBand source target parent b P exponent (value tau) (value F)
  (fun i q => value (child i q)) (fun i q => value (Prod.fst (initial i q)))

theorem unskippedEstimateSourceWithWork_value (member : Member) :
    (unskippedEstimateSourceWithWork source target parent b P exponent Q tau F child initial current
      scales draw member).1 =
      (unskippedEstimateReadWithWork source target parent b P exponent Q tau F child initial current
        scales (fun s i => (draw s i).1) member).1 := by
  exact countedGroupMemberSourceWithWork_value Q b scales _ _ _ draw

theorem chooseUnskippedSourceWithWork_value (members : List Member) (hne : members ≠ []) :
    (chooseUnskippedSourceWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).1 =
      (chooseUnskippedReadWithWork source target parent b P exponent Q tau F child initial current
        scales (fun s i => (draw s i).1) members hne).1 := by
  simp only [chooseUnskippedSourceWithWork, chooseUnskippedReadWithWork, selectGroupWithWork_value]
  congr 1
  funext member
  rw [unskippedEstimateSourceWithWork_value]


theorem sampledGroupActionSourceWithWork_value (members : List Member) (hne : members ≠ []) :
    (sampledGroupActionSourceWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).1 =
      (sampledGroupActionReadWithWork source target parent b P exponent Q tau F child initial current
        scales (fun s i => (draw s i).1) members hne).1 := by
  let finish := fun selected : Member =>
    let rounded := roundedBandReadWithWork exponent b selected.actions selected.nonempty initial
    (endpointActionWithWork selected.center rounded.1.get).1
  change finish (chooseUnskippedSourceWithWork source target parent b P exponent Q tau F
      child initial current scales draw members hne).1 =
      finish (chooseUnskippedReadWithWork source target parent b P exponent Q tau F
        child initial current scales (fun s i => (draw s i).1) members hne).1
  exact congrArg finish (chooseUnskippedSourceWithWork_value source target parent b P exponent Q
    tau F child initial current scales draw members hne)


end Group
end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCellSourcePort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

section Cell
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (hb : 0 < b) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R C : ℕ) (hr : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ C)
  (raw : List BinaryFraction) (hraw : raw.map value = groupDyadicScales M b (nat F).value)
  (draw : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → Fin M × ℕ)

theorem preparedCellGroupSourceWithWork_value (cell : ℕ × ℕ) :
    (preparedCellGroupSourceWithWork source target parent b P F exponent Q hb hP tau a
      parentInitial child initial current R C hr hi raw hraw draw cell).1 =
      (preparedCellGroupReadWithWork source target parent b P F exponent Q hb hP tau a
        parentInitial child initial current R C hr hi raw hraw (fun t i => (draw t i).1) cell).1 := by
  unfold preparedCellGroupSourceWithWork preparedCellGroupReadWithWork
  dsimp only
  split_ifs with hempty
  · rfl
  · apply congrArg some
    exact sampledGroupActionSourceWithWork_value source target parent b P exponent Q tau (nat F)
      (fun i q => (child i q).1) initial current (indexedGroupScales raw M b (nat F).value hraw)
      (fun t j => draw t (Fin.cast (congrArg (groupSampleCount M Q b)
        (indexedGroupScales_value raw M b (nat F).value hraw t)) j)) _ hempty

end Cell
end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGatheredValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Finite stored-word tables for gathered earlier values. The lookup scan
and the construction of every gathered warmup mean are explicit. -/

namespace EditApproximation
namespace BinaryFraction



theorem gatheredWordLookupWithWork_value {κ : Type*} [DecidableEq κ]
    (equal : κ → κ → Bool × ℕ) (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (keys : List κ) (values : List BinaryFraction) (query : κ) :
    (gatheredWordLookupWithWork equal keys values query).1.value =
      finiteAnswerTable keys (values.map BinaryFraction.value) query := by
  induction keys generalizing values with
  | nil => simp only [gatheredWordLookupWithWork, finiteAnswerTable, nat_value, Nat.cast_zero]
  | cons key keys ih =>
    cases values with
    | nil => simp only [gatheredWordLookupWithWork, List.map_nil, finiteAnswerTable, nat_value, Nat.cast_zero]
    | cons value values =>
      simp only [gatheredWordLookupWithWork, List.map_cons, finiteAnswerTable]
      by_cases h : query = key
      · rw [ite_eq_left ((heq query key).mpr h), ite_eq_left h]
      · rw [ite_eq_right (fun hx => h ((heq query key).mp hx)), ite_eq_right h]
        exact ih values

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedComputedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cell kernel constructs its rational scales from the dyadic
parameter exponents. -/

namespace EditApproximation
namespace BinaryFraction

theorem preparedComputedCellGroupWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F exponent Q eM eb eF : ℕ)
    (hM : M = 2 ^ eM) (hb : b = 2 ^ eb) (hF : F = 2 ^ eF)
    (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : cellScaleDraw M b Q (nat F).value) (cell : ℕ × ℕ) (hP : 0 < P) :
    ((preparedComputedCellGroupWithWork source target parent b P F exponent Q eM eb eF hM hb hF hP tau a
      parentInitial child initial current draw cell).1.map BinaryBellmanAction.decode) =
      chooseCellGroupAction source target parent b P F exponent Q tau.value a.value
        (fun q => (parentInitial q).value) (fun i q => (child i q).value)
        (fun i q => (initial i q).value) (fun i q => (current i q).value) cell
        (Eq.mp (congrArg (cellScaleDraw M b Q) (nat_value F)) draw) := by
  have h := preparedCellGroupWithWork_value source target parent b P F exponent Q
    (by rw [hb]; exact Nat.two_pow_pos eb) tau a parentInitial child initial current
    (groupScalesWithWork eM eb eF).1 (computedGroupScales_value M b F eM eb eF hM hb hF)
    draw cell hP
  simpa only [preparedComputedCellGroupWithWork] using h

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedLocalGroups
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Whole-cell query groups with fully constructed endpoint grids. -/

namespace EditApproximation
namespace BinaryFraction

private theorem prepared_cellDraw_roundtrip (M b Q : ℕ) (f g : ℚ) (h : f = g)
    (draw : cellScaleDraw M b Q g) :
    Eq.mp (congrArg (cellScaleDraw M b Q) h)
      (Eq.mpr (congrArg (cellScaleDraw M b Q) h) draw) = draw := by
  cases h
  rfl

theorem preparedLocalGroupScaleWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent Q eM eF eb : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P) (tau a : BinaryFraction)
    (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length) :
    ((preparedLocalGroupScaleWithWork source target parent P F exponent Q eM eF eb hM hF hP tau a
      parentInitial child initial current draw query).1.map BinaryBellmanAction.decode) =
      (localTargetCells (((2 : ℚ) ^ (-(exponent : ℤ))) * (2 ^ eb : ℕ))
        ⌈(parentInitial query).value⌉₊ query).filterMap (fun cell =>
        chooseCellGroupAction source target parent (2 ^ eb) P F exponent Q tau.value a.value
          (fun r => (parentInitial r).value) (fun i r => (child i r).value)
          (fun i r => (initial i r).value) (fun i r => (current i r).value) cell (draw (2 ^ eb) cell)) := by
  simp only [preparedLocalGroupScaleWithWork, filterMapWithWork_value, List.map_filterMap,
    targetCellsWithWork_value, canonicalMulWithWork_value, inversePowerTwo_value, nat_value,
    naturalCeilingWithWork_value]
  apply List.filterMap_congr
  intro cell _
  have hv := preparedComputedCellGroupWithWork_value source target parent (2 ^ eb) P F exponent Q eM eb eF
      hM rfl hF tau a parentInitial child initial current
      (Eq.mpr (congrArg (cellScaleDraw M (2 ^ eb) Q) (nat_value F)) (draw (2 ^ eb) cell)) cell hP
  rw [prepared_cellDraw_roundtrip M (2 ^ eb) Q (nat F).value (F : ℚ) (nat_value F)
    (draw (2 ^ eb) cell)] at hv
  exact hv

private theorem flatMap_filter_condition_p1 {α β : Type*} (p : α → Bool) (f : α → List β)
    (xs : List α) :
    xs.flatMap (fun x => if p x then f x else []) = (xs.filter p).flatMap f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.filter_cons]
    cases p x <;> simp only [Bool.false_eq_true, ↓reduceIte, List.flatMap_cons,
      List.nil_append, ih]

theorem preparedLocalCellGroupsWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q eM eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P) (tau a : BinaryFraction)
    (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length) :
    ((preparedLocalCellGroupsWithWork source target parent N P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current draw query).1.map BinaryBellmanAction.decode) =
      localCellGroupActions source target parent N P F exponent Q tau.value a.value
        (fun r => (parentInitial r).value) (fun i r => (child i r).value)
        (fun i r => (initial i r).value) (fun i r => (current i r).value) draw query := by
  let predicate := fun b : ℕ => decide ((parentInitial query).value / (16 * (F : ℚ)) ≤ b ∧
    (b : ℚ) ≤ 8 * a.value * (parentInitial query).value)
  let values := fun b : ℕ => (localTargetCells (((2 : ℚ) ^ (-(exponent : ℤ))) * b)
    ⌈(parentInitial query).value⌉₊ query).filterMap (fun cell =>
      chooseCellGroupAction source target parent b P F exponent Q tau.value a.value
        (fun r => (parentInitial r).value) (fun i r => (child i r).value)
        (fun i r => (initial i r).value) (fun i r => (current i r).value) cell (draw b cell))
  have hscale : (List.range (max 1 N.bits.length)).map (fun eb => 2 ^ eb) = dyadicScales N := by
    simpa only [dyadicScalesWithWork, arithmeticMapWithWork_value, powerTwoWord_value] using
      dyadicScalesWithWork_value N
  have hguard (eb : ℕ) : (refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query)).1 =
      predicate (2 ^ eb) := Bool.eq_iff_iff.mpr (by
        simp only [refinementScaleGuardWithWork_value, predicate, decide_eq_true_eq])
  unfold preparedLocalCellGroupsWithWork
  simp only [arithmeticFlatMapWithWork_value, List.map_flatMap]
  trans (List.range (max 1 N.bits.length)).flatMap
    (fun eb => if predicate (2 ^ eb) then values (2 ^ eb) else [])
  · apply List.flatMap_congr
    intro eb _
    by_cases hg : (refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query)).1 = true
    · have hp : predicate (2 ^ eb) = true := (hguard eb) ▸ hg
      simp only [ite_eq_left hg, ite_eq_left hp]
      exact preparedLocalGroupScaleWithWork_value source target parent P F exponent Q eM eF eb hM hF hP
        tau a parentInitial child initial current draw query
    · have hp : predicate (2 ^ eb) ≠ true := by simpa only [← hguard eb] using hg
      simp only [ite_eq_right hg, ite_eq_right hp, List.map_nil]
  · calc
      _ = ((List.range (max 1 N.bits.length)).map (fun eb => 2 ^ eb)).flatMap
          (fun b => if predicate b then values b else []) :=
        (List.flatMap_map _ _ _).symm
      _ = (((List.range (max 1 N.bits.length)).map (fun eb => 2 ^ eb)).filter predicate).flatMap
          values := flatMap_filter_condition_p1 _ _ _
      _ = _ := by rw [hscale]; rfl

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalReadValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Value preservation of local data readers does not require a chosen
work cap for arbitrary answer tables. Finite bounds used below exist only
inside these proofs and are never constructed by the algorithm. -/

namespace EditApproximation.BinaryFraction

private theorem finite_work_bound {ι : Type*} [Fintype ι] (work : ι → ℕ) :
    ∃ R, ∀ i, work i ≤ R := by
  classical
  exact ⟨∑ i, work i, fun i => Finset.single_le_sum (f := work) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)⟩

section Group
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ)
  (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)

theorem preparedComputedCellReadWithWork_value_only (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : cellScaleDraw M b Q (nat F).value) (cell : ℕ × ℕ) :
    (preparedComputedCellReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb hb draw cell).1 =
    (preparedComputedCellGroupWithWork source target parent b P F exponent Q eM eb eF hM hb hF hP
      tau a (fun r => (parentInitial r).1) (fun i q => (child i q).1)
      (fun i q => (initial i q).1) (fun i q => (current i q).1) draw cell).1 := by
  classical
  obtain ⟨Rp, hp⟩ := finite_work_bound (fun r => (parentInitial r).2)
  obtain ⟨Rc, hcur⟩ := finite_work_bound (fun iq : Fin M × TargetInterval target.length =>
    (current iq.1 iq.2).2)
  have h := preparedCellGroupReadWithWork_eq source target parent b P F exponent Q
    (by rw [hb]; exact Nat.two_pow_pos eb) hP tau a parentInitial child initial current
    R R hc hi (groupScalesWithWork eM eb eF).1
    (computedGroupScales_value M b F eM eb eF hM hb hF) draw cell Rp Rc hp
    (fun i q => hcur (i, q))
  simpa only [preparedComputedCellReadWithWork, preparedComputedCellGroupWithWork] using h

theorem preparedLocalGroupScaleReadWithWork_value_only (eb : ℕ)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length) :
    (preparedLocalGroupScaleReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi eb draw query).1 =
    (preparedLocalGroupScaleWithWork source target parent P F exponent Q eM eF eb hM hF hP tau a
      (fun r => (parentInitial r).1) (fun i q => (child i q).1)
      (fun i q => (initial i q).1) (fun i q => (current i q).1) draw query).1 := by
  simp only [preparedLocalGroupScaleReadWithWork, preparedLocalGroupScaleWithWork,
    filterMapWithWork_value]
  apply List.filterMap_congr
  intro cell _
  have h := preparedComputedCellReadWithWork_value_only source target parent P F exponent Q eM eF
    hM hF hP tau a parentInitial child initial current R hc hi (2 ^ eb) eb rfl
    (Eq.mpr (congrArg (cellScaleDraw M (2 ^ eb) Q) (nat_value F)) (draw (2 ^ eb) cell)) cell
  simpa only using h

theorem preparedLocalCellGroupsReadWithWork_value_only (N : ℕ)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length) :
    (preparedLocalCellGroupsReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi N draw query).1 =
    (preparedLocalCellGroupsWithWork source target parent N P F exponent Q eM eF hM hF hP tau a
      (fun r => (parentInitial r).1) (fun i q => (child i q).1)
      (fun i q => (initial i q).1) (fun i q => (current i q).1) draw query).1 := by
  simp only [preparedLocalCellGroupsReadWithWork, preparedLocalCellGroupsWithWork,
    arithmeticFlatMapWithWork_value]
  apply List.flatMap_congr
  intro eb _
  split_ifs
  · have h := preparedLocalGroupScaleReadWithWork_value_only source target parent P F exponent Q eM eF
      hM hF hP tau a parentInitial child initial current R hc hi eb draw query
    simpa only using h
  · rfl
end Group

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalSourceValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact local source-port values for arbitrary gathered answer lists.
No cost bound on unqueried coordinates enters these identities. -/

namespace EditApproximation

private theorem sourceDraw_project_cast (M b Q : ℕ) (f g : ℚ) (h : f = g)
    (draw : cellScaleReadDraw M b Q g) :
    (fun t i => ((Eq.mpr (congrArg (cellScaleReadDraw M b Q) h) draw) t i).1) =
      Eq.mpr (congrArg (BinaryFraction.cellScaleDraw M b Q) h) (fun t i => (draw t i).1) := by
  cases h
  rfl

namespace BinaryFraction
section Group
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ)
  (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)

theorem preparedComputedCellSourceWithWork_value (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : cellScaleReadDraw M b Q (nat F).value) (cell : ℕ × ℕ) :
    (preparedComputedCellSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb hb draw cell).1 =
      (preparedComputedCellReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi b eb hb (fun t i => (draw t i).1) cell).1 := by
  have h := preparedCellGroupSourceWithWork_value source target parent b P F exponent Q
    (by rw [hb]; exact Nat.two_pow_pos eb) hP tau a parentInitial child initial current R R hc hi
    (groupScalesWithWork eM eb eF).1 (computedGroupScales_value M b F eM eb eF hM hb hF) draw cell
  simpa only [preparedComputedCellSourceWithWork, preparedComputedCellReadWithWork] using h

private theorem computedCellSource_cast_value (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : cellScaleReadDraw M b Q F) (cell : ℕ × ℕ) :
    (preparedComputedCellSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb hb
      (Eq.mpr (congrArg (cellScaleReadDraw M b Q) (nat_value F)) draw) cell).1 =
    (preparedComputedCellReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb hb
      (Eq.mpr (congrArg (cellScaleDraw M b Q) (nat_value F)) (fun t i => (draw t i).1)) cell).1 := by
  have h := preparedComputedCellSourceWithWork_value source target parent P F exponent Q eM eF
    hM hF hP tau a parentInitial child initial current R hc hi b eb hb
    (Eq.mpr (congrArg (cellScaleReadDraw M b Q) (nat_value F)) draw) cell
  rw [sourceDraw_project_cast M b Q _ _ (nat_value F) draw] at h
  exact h

theorem preparedLocalGroupScaleSourceWithWork_value (eb : ℕ)
    (draw : CellGroupReadDraws M F Q) (query : TargetInterval target.length) :
    (preparedLocalGroupScaleSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi eb draw query).1 =
      (preparedLocalGroupScaleReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi eb (fun b cell t i => (draw b cell t i).1) query).1 := by
  simp only [preparedLocalGroupScaleSourceWithWork, preparedLocalGroupScaleReadWithWork,
    filterMapWithWork_value]
  apply List.filterMap_congr
  intro cell _
  have h := computedCellSource_cast_value source target parent P F exponent Q eM eF hM hF hP tau a
    parentInitial child initial current R hc hi (2 ^ eb) eb rfl (draw (2 ^ eb) cell) cell
  simpa only using h

theorem preparedLocalCellGroupsSourceWithWork_value (N : ℕ)
    (draw : CellGroupReadDraws M F Q) (query : TargetInterval target.length) :
    (preparedLocalCellGroupsSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi N draw query).1 =
      (preparedLocalCellGroupsReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi N (fun b cell t i => (draw b cell t i).1) query).1 := by
  simp only [preparedLocalCellGroupsSourceWithWork, preparedLocalCellGroupsReadWithWork,
    arithmeticFlatMapWithWork_value]
  apply List.flatMap_congr
  intro eb _
  split_ifs
  · have h := preparedLocalGroupScaleSourceWithWork_value source target parent P F exponent Q eM eF
      hM hF hP tau a parentInitial child initial current R hc hi eb draw query
    simpa only using h
  · rfl

theorem preparedLocalCellGroupsSourceWithWork_semantic_value (N : ℕ)
    (draw : CellGroupReadDraws M F Q) (query : TargetInterval target.length) :
    (preparedLocalCellGroupsSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi N draw query).1 =
      (preparedLocalCellGroupsWithWork source target parent N P F exponent Q eM eF hM hF hP tau a
        (fun r => (parentInitial r).1) (fun i r => (child i r).1)
        (fun i r => (initial i r).1) (fun i r => (current i r).1)
        (fun b cell t i => (draw b cell t i).1) query).1 :=
  (preparedLocalCellGroupsSourceWithWork_value source target parent P F exponent Q eM eF hM hF hP tau a
    parentInitial child initial current R hc hi N draw query).trans
  (preparedLocalCellGroupsReadWithWork_value_only source target parent P F exponent Q eM eF hM hF hP tau a
    parentInitial child initial current R hc hi N (fun b cell t i => (draw b cell t i).1) query)
end Group

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySourceBuffers
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Source words are decoded only by counted buffer lookups, natural
floor and remainder routines. The resulting draws are exactly the draws
used by the semantic adaptive query, for every stored answer list. -/

namespace EditApproximation



namespace BinaryFraction



@[simp] theorem queryOnlineIntegerReadWithWork_value {n : ℕ} (keys : List (ℕ × TargetInterval n))
    (values : List BinaryFraction) (b : ℕ) (q : TargetInterval n) :
    (queryOnlineIntegerReadWithWork keys values b q).1 =
      ⌊finiteAnswerTable keys (values.map value) (b, q)⌋₊ := by
  simp only [queryOnlineIntegerReadWithWork, naturalFloorWithWork_value,
    gatheredWordLookupWithWork_value _ queryOnlineKeyEqualWithWork_value]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryDataBuffers
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Counted local data buffers for the adaptive gathers. Bounds depend on
stored keys and the requested key, not on an unbounded ambient key type. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem queryChildReadWithWork_value {M n : ℕ}
    (keys : List (Fin M × TargetInterval n)) (values : List BinaryFraction)
    (i : Fin M) (q : TargetInterval n) :
    (queryChildReadWithWork keys values i q).1.value =
      finiteAnswerTable keys (values.map value) (i, q) :=
  gatheredWordLookupWithWork_value _ coordinateEqualWithWork_value keys values (i, q)



@[simp] theorem queryHistoryReadWithWork_value {M n : ℕ}
    (keys : List (Fin M × ℕ × TargetInterval n)) (values : List BinaryFraction)
    (s : ℕ) (input : Fin M × TargetInterval n) :
    (queryHistoryReadWithWork keys values s input).1.value =
      finiteAnswerTable keys (values.map value) (input.1, s, input.2) :=
  gatheredWordLookupWithWork_value _ queryHistoryEqualWithWork_value keys values (input.1, s, input.2)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalSelectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete selectors of the adaptive local program. Source and table
lookups are evaluated by their counted finite-buffer routines. Their value
identities hold even for arbitrary gathered answer lists. -/

namespace EditApproximation
namespace BinaryFraction

section Selectors
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)

theorem queryGroupSelectWithWork_value_oai (draw : CountedCellGroupDraws M F Q)
    (keys : List (Fin M × TargetInterval target.length)) (words : List BinaryFraction)
    (q : TargetInterval target.length) :
    ((queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF tau a
      parentInitial child initial R hc hi draw keys words q).1.map BinaryBellmanAction.decode) =
      localCellGroupActions source target parent N P F exponent Q tau.value a.value
        (fun r => (parentInitial r).1.value) (fun i r => (child i r).1.value)
        (fun i r => (initial i r).1.value)
        (fun i r => finiteAnswerTable keys (words.map value) (i, r))
        (fun b cell scale sample => (draw b cell scale sample).1) q := by
  unfold queryGroupSelectWithWork
  rw [preparedLocalCellGroupsSourceWithWork_semantic_value]
  rw [preparedLocalCellGroupsWithWork_value]
  simp only [queryChildReadWithWork_value]

end Selectors
end BinaryFraction
end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWork_value_oai.{u_1} := @OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWork_value_oai.{u_1}
