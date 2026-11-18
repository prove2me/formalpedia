-- Prove2me | solution 1 for OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWork_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:26:54.529197+00:00
-- url     : https://prove2.me/submissions/f3929189-c54a-4e4a-89f2-8df7a851f2d6

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
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea000
import Definitions.Def_OAIQ361V3Ea001
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_preparedLocalCellGroupsWithWork_cost

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

theorem arithmeticFlatMapWithWork_factor {α β : Type*} (read plain : α → List β × ℕ)
    (xs : List α) (K : ℕ) (hK : 1 ≤ K)
    (hvalue : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hcost : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 * K) :
    (arithmeticFlatMapWithWork read xs).1 = (arithmeticFlatMapWithWork plain xs).1 ∧
      (arithmeticFlatMapWithWork read xs).2 ≤ (arithmeticFlatMapWithWork plain xs).2 * K := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [arithmeticFlatMapWithWork, Nat.zero_mul, le_refl]⟩
  | cons x xs ih =>
    have hv := hvalue x List.mem_cons_self
    have hc := hcost x List.mem_cons_self
    have ht := ih (fun y hy => hvalue y (List.mem_cons_of_mem _ hy))
      (fun y hy => hcost y (List.mem_cons_of_mem _ hy))
    constructor
    · simp only [arithmeticFlatMapWithWork, hv, ht.1]
    · simp only [arithmeticFlatMapWithWork, hv]
      have hl : (plain x).1.length ≤ (plain x).1.length * K := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (plain x).1.length hK
      nlinarith only [hc, ht.2, hl, hK]

theorem filterWithWork_length_le_cost {α : Type*} (test : α → Bool × ℕ) (xs : List α) :
    xs.length ≤ (filterWithWork test xs).2 := by
  induction xs with
  | nil => simp only [List.length_nil, Nat.zero_le]
  | cons x xs ih => simp only [List.length_cons, filterWithWork]; omega

theorem arithmeticMapWithWork_length_le_cost {α β : Type*} (f : α → β × ℕ) (xs : List α) :
    xs.length ≤ (arithmeticMapWithWork f xs).2 := by
  induction xs with
  | nil => simp only [List.length_nil, Nat.zero_le]
  | cons x xs ih => simp only [List.length_cons, arithmeticMapWithWork]; omega

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryReadCostBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lookup overhead is controlled by the loops that actually run.
These comparisons require only a bound on one finite-buffer lookup. -/

namespace EditApproximation

theorem arithmeticMapWithWork_factor {α β : Type*} (read plain : α → β × ℕ)
    (xs : List α) (K : ℕ) (hK : 1 ≤ K)
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 * K) :
    (arithmeticMapWithWork read xs).1 = (arithmeticMapWithWork plain xs).1 ∧
    (arithmeticMapWithWork read xs).2 ≤ (arithmeticMapWithWork plain xs).2 * K := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [arithmeticMapWithWork, Nat.zero_mul, le_refl]⟩
  | cons x xs ih =>
    have hx := hv x List.mem_cons_self
    have hcx := hc x List.mem_cons_self
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    constructor
    · simp only [arithmeticMapWithWork, hx, ht.1]
    · simp only [arithmeticMapWithWork]
      nlinarith only [hcx, ht.2, hK]

theorem vectorMapWithWork_factor {α : Type*} (d : ℕ) (read plain : Fin d → α × ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hv : ∀ i, (read i).1 = (plain i).1)
    (hc : ∀ i, (read i).2 ≤ (plain i).2 * K) :
    (vectorMapWithWork d read).1 = (vectorMapWithWork d plain).1 ∧
    (vectorMapWithWork d read).2 ≤ (vectorMapWithWork d plain).2 * K := by
  constructor
  · apply Vector.ext
    intro i hi
    change (vectorMapWithWork d read).1.get ⟨i, hi⟩ = (vectorMapWithWork d plain).1.get ⟨i, hi⟩
    rw [vectorMapWithWork_value, vectorMapWithWork_value]
    exact hv _
  · simp only [vectorMapWithWork, Vector.toList_map, Vector.toList_ofFn,
      List.map_ofFn, Function.comp_def, List.sum_ofFn]
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hc i)
    rw [← Finset.sum_mul] at hs
    have hd := Nat.mul_le_mul_left (6 * d) hK
    simp only [Nat.mul_one] at hd
    nlinarith only [hs, hd]


theorem filterWithWork_factor {α : Type*} (read plain : α → Bool × ℕ)
    (xs : List α) (K : ℕ) (hK : 1 ≤ K)
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 * K) :
    (filterWithWork read xs).1 = (filterWithWork plain xs).1 ∧
    (filterWithWork read xs).2 ≤ (filterWithWork plain xs).2 * K := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [filterWithWork, Nat.zero_mul, le_refl]⟩
  | cons x xs ih =>
    have hx := hv x List.mem_cons_self
    have hcx := hc x List.mem_cons_self
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    constructor
    · simp only [filterWithWork, hx, ht.1]
    · simp only [filterWithWork]
      nlinarith only [hcx, ht.2, hK]

theorem allWithWork_factor {α : Type*} (read plain : α → Bool × ℕ)
    (xs : List α) (K : ℕ) (hK : 1 ≤ K)
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 * K) :
    (allWithWork read xs).1 = (allWithWork plain xs).1 ∧
    (allWithWork read xs).2 ≤ (allWithWork plain xs).2 * K := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [allWithWork, Nat.zero_mul, le_refl]⟩
  | cons x xs ih =>
    have hx := hv x List.mem_cons_self
    have hcx := hc x List.mem_cons_self
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    constructor
    · simp only [allWithWork, hx, ht.1]
    · simp only [allWithWork]
      nlinarith only [hcx, ht.2, hK]

theorem filterMapWithWork_factor {α β : Type*} (read plain : α → Option β × ℕ)
    (xs : List α) (K : ℕ) (hK : 1 ≤ K)
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 * K) :
    (filterMapWithWork read xs).1 = (filterMapWithWork plain xs).1 ∧
    (filterMapWithWork read xs).2 ≤ (filterMapWithWork plain xs).2 * K := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [filterMapWithWork, Nat.zero_mul, le_refl]⟩
  | cons x xs ih =>
    have hx := hv x List.mem_cons_self
    have hcx := hc x List.mem_cons_self
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    simp only [filterMapWithWork, hx, ht.1]
    cases (plain x).1 with
    | none => exact ⟨trivial, by nlinarith only [hcx, ht.2, hK]⟩
    | some value => exact ⟨trivial, by nlinarith only [hcx, ht.2, hK]⟩

/-- Multiplicative work bounds are preserved when the same nonnegative
overhead is added to both counters. -/
theorem cost_replace_factor (a c old new K : ℕ) (hc : c ≤ a * K) (hK : 1 ≤ K)
    (ha : a ≤ old) (hn : new + a ≤ old + c) : new ≤ old * K := by
  have hx := Nat.mul_le_mul_left (old - a) hK
  simp only [Nat.mul_one] at hx
  have he : a + (old - a) = old := by omega
  calc
    new ≤ c + (old - a) := by omega
    _ ≤ a * K + (old - a) * K := Nat.add_le_add hc hx
    _ = old * K := by rw [← Nat.add_mul, he]

/-- A compulsory constant instruction pays for one additional lookup. -/
theorem cost_factor_with_read (a c x r R K : ℕ) (hc : c ≤ a * K)
    (hr : r ≤ R) (hx : 1 ≤ x) (hK : R + 1 ≤ K) :
    r + c + x ≤ (a + x) * K := by
  have hmul := Nat.mul_le_mul_left x hK
  have hR := Nat.mul_le_mul_right R hx
  simp only [Nat.one_mul] at hR
  have hrest : r + x ≤ x * K := by nlinarith only [hmul, hR, hr]
  calc
    r + c + x = c + (r + x) := by omega
    _ ≤ a * K + x * K := Nat.add_le_add hc hrest
    _ = (a + x) * K := by ring

namespace BinaryFraction

theorem tableReadFactor_pos (R : ℕ) : 1 ≤ tableReadFactor R := by
  unfold tableReadFactor
  omega

theorem tableReadFactor_absorb (a c n R : ℕ) (hc : c ≤ a + n * (R + 3)) (hn : n ≤ a) :
    c ≤ a * tableReadFactor R := by
  have hm := Nat.mul_le_mul_right (R + 3) hn
  have hk : R + 4 ≤ tableReadFactor R := by unfold tableReadFactor; omega
  calc
    c ≤ a + a * (R + 3) := hc.trans (Nat.add_le_add_left hm a)
    _ = a * (R + 4) := by ring
    _ ≤ a * tableReadFactor R := Nat.mul_le_mul_left a hk

theorem endpointScoreReadWithWork_factor {n M : ℕ} (r : TargetInterval n)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (states : Fin M → TargetInterval n)
    (R : ℕ) (hr : ∀ i, (read i (states i)).2 ≤ R) :
    (endpointScoreReadWithWork r read states).2 ≤
      (endpointScoreWithWork r (fun i q => (read i q).1) states).2 * tableReadFactor R := by
  apply tableReadFactor_absorb _ _ M R (endpointScoreReadWithWork_cost r read states R hr)
  simp only [endpointScoreWithWork, endpointConnectionWithWork]
  omega

theorem prefixReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx) (r : TargetInterval n)
    (states : Fin M → TargetInterval n) (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (j : ℕ) (p : BinaryFraction) (R : ℕ) (hr : ∀ i, (read i (states i)).2 ≤ R) :
    (prefixReadWithWork parent r states read j p).2 ≤
      (prefixWithWork parent r states (fun i q => (read i q).1) j p).2 * tableReadFactor R := by
  have hc := prefixReadWithWork_cost parent r states read j p R hr
  have hn : M ≤ (prefixWithWork parent r states (fun i q => (read i q).1) j p).2 := by
    simp only [prefixWithWork]
    omega
  have hm := Nat.mul_le_mul_right (R + 4) hn
  have hk : R + 5 ≤ tableReadFactor R := by unfold tableReadFactor; omega
  calc
    _ ≤ _ + M * (R + 4) := hc
    _ ≤ _ + (prefixWithWork parent r states (fun i q => (read i q).1) j p).2 * (R + 4) :=
      Nat.add_le_add_left hm _
    _ = (prefixWithWork parent r states (fun i q => (read i q).1) j p).2 * (R + 5) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hk

theorem bandEnvelopeReadWithWork_factor {M n : ℕ} (b : ℕ) (band : List (Fin M → TargetInterval n))
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (i : Fin M) (R : ℕ)
    (hr : ∀ action ∈ band, (read i (action i)).2 ≤ R) :
    (bandEnvelopeReadWithWork b band read i).2 ≤
      (bandEnvelopeWithWork b band (fun j q => (read j q).1) i).2 * tableReadFactor R := by
  apply tableReadFactor_absorb _ _ band.length R (bandEnvelopeReadWithWork_cost b band read i R hr)
  simp only [bandEnvelopeWithWork]
  omega

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandReadCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite-buffer lookup multiplies local band-loop work by a fixed
linear factor. Every comparison uses the same actual band and output. -/

namespace EditApproximation
namespace BinaryFraction

theorem wideMinimumReadWithWork_factor {n M : ℕ} (r : TargetInterval n)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ [])
    (R : ℕ) (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (wideMinimumReadWithWork r read actions hne).2 ≤
      (wideMinimumWithWork r (fun i q => (read i q).1) actions hne).2 * tableReadFactor R := by
  have hm := arithmeticMapWithWork_factor
    (endpointScoreReadWithWork r read) (endpointScoreWithWork r (fun i q => (read i q).1))
    actions (tableReadFactor R) (tableReadFactor_pos R)
    (fun action _ => endpointScoreReadWithWork_eq r read action)
    (fun action ha => endpointScoreReadWithWork_factor r read action R (hr action ha))
  have hf := endpointScoreReadWithWork_factor r read (actions.head hne) R
    (hr _ (List.head_mem hne))
  have hc := Nat.add_le_add hf hm.2
  rw [← Nat.add_mul] at hc
  apply cost_replace_factor _ _ _ _ _ hc (tableReadFactor_pos R)
  · unfold wideMinimumWithWork
    dsimp only
    omega
  · unfold wideMinimumReadWithWork wideMinimumWithWork
    dsimp only
    rw [hm.1, endpointScoreReadWithWork_eq]
    omega

theorem prefixMinimumReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (j : ℕ) (p : BinaryFraction)
    (R : ℕ) (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (prefixMinimumReadWithWork parent r actions hne read j p).2 ≤
      (prefixMinimumWithWork parent r actions hne (fun i q => (read i q).1) j p).2 *
        tableReadFactor R := by
  have hm := arithmeticMapWithWork_factor
    (fun action => prefixReadWithWork parent r action read j p)
    (fun action => prefixWithWork parent r action (fun i q => (read i q).1) j p)
    actions (tableReadFactor R) (tableReadFactor_pos R)
    (fun action _ => prefixReadWithWork_eq parent r action read j p)
    (fun action ha => prefixReadWithWork_factor parent r action read j p R (hr action ha))
  have hf := prefixReadWithWork_factor parent r (actions.head hne) read j p R
    (hr _ (List.head_mem hne))
  have hc := Nat.add_le_add hf hm.2
  rw [← Nat.add_mul] at hc
  apply cost_replace_factor _ _ _ _ _ hc (tableReadFactor_pos R)
  · unfold prefixMinimumWithWork
    dsimp only
    omega
  · unfold prefixMinimumReadWithWork prefixMinimumWithWork
    dsimp only
    rw [hm.1, prefixReadWithWork_eq]
    omega

theorem cutGuardReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (states : Fin M → TargetInterval n)
    (velocity tolerance : BinaryFraction) (j : Fin M) (R : ℕ)
    (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (cutGuardReadWithWork parent r actions hne read states velocity tolerance j).2 ≤
      (cutGuardWithWork parent r actions hne (fun i q => (read i q).1) states velocity tolerance j).2 *
        tableReadFactor R := by
  unfold cutGuardReadWithWork cutGuardWithWork
  split_ifs
  · simpa only [Nat.one_mul] using tableReadFactor_pos R
  · have h := prefixMinimumReadWithWork_factor parent r actions hne read j.val
      (subWithWork (nat (states j).lo) (nat (sourceChild parent j).lo)).1 R hr
    dsimp only
    rw [prefixMinimumReadWithWork_eq]
    apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R)
    · omega
    · omega

theorem bandPredicateReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (b : ℕ) (tau theta velocity : BinaryFraction)
    (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (states : Fin M → TargetInterval n)
    (R : ℕ) (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (bandPredicateReadWithWork parent r b tau theta velocity actions hne read states).2 ≤
      (bandPredicateWithWork parent r b tau theta velocity actions hne (fun i q => (read i q).1) states).2 *
        tableReadFactor R := by
  have hc := allWithWork_factor
    (cutGuardReadWithWork parent r actions hne read states velocity (bandToleranceWithWork tau theta b M).1)
    (cutGuardWithWork parent r actions hne (fun i q => (read i q).1) states velocity
      (bandToleranceWithWork tau theta b M).1)
    (List.finRange M) (tableReadFactor R) (tableReadFactor_pos R)
    (fun j _ => cutGuardReadWithWork_eq parent r actions hne read states velocity _ j)
    (fun j _ => cutGuardReadWithWork_factor parent r actions hne read states velocity _ j R hr)
  apply cost_replace_factor _ _ _ _ _ hc.2 (tableReadFactor_pos R)
  · unfold bandPredicateWithWork
    dsimp only
    omega
  · unfold bandPredicateReadWithWork bandPredicateWithWork
    dsimp only
    omega

theorem bandFromActionsReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (b : ℕ) (tau theta velocity : BinaryFraction)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ [])
    (R : ℕ) (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (bandFromActionsReadWithWork parent r b tau theta velocity read actions hne).2 ≤
      (bandFromActionsWithWork parent r b tau theta velocity (fun i q => (read i q).1) actions hne).2 *
        tableReadFactor R := by
  have hf := filterWithWork_factor
    (bandPredicateReadWithWork parent r b tau theta velocity actions hne read)
    (bandPredicateWithWork parent r b tau theta velocity actions hne (fun i q => (read i q).1))
    actions (tableReadFactor R) (tableReadFactor_pos R)
    (fun action _ => (bandPredicateReadWithWork_eq_cost parent r b tau theta velocity actions hne
      read action R hr).1)
    (fun action _ => bandPredicateReadWithWork_factor parent r b tau theta velocity actions hne
      read action R hr)
  unfold bandFromActionsReadWithWork bandFromActionsWithWork
  dsimp only
  split_ifs
  · apply cost_replace_factor _ _ _ _ _ hf.2 (tableReadFactor_pos R)
    · omega
    · omega
  · exact Nat.le_mul_of_pos_right _ (by have := tableReadFactor_pos R; omega)

theorem representativeFromActionsReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (sourceLength b : ℕ) (tau theta : BinaryFraction)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (actions : List (Fin M → TargetInterval n)) (R : ℕ)
    (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (representativeFromActionsReadWithWork parent r sourceLength b tau theta read actions).2 ≤
      (representativeFromActionsWithWork parent r sourceLength b tau theta
        (fun i q => (read i q).1) actions).2 * tableReadFactor R := by
  unfold representativeFromActionsReadWithWork representativeFromActionsWithWork
  by_cases hne : actions = []
  · simp only [dite_eq_left hne]
    simpa only [Nat.one_mul] using tableReadFactor_pos R
  · simp only [dite_eq_right hne]
    have hz := wideMinimumReadWithWork_factor r read actions hne R hr
    rw [wideMinimumReadWithWork_eq]
    split_ifs
    · have hb := bandFromActionsReadWithWork_factor parent r b tau theta
        (divWithWork (stateGapWithWork sourceLength r).1
          (wideMinimumWithWork r (fun i q => (read i q).1) actions hne).1).1 read actions hne R hr
      have hc := Nat.add_le_add hz hb
      rw [← Nat.add_mul] at hc
      apply cost_replace_factor _ _ _ _ _ hc (tableReadFactor_pos R) <;> omega
    · apply cost_replace_factor _ _ _ _ _ hz (tableReadFactor_pos R) <;> omega

theorem preparedRepresentativeReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (sourceLength b P : ℕ) (tau theta : BinaryFraction)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (R : ℕ)
    (hr : ∀ i q, (read i q).2 ≤ R) :
    (preparedRepresentativeReadWithWork parent r sourceLength b P tau theta read).2 ≤
      (preparedRepresentativeWithWork parent r sourceLength b P tau theta
        (fun i q => (read i q).1)).2 * tableReadFactor R := by
  have h := representativeFromActionsReadWithWork_factor parent r sourceLength b tau theta read
    ((wideActionGridWithWork M parent r b P).1.map Vector.get) R (fun _ _ i => hr i _)
  unfold preparedRepresentativeReadWithWork preparedRepresentativeWithWork
  dsimp only
  apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R) <;> omega

theorem envelopeVectorReadWithWork_factor {n M : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval n))
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (R : ℕ)
    (hr : ∀ i q, (read i q).2 ≤ R) :
    (envelopeVectorReadWithWork b band read).2 ≤
      (envelopeVectorWithWork b band (fun i q => (read i q).1)).2 * tableReadFactor R := by
  exact (vectorMapWithWork_factor M
    (bandEnvelopeReadWithWork b band read)
    (bandEnvelopeWithWork b band (fun i q => (read i q).1))
    (tableReadFactor R) (tableReadFactor_pos R)
    (fun i => bandEnvelopeReadWithWork_eq b band read i)
    (fun i => bandEnvelopeReadWithWork_factor b band read i R (fun _ _ => hr i _))).2

theorem roundedBandReadWithWork_factor {n M : ℕ} (exponent b : ℕ)
    (band : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (R : ℕ)
    (hr : ∀ i q, (read i q).2 ≤ R) :
    (roundedBandReadWithWork exponent b band hne read).2 ≤
      (roundedBandWithWork exponent b band hne (fun i q => (read i q).1)).2 * tableReadFactor R := by
  apply (vectorMapWithWork_factor M _ _ (tableReadFactor R) (tableReadFactor_pos R) ?_ ?_).2
  · intro i
    simp only [bandEnvelopeReadWithWork_eq]
  · intro i
    have h := bandEnvelopeReadWithWork_factor b band read i R (fun _ _ => hr i _)
    dsimp only
    simp only [bandEnvelopeReadWithWork_eq]
    apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R) <;> omega

theorem unskippedGuardReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (b exponent : ℕ) (F : BinaryFraction)
    (band wide : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (R : ℕ)
    (hr : ∀ i q, (read i q).2 ≤ R) :
    (unskippedGuardReadWithWork parent r b exponent F band wide hne read).2 ≤
      (unskippedGuardWithWork parent r b exponent F band wide hne
        (fun i q => (read i q).1)).2 * tableReadFactor R := by
  have he := envelopeVectorReadWithWork_factor b band read R hr
  have heq := (envelopeVectorReadWithWork_eq_cost b band read R hr).1
  have hrnd := roundedBandReadWithWork_factor exponent b band hne read R hr
  have hrndq := (roundedBandReadWithWork_eq_cost exponent b band hne read R hr).1
  have h := Nat.add_le_add he hrnd
  rw [← Nat.add_mul] at h
  unfold unskippedGuardReadWithWork unskippedGuardWithWork
  dsimp only
  rw [heq, hrndq]
  apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R) <;> omega

theorem preparedUnskippedReadWithWork_factor {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau F : BinaryFraction)
    (read initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (R : ℕ) (hr : ∀ i q, (read i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
    (center : TargetInterval target.length) :
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau F
      read initial R R hr hi center).2 ≤
      (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau F
        (fun i q => (read i q).1) (fun i q => (initial i q).1) center).2 * tableReadFactor R := by
  have hband := preparedRepresentativeReadWithWork_factor parent center (parent.hi - parent.lo)
    b P tau (inversePowerTwo exponent) read R hr
  have hbandq := (preparedRepresentativeReadWithWork_eq_cost parent center (parent.hi - parent.lo)
    b P tau (inversePowerTwo exponent) read R hr).1
  unfold preparedUnskippedReadWithWork preparedUnskippedCandidateWithWork
  dsimp only
  simp only [hbandq]
  by_cases hempty : (preparedRepresentativeWithWork parent center (parent.hi - parent.lo)
      b P tau (inversePowerTwo exponent) (fun i q => (read i q).1)).1 = []
  · simp only [dite_eq_left hempty]
    apply cost_replace_factor _ _ _ _ _ hband (tableReadFactor_pos R) <;> omega
  · simp only [dite_eq_right hempty]
    have hg := unskippedGuardReadWithWork_factor parent center b exponent F
      (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
        tau (inversePowerTwo exponent) (fun i q => (read i q).1)).1
      ((wideActionGridWithWork M parent center b P).1.map Vector.get) hempty initial R hi
    have hgq := (unskippedGuardReadWithWork_eq_cost parent center b exponent F
      (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
        tau (inversePowerTwo exponent) (fun i q => (read i q).1)).1
      ((wideActionGridWithWork M parent center b P).1.map Vector.get) hempty initial R hi).1
    simp only [hgq]
    have h := Nat.add_le_add hband hg
    rw [← Nat.add_mul] at h
    split_ifs <;> apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R) <;> omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalCells
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Direct bounded-range enumeration of the cells meeting a query square. -/

namespace EditApproximation



theorem localCellCoordinates_length_le (side : ℚ) (hside : 0 < side)
    (p radius K : ℕ) (hbudget : 2 * (radius : ℚ) / side ≤ K) :
    (localCellCoordinates side p radius).length ≤ K + 2 := by
  let first := ⌊((p - radius : ℕ) : ℚ) / side⌋₊
  let last := ⌊((p + radius : ℕ) : ℚ) / side⌋₊
  have horder : first ≤ last := Nat.floor_le_floor (div_le_div_of_nonneg_right
    (by exact_mod_cast (show p - radius ≤ p + radius by omega)) hside.le)
  have hhi : (last : ℚ) ≤ ((p + radius : ℕ) : ℚ) / side :=
    Nat.floor_le (div_nonneg (Nat.cast_nonneg _) hside.le)
  have hlo : ((p - radius : ℕ) : ℚ) / side < (first : ℚ) + 1 := Nat.lt_floor_add_one _
  have hwidth : ((p + radius : ℕ) : ℚ) - ((p - radius : ℕ) : ℚ) ≤ 2 * radius := by
    have h : p + radius - (p - radius) ≤ 2 * radius := by omega
    have hR : ((p + radius - (p - radius) : ℕ) : ℚ) ≤ ((2 * radius : ℕ) : ℚ) := by exact_mod_cast h
    simpa only [Nat.cast_sub (show p - radius ≤ p + radius by omega), Nat.cast_mul, Nat.cast_ofNat] using hR
  have hquotient : ((p + radius : ℕ) : ℚ) / side - ((p - radius : ℕ) : ℚ) / side ≤ K := by
    calc
      _ = (((p + radius : ℕ) : ℚ) - ((p - radius : ℕ) : ℚ)) / side := by ring
      _ ≤ (2 * radius) / side := div_le_div_of_nonneg_right hwidth hside.le
      _ ≤ K := hbudget
  have hcount : ((last + 1 - first : ℕ) : ℚ) < (K : ℚ) + 2 := by
    rw [Nat.cast_sub (by omega : first ≤ last + 1), Nat.cast_add, Nat.cast_one]
    linarith only [hhi, hlo, hquotient]
  have hcountN : last + 1 - first < K + 2 := by exact_mod_cast hcount
  exact (by simpa only [localCellCoordinates, List.length_range', first, last] using hcountN.le)



theorem localTargetCells_length_le {n : ℕ} (side : ℚ) (hside : 0 < side)
    (radius K : ℕ) (q : TargetInterval n) (hbudget : 2 * (radius : ℚ) / side ≤ K) :
    (localTargetCells side radius q).length ≤ (K + 2) ^ 2 := by
  have hfirst := localCellCoordinates_length_le side hside q.lo radius K hbudget
  have hsecond := localCellCoordinates_length_le side hside q.hi radius K hbudget
  have h := list_flatMap_length_le (localCellCoordinates side q.lo radius)
    (fun lo => (localCellCoordinates side q.hi radius).map fun hi => (lo, hi)) (K + 2)
    (fun lo _ => by simpa only [List.length_map] using hsecond)
  exact h.trans (by simpa only [pow_two] using Nat.mul_le_mul_right (K + 2) hfirst)

/-- Every retained query scale has only polynomially many nearby cells,
even when the initial seed is inaccurate. -/
theorem localTargetCells_query_length {n : ℕ} (F b exponent : ℕ)
    (q : TargetInterval n) (w : ℚ) (hF : 1 ≤ F) (hb : 1 ≤ b)
    (hw : 0 ≤ w) (hwindow : w / (16 * F) ≤ b) :
    (localTargetCells ((2 : ℚ) ^ (-(exponent : ℤ)) * b) ⌈w⌉₊ q).length ≤
      ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 := by
  have hFpos : (0 : ℚ) < F := by exact_mod_cast (by omega : 0 < F)
  have hbpos : (0 : ℚ) < b := by exact_mod_cast (by omega : 0 < b)
  have hbR : (1 : ℚ) ≤ b := by exact_mod_cast hb
  have hside : 0 < (2 : ℚ) ^ (-(exponent : ℤ)) * b := by positivity
  apply localTargetCells_length_le _ hside _ ((32 * F + 2) * 2 ^ exponent) q
  apply (div_le_iff₀ hside).2
  have hwidth : w ≤ 16 * (F : ℚ) * b :=
    by nlinarith only [(div_le_iff₀ (by positivity : (0 : ℚ) < 16 * F)).mp hwindow]
  have hceil : (⌈w⌉₊ : ℚ) < w + 1 := Nat.ceil_lt_add_one hw
  have hcancel : (((32 * F + 2) * 2 ^ exponent : ℕ) : ℚ) *
      ((2 : ℚ) ^ (-(exponent : ℤ)) * b) = (32 * (F : ℚ) + 2) * b := by
    push_cast
    rw [zpow_neg, zpow_natCast]
    field_simp
  rw [hcancel]
  nlinarith only [hceil, hwidth, hbR]

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalGroupBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded local cell loops on arbitrary initial seeds. -/

namespace EditApproximation

theorem localCellGroupActions_length {α : Type*} {M : ℕ} (source target : List α)
    (parent : TargetInterval source.length) (N P F exponent Q : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial current : Fin M → TargetInterval target.length → ℚ)
    (draw : CellGroupDraws M F Q) (q : TargetInterval target.length)
    (hF : 1 ≤ F) (hw : 0 ≤ parentInitial q) :
    (localCellGroupActions source target parent N P F exponent Q tau a parentInitial
      child initial current draw q).length ≤
      (dyadicQueryWindow N (parentInitial q) a F).length *
        ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 := by
  unfold localCellGroupActions
  apply list_flatMap_length_le
  intro b hb
  have hwindow := of_decide_eq_true (List.mem_filter.mp hb).2
  have hbpos : 1 ≤ b := by
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hb).1
    exact Nat.one_le_two_pow
  exact (List.length_filterMap_le _ _).trans
    (localTargetCells_query_length F b exponent q (parentInitial q) hF hbpos hw hwindow.1)

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupReadCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact group score scans charge the finite-buffer readers through the
same loops as their arithmetic-only counterparts. -/

namespace EditApproximation
namespace BinaryFraction

theorem scoredArgmaxWithWork_factor {α : Type*} (read plain : α → BinaryFraction × ℕ)
    (xs : List α) (K : ℕ) (hK : 1 ≤ K)
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 * K) :
    (scoredArgmaxWithWork read xs).1 = (scoredArgmaxWithWork plain xs).1 ∧
    (scoredArgmaxWithWork read xs).2 ≤ (scoredArgmaxWithWork plain xs).2 * K := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [scoredArgmaxWithWork, Nat.zero_mul, le_refl]⟩
  | cons x xs ih =>
    have hx := hv x List.mem_cons_self
    have hcx := hc x List.mem_cons_self
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    have h := Nat.add_le_add ht.2 hcx
    rw [← Nat.add_mul] at h
    simp only [scoredArgmaxWithWork, ht.1, hx]
    cases (scoredArgmaxWithWork plain xs).1 with
    | none =>
      refine ⟨rfl, ?_⟩
      dsimp only
      apply cost_replace_factor _ _ _ _ _ h hK <;> omega
    | some best =>
      refine ⟨rfl, ?_⟩
      dsimp only
      apply cost_replace_factor _ _ _ _ _ h hK <;> omega

theorem selectGroupWithWork_factor {α : Type*} (read plain : α → BinaryFraction × ℕ)
    (xs : List α) (hne : xs ≠ []) (K : ℕ) (hK : 1 ≤ K)
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 * K) :
    (selectGroupWithWork xs hne read).1 = (selectGroupWithWork xs hne plain).1 ∧
    (selectGroupWithWork xs hne read).2 ≤ (selectGroupWithWork xs hne plain).2 * K := by
  have h := scoredArgmaxWithWork_factor
    (fun x => ((read x).1.neg, (read x).2 + 1))
    (fun x => ((plain x).1.neg, (plain x).2 + 1)) xs K hK
    (fun x hx => by rw [hv x hx]) (fun x hx => by
      apply cost_replace_factor _ _ _ _ _ (hc x hx) hK <;> omega)
  unfold selectGroupWithWork
  dsimp only
  rw [h.1]
  refine ⟨rfl, ?_⟩
  apply cost_replace_factor _ _ _ _ _ h.2 hK <;> omega

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

theorem unskippedEstimateReadWithWork_factor (member : Member) (R : ℕ)
    (hi : ∀ i q, (initial i q).2 ≤ R) (hr : ∀ i q, (current i q).2 ≤ R) :
    (unskippedEstimateReadWithWork source target parent b P exponent Q tau F child initial current
      scales draw member).2 ≤
      (unskippedEstimateWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw member).2 *
        tableReadFactor R := by
  have hm := envelopeVectorReadWithWork_factor b member.actions initial R hi
  have hmq := (envelopeVectorReadWithWork_eq_cost b member.actions initial R hi).1
  have hp := roundedBandReadWithWork_factor exponent b member.actions member.nonempty initial R hi
  have hpq := (roundedBandReadWithWork_eq_cost exponent b member.actions member.nonempty initial R hi).1
  have hv := vectorMapWithWork_factor M
    (fun i => current i ((roundedBandWithWork exponent b member.actions member.nonempty
      (fun j q => (initial j q).1)).1.get i))
    (fun i => ((current i ((roundedBandWithWork exponent b member.actions member.nonempty
      (fun j q => (initial j q).1)).1.get i)).1, 1))
    (tableReadFactor R) (tableReadFactor_pos R) (fun _ => rfl)
    (fun i => by
      change (current i _).2 ≤ 1 * tableReadFactor R
      have hR : R ≤ tableReadFactor R := by unfold tableReadFactor; omega
      simpa only [Nat.one_mul] using (hr i _).trans hR)
  have h := Nat.add_le_add (Nat.add_le_add hm hp) hv.2
  simp only [← Nat.add_mul] at h
  unfold unskippedEstimateReadWithWork unskippedEstimateWithWork
  dsimp only
  rw [hmq, hpq, hv.1]
  apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R) <;> omega

theorem chooseUnskippedReadWithWork_factor (members : List Member) (hne : members ≠ []) (R : ℕ)
    (hi : ∀ i q, (initial i q).2 ≤ R) (hr : ∀ i q, (current i q).2 ≤ R) :
    (chooseUnskippedReadWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).2 ≤
      (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).2 *
        tableReadFactor R := by
  exact (selectGroupWithWork_factor _ _ members hne (tableReadFactor R) (tableReadFactor_pos R)
    (fun member _ => (unskippedEstimateReadWithWork_eq_cost source target parent b P exponent Q
      tau F child initial current scales draw member R R hi hr).1)
    (fun member _ => unskippedEstimateReadWithWork_factor source target parent b P exponent Q
      tau F child initial current scales draw member R hi hr)).2

theorem sampledGroupActionReadWithWork_factor (members : List Member) (hne : members ≠ []) (R : ℕ)
    (hi : ∀ i q, (initial i q).2 ≤ R) (hr : ∀ i q, (current i q).2 ≤ R) :
    (sampledGroupActionReadWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).2 ≤
      (sampledGroupActionWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).2 *
        tableReadFactor R := by
  have hc := chooseUnskippedReadWithWork_factor source target parent b P exponent Q tau F
    child initial current scales draw members hne R hi hr
  have hcq := (chooseUnskippedReadWithWork_eq_cost source target parent b P exponent Q tau F
    child initial current scales draw members hne R R hi hr).1
  have hp := roundedBandReadWithWork_factor exponent b
    (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child
      (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).1.actions
    (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child
      (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).1.nonempty initial R hi
  have hpq := (roundedBandReadWithWork_eq_cost exponent b
    (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child
      (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).1.actions
    (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child
      (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).1.nonempty initial R hi).1
  have h := Nat.add_le_add hc hp
  rw [← Nat.add_mul] at h
  unfold sampledGroupActionReadWithWork sampledGroupActionWithWork
  dsimp only
  simp only [hcq, hpq]
  apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R) <;> omega

end Group
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCellReadCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete whole-cell estimator, including its ordered choice,
executes with a linear factor for each finite-buffer lookup. -/

namespace EditApproximation
namespace BinaryFraction

theorem cellCentersReadWithWork_factor {n : ℕ} (P F b : ℕ) (a theta : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction × ℕ) (cell : ℕ × ℕ)
    (R : ℕ) (hr : ∀ r, (initial r).2 ≤ R) :
    (cellCentersReadWithWork P F b a theta initial cell).2 ≤
      (cellCentersWithWork P F b a theta (fun r => (initial r).1) cell).2 * tableReadFactor R := by
  have h := (cellCentersReadWithWork_eq_cost P F b a theta initial cell R hr).2
  have hK : R + 1 ≤ tableReadFactor R := by unfold tableReadFactor; omega
  exact h.trans (Nat.mul_le_mul_left _ hK)

section Cell
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (hb : 0 < b) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
  (raw : List BinaryFraction) (hraw : raw.map value = groupDyadicScales M b (nat F).value)
  (draw : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → Fin M)

theorem preparedCellGroupReadWithWork_factor (cell : ℕ × ℕ)
    (hp : ∀ r, (parentInitial r).2 ≤ R) (hn : ∀ i q, (current i q).2 ≤ R) :
    (preparedCellGroupReadWithWork source target parent b P F exponent Q hb hP tau a
      parentInitial child initial current R R hc hi raw hraw draw cell).2 ≤
      (preparedCellGroupWithWork source target parent b P F exponent Q hb tau a
        (fun r => (parentInitial r).1) (fun i q => (child i q).1)
        (fun i q => (initial i q).1) (fun i q => (current i q).1) raw hraw draw hP cell).2 *
        tableReadFactor R := by
  have hcenters := cellCentersReadWithWork_factor P F b a (inversePowerTwo exponent)
    parentInitial cell R hp
  have hcentersq := (cellCentersReadWithWork_eq_cost P F b a (inversePowerTwo exponent)
    parentInitial cell R hp).1
  have hm := filterMapWithWork_factor
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
      child initial R R hc hi)
    (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau (nat F)
      (fun i q => (child i q).1) (fun i q => (initial i q).1))
    (cellCentersWithWork P F b a (inversePowerTwo exponent) (fun r => (parentInitial r).1) cell).1
    (tableReadFactor R) (tableReadFactor_pos R)
    (fun center _ => preparedUnskippedReadWithWork_value source target parent b P exponent hb hP
      tau (nat F) child initial R R hc hi center)
    (fun center _ => preparedUnskippedReadWithWork_factor source target parent b P exponent hb hP
      tau (nat F) child initial R hc hi center)
  have hcm := Nat.add_le_add hcenters hm.2
  rw [← Nat.add_mul] at hcm
  unfold preparedCellGroupReadWithWork preparedCellGroupWithWork
  dsimp only
  simp only [hcentersq, hm.1]
  split_ifs with hempty
  · apply cost_replace_factor _ _ _ _ _ hcm (tableReadFactor_pos R) <;> omega
  · have hs := sampledGroupActionReadWithWork_factor source target parent b P exponent Q tau
      (nat F) (fun i q => (child i q).1) initial current
      (indexedGroupScales raw M b (nat F).value hraw)
      (fun t j => draw t (Fin.cast (congrArg (groupSampleCount M Q b)
        (indexedGroupScales_value raw M b (nat F).value hraw t)) j))
      _ hempty R hi hn
    have h := Nat.add_le_add hcm hs
    rw [← Nat.add_mul] at h
    change _ ≤ _ at hs
    unfold dyadicSampledGroupActionReadWithWork dyadicSampledGroupActionWithWork
    dsimp only
    apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R) <;> omega

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

theorem groupScaleSourceCalls_le_work {M : ℕ} (k : ℕ) (h : BinaryFraction)
    (envelope values : Vector BinaryFraction M) (draw : Fin k → Fin M) :
    groupScaleSourceCalls M k ≤ (groupScaleWithWork k h envelope values draw).2 := by
  unfold groupScaleSourceCalls
  split_ifs with heq
  · exact Nat.zero_le _
  · have hl := arithmeticMapWithWork_length_le_cost
      (fun i : Fin M => let test := equalWithWork (envelope.get i) h
        (if test.1 then values.get i else zero, test.2 + 2)) ((List.finRange k).map draw)
    simp only [List.length_map, List.length_finRange] at hl
    change k ≤ (groupTermsWithWork h envelope values ((List.finRange k).map draw)).2 at hl
    unfold groupScaleWithWork
    rw [ite_eq_right heq]
    unfold groupIndexWithWork
    dsimp only
    omega

theorem groupScaleSourceWithWork_cost {M : ℕ} (k : ℕ) (h : BinaryFraction)
    (envelope values : Vector BinaryFraction M) (draw : Fin k → Fin M × ℕ)
    (R : ℕ) (hr : ∀ i, (draw i).2 ≤ R) :
    (groupScaleSourceWithWork k h envelope values draw).2 ≤
      (groupScaleWithWork k h envelope values (fun i => (draw i).1)).2 * (R + 4) := by
  have hmap := arithmeticMapWithWork_cost draw (List.finRange k) R (fun i _ => hr i)
  simp only [List.length_finRange] at hmap
  have hcalls := groupScaleSourceCalls_le_work k h envelope values (fun i => (draw i).1)
  by_cases heq : k = M
  · unfold groupScaleSourceWithWork groupScaleWithWork
    simp only [heq, ite_true, if_true, Nat.zero_add]
    exact Nat.le_mul_of_pos_right _ (by omega)
  · unfold groupScaleSourceWithWork
    rw [ite_eq_right heq]
    dsimp only
    rw [arithmeticMapWithWork_value]
    unfold groupScaleWithWork at hcalls ⊢
    rw [ite_eq_right heq] at hcalls ⊢
    unfold groupScaleSourceCalls at hcalls
    rw [ite_eq_right heq] at hcalls
    simp only [ite_eq_right heq] at hcalls ⊢
    nlinarith only [hmap, hcalls]

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



theorem groupMemberSourceWithWork_eq_cost {M T : ℕ} (scales : Fin T → BinaryFraction)
    (count : Fin T → ℕ) (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ s : Fin T, Fin (count s) → Fin M × ℕ) (R : ℕ)
    (hr : ∀ s i, (draw s i).2 ≤ R) :
    (groupMemberSourceWithWork scales count connection envelope values draw).1 =
      (groupMemberWithWork scales count connection envelope values (fun s i => (draw s i).1)).1 ∧
    (groupMemberSourceWithWork scales count connection envelope values draw).2 ≤
      (groupMemberWithWork scales count connection envelope values (fun s i => (draw s i).1)).2 * (R + 4) := by
  have hm := arithmeticMapWithWork_factor
    (fun s => groupScaleSourceWithWork (count s) (scales s) envelope values (draw s))
    (fun s => groupScaleWithWork (count s) (scales s) envelope values (fun i => (draw s i).1))
    (List.finRange T) (R + 4) (by omega)
    (fun s _ => groupScaleSourceWithWork_value _ _ _ _ _)
    (fun s _ => groupScaleSourceWithWork_cost _ _ _ _ _ R (hr s))
  unfold groupMemberSourceWithWork groupMemberWithWork
  dsimp only
  rw [hm.1]
  exact ⟨rfl, by nlinarith only [hm.2]⟩



theorem countedGroupMemberSourceWithWork_eq_cost {M T : ℕ} (Q b : ℕ)
    (scales : Fin T → BinaryFraction) (connection : BinaryFraction)
    (envelope values : Vector BinaryFraction M)
    (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M × ℕ)
    (R : ℕ) (hr : ∀ t i, (draw t i).2 ≤ R) :
    (countedGroupMemberSourceWithWork Q b scales connection envelope values draw).1 =
      (countedGroupMemberWithWork Q b scales connection envelope values (fun t i => (draw t i).1)).1 ∧
    (countedGroupMemberSourceWithWork Q b scales connection envelope values draw).2 ≤
      (countedGroupMemberWithWork Q b scales connection envelope values (fun t i => (draw t i).1)).2 * (R + 4) := by
  let counts := vectorMapWithWork T fun t => groupSampleCountWithWork M Q b (scales t)
  let count := fun t => bitWordValue (counts.1.get t)
  have heq : ∀ t, count t = groupSampleCount M Q b (scales t).value := by
    intro t
    simp only [count, counts, vectorMapWithWork_value, groupSampleCountWithWork_value]
  have hm := groupMemberSourceWithWork_eq_cost scales count connection envelope values
    (fun t j => draw t (Fin.cast (heq t) j)) R (fun t j => hr t _)
  unfold countedGroupMemberSourceWithWork countedGroupMemberWithWork
  dsimp only
  change _ = (groupMemberWithWork scales count connection envelope values
    (fun t j => (draw t (Fin.cast (heq t) j)).1)).1 ∧ _
  rw [hm.1]
  exact ⟨rfl, by nlinarith only [hm.2]⟩

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

theorem unskippedEstimateSourceWithWork_eq_cost (member : Member) (R : ℕ)
    (hr : ∀ s i, (draw s i).2 ≤ R) :
    (unskippedEstimateSourceWithWork source target parent b P exponent Q tau F child initial current
      scales draw member).1 =
      (unskippedEstimateReadWithWork source target parent b P exponent Q tau F child initial current
        scales (fun s i => (draw s i).1) member).1 ∧
    (unskippedEstimateSourceWithWork source target parent b P exponent Q tau F child initial current
      scales draw member).2 ≤
      (unskippedEstimateReadWithWork source target parent b P exponent Q tau F child initial current
        scales (fun s i => (draw s i).1) member).2 * (R + 4) := by
  have h := countedGroupMemberSourceWithWork_eq_cost Q b scales
    (endpointConnectionWithWork member.center
      (roundedBandReadWithWork exponent b member.actions member.nonempty initial).1.get).1
    (envelopeVectorReadWithWork b member.actions initial).1
    (vectorMapWithWork M fun i => current i
      ((roundedBandReadWithWork exponent b member.actions member.nonempty initial).1.get i)).1 draw R hr
  unfold unskippedEstimateSourceWithWork unskippedEstimateReadWithWork
  dsimp only
  rw [h.1]
  exact ⟨rfl, by nlinarith only [h.2]⟩

theorem chooseUnskippedSourceWithWork_eq_cost (members : List Member) (hne : members ≠ [])
    (R : ℕ) (hr : ∀ s i, (draw s i).2 ≤ R) :
    (chooseUnskippedSourceWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).1 =
      (chooseUnskippedReadWithWork source target parent b P exponent Q tau F child initial current
        scales (fun s i => (draw s i).1) members hne).1 ∧
    (chooseUnskippedSourceWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).2 ≤
      (chooseUnskippedReadWithWork source target parent b P exponent Q tau F child initial current
        scales (fun s i => (draw s i).1) members hne).2 * (R + 4) := by
  exact selectGroupWithWork_factor _ _ members hne (R + 4) (by omega)
    (fun member _ => (unskippedEstimateSourceWithWork_eq_cost source target parent b P exponent Q
      tau F child initial current scales draw member R hr).1)
    (fun member _ => (unskippedEstimateSourceWithWork_eq_cost source target parent b P exponent Q
      tau F child initial current scales draw member R hr).2)

theorem sampledGroupActionSourceWithWork_eq_cost (members : List Member) (hne : members ≠ [])
    (R : ℕ) (hr : ∀ s i, (draw s i).2 ≤ R) :
    (sampledGroupActionSourceWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).1 =
      (sampledGroupActionReadWithWork source target parent b P exponent Q tau F child initial current
        scales (fun s i => (draw s i).1) members hne).1 ∧
    (sampledGroupActionSourceWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).2 ≤
      (sampledGroupActionReadWithWork source target parent b P exponent Q tau F child initial current
        scales (fun s i => (draw s i).1) members hne).2 * (R + 4) := by
  have h := chooseUnskippedSourceWithWork_eq_cost source target parent b P exponent Q tau F
    child initial current scales draw members hne R hr
  let finish := fun selected : Member =>
    let rounded := roundedBandReadWithWork exponent b selected.actions selected.nonempty initial
    let result := endpointActionWithWork selected.center rounded.1.get
    (result.1, rounded.2 + result.2)
  change (finish (chooseUnskippedSourceWithWork source target parent b P exponent Q tau F
      child initial current scales draw members hne).1).1 =
      (finish (chooseUnskippedReadWithWork source target parent b P exponent Q tau F
        child initial current scales (fun s i => (draw s i).1) members hne).1).1 ∧ _
  have hf := congrArg finish h.1
  refine ⟨congrArg Prod.fst hf, ?_⟩
  have hcost : (chooseUnskippedSourceWithWork source target parent b P exponent Q tau F
      child initial current scales draw members hne).2 +
      (finish (chooseUnskippedSourceWithWork source target parent b P exponent Q tau F
        child initial current scales draw members hne).1).2 + 3 ≤
      ((chooseUnskippedReadWithWork source target parent b P exponent Q tau F
        child initial current scales (fun s i => (draw s i).1) members hne).2 +
        (finish (chooseUnskippedReadWithWork source target parent b P exponent Q tau F
          child initial current scales (fun s i => (draw s i).1) members hne).1).2 + 3) * (R + 4) := by
    rw [hf]
    nlinarith only [h.2]
  simpa only [sampledGroupActionSourceWithWork, sampledGroupActionReadWithWork, finish,
    Nat.add_assoc] using hcost


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

theorem preparedCellGroupSourceWithWork_eq_cost (cell : ℕ × ℕ) (S : ℕ)
    (hs : ∀ t i, (draw t i).2 ≤ S) :
    (preparedCellGroupSourceWithWork source target parent b P F exponent Q hb hP tau a
      parentInitial child initial current R C hr hi raw hraw draw cell).1 =
      (preparedCellGroupReadWithWork source target parent b P F exponent Q hb hP tau a
        parentInitial child initial current R C hr hi raw hraw (fun t i => (draw t i).1) cell).1 ∧
    (preparedCellGroupSourceWithWork source target parent b P F exponent Q hb hP tau a
      parentInitial child initial current R C hr hi raw hraw draw cell).2 ≤
      (preparedCellGroupReadWithWork source target parent b P F exponent Q hb hP tau a
        parentInitial child initial current R C hr hi raw hraw (fun t i => (draw t i).1) cell).2 * (S + 4) := by
  let centers := cellCentersReadWithWork P F b a (inversePowerTwo exponent) parentInitial cell
  let members := filterMapWithWork
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
      child initial R C hr hi) centers.1
  unfold preparedCellGroupSourceWithWork preparedCellGroupReadWithWork
  dsimp only
  split_ifs with hempty
  · exact ⟨rfl, by dsimp only; nlinarith only [Nat.zero_le S]⟩
  · have h := sampledGroupActionSourceWithWork_eq_cost source target parent b P exponent Q tau (nat F)
      (fun i q => (child i q).1) initial current (indexedGroupScales raw M b (nat F).value hraw)
      (fun t j => draw t (Fin.cast (congrArg (groupSampleCount M Q b)
        (indexedGroupScales_value raw M b (nat F).value hraw t)) j)) members.1 hempty S
      (fun t j => hs t _)
    dsimp only [dyadicSampledGroupActionReadWithWork]
    rw [h.1]
    exact ⟨rfl, by nlinarith only [h.2]⟩

end Cell
end EditApproximation.BinaryFraction

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalGroupReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical query's outer whole-cell loops use the same dyadic
scales and exact Fin-count draws, with explicit initial-table lookups. -/

namespace EditApproximation
namespace BinaryFraction

section Local
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ)
  (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)

theorem preparedComputedCellReadWithWork_eq (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : cellScaleDraw M b Q (nat F).value) (cell : ℕ × ℕ)
    (hp : ∀ r, (parentInitial r).2 ≤ R) (hcurrent : ∀ i q, (current i q).2 ≤ R) :
    (preparedComputedCellReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb hb draw cell).1 =
    (preparedComputedCellGroupWithWork source target parent b P F exponent Q eM eb eF hM hb hF hP
      tau a (fun r => (parentInitial r).1) (fun i q => (child i q).1)
      (fun i q => (initial i q).1) (fun i q => (current i q).1) draw cell).1 := by
  have h := preparedCellGroupReadWithWork_eq source target parent b P F exponent Q
    (by rw [hb]; exact Nat.two_pow_pos eb) hP tau a parentInitial child initial current
    R R hc hi (groupScalesWithWork eM eb eF).1
    (computedGroupScales_value M b F eM eb eF hM hb hF) draw cell R R hp hcurrent
  simpa only [preparedComputedCellReadWithWork, preparedComputedCellGroupWithWork] using h

theorem preparedLocalGroupScaleReadWithWork_eq (eb : ℕ)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length)
    (hp : ∀ r, (parentInitial r).2 ≤ R) (hcurrent : ∀ i q, (current i q).2 ≤ R) :
    (preparedLocalGroupScaleReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi eb draw query).1 =
    (preparedLocalGroupScaleWithWork source target parent P F exponent Q eM eF eb hM hF hP tau a
      (fun r => (parentInitial r).1) (fun i q => (child i q).1)
      (fun i q => (initial i q).1) (fun i q => (current i q).1) draw query).1 := by
  simp only [preparedLocalGroupScaleReadWithWork, preparedLocalGroupScaleWithWork,
    filterMapWithWork_value]
  apply List.filterMap_congr
  intro cell _
  have h := preparedComputedCellReadWithWork_eq source target parent P F exponent Q eM eF hM hF hP
    tau a parentInitial child initial current R hc hi (2 ^ eb) eb rfl
    (Eq.mpr (congrArg (cellScaleDraw M (2 ^ eb) Q) (nat_value F)) (draw (2 ^ eb) cell))
    cell hp hcurrent
  simpa only using h

theorem preparedLocalCellGroupsReadWithWork_eq (N : ℕ)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length)
    (hp : ∀ r, (parentInitial r).2 ≤ R) (hcurrent : ∀ i q, (current i q).2 ≤ R) :
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
  · have h := preparedLocalGroupScaleReadWithWork_eq source target parent P F exponent Q eM eF hM hF hP
      tau a parentInitial child initial current R hc hi eb draw query hp hcurrent
    simpa only using h
  · rfl

end Local
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalGroupSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation





private theorem cellScaleReadDraw_cast_plain (M b Q : ℕ) (f g : ℚ) (h : f = g)
    (draw : cellScaleReadDraw M b Q g) :
    (fun t i => ((Eq.mpr (congrArg (cellScaleReadDraw M b Q) h) draw) t i).1) =
      Eq.mpr (congrArg (BinaryFraction.cellScaleDraw M b Q) h) (fun t i => (draw t i).1) := by
  cases h
  rfl

private theorem cellScaleReadDraw_cast_bound (M b Q : ℕ) (f g : ℚ) (h : f = g)
    (draw : cellScaleReadDraw M b Q g) (S : ℕ) (hs : ∀ t i, (draw t i).2 ≤ S) :
    ∀ t i, ((Eq.mpr (congrArg (cellScaleReadDraw M b Q) h) draw) t i).2 ≤ S := by
  cases h
  exact hs

namespace BinaryFraction
section Local
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ)
  (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)

theorem preparedComputedCellSourceWithWork_eq_cost (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → Fin M × ℕ)
    (cell : ℕ × ℕ) (S : ℕ) (hs : ∀ t i, (draw t i).2 ≤ S) :
    (preparedComputedCellSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb hb draw cell).1 =
      (preparedComputedCellReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi b eb hb (fun t i => (draw t i).1) cell).1 ∧
    (preparedComputedCellSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb hb draw cell).2 ≤
      (preparedComputedCellReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi b eb hb (fun t i => (draw t i).1) cell).2 * (S + 4) := by
  have h := preparedCellGroupSourceWithWork_eq_cost source target parent b P F exponent Q
    (by rw [hb]; exact Nat.two_pow_pos eb) hP tau a parentInitial child initial current R R hc hi
    (groupScalesWithWork eM eb eF).1 (computedGroupScales_value M b F eM eb eF hM hb hF)
    draw cell S hs
  unfold preparedComputedCellSourceWithWork preparedComputedCellReadWithWork
  dsimp only
  rw [h.1]
  exact ⟨rfl, by nlinarith only [h.2]⟩

private theorem add_source_cost (u v read plain S : ℕ) (h : read ≤ plain * (S + 4)) :
    u + read + v ≤ (u + plain + v) * (S + 4) := by
  have hconst : u + v ≤ (u + v) * (S + 4) :=
    Nat.le_mul_of_pos_right _ (by omega)
  calc
    u + read + v ≤ u + plain * (S + 4) + v := by omega
    _ = plain * (S + 4) + (u + v) := by omega
    _ ≤ plain * (S + 4) + (u + v) * (S + 4) := Nat.add_le_add_left hconst _
    _ = (u + plain + v) * (S + 4) := by ring

private theorem computedCellSource_cast_cost (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : cellScaleReadDraw M b Q F) (cell : ℕ × ℕ) (S : ℕ)
    (hs : ∀ t i, (draw t i).2 ≤ S) :
    let castDraw := Eq.mpr (congrArg (cellScaleReadDraw M b Q) (nat_value F)) draw
    let plainDraw := Eq.mpr (congrArg (cellScaleDraw M b Q) (nat_value F)) (fun t i => (draw t i).1)
    (preparedComputedCellSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb hb castDraw cell).1 =
      (preparedComputedCellReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi b eb hb plainDraw cell).1 ∧
    (preparedComputedCellSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb hb castDraw cell).2 ≤
      (preparedComputedCellReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi b eb hb plainDraw cell).2 * (S + 4) := by
  dsimp only
  have h := preparedComputedCellSourceWithWork_eq_cost source target parent P F exponent Q eM eF
    hM hF hP tau a parentInitial child initial current R hc hi b eb hb
    (Eq.mpr (congrArg (cellScaleReadDraw M b Q) (nat_value F)) draw) cell S
    (cellScaleReadDraw_cast_bound M b Q _ _ (nat_value F) draw S hs)
  rw [cellScaleReadDraw_cast_plain M b Q _ _ (nat_value F) draw] at h
  exact h

theorem preparedLocalGroupScaleSourceWithWork_eq_cost_on (eb : ℕ)
    (draw : CellGroupReadDraws M F Q) (query : TargetInterval target.length)
    (S : ℕ) (hs : ∀ cell ∈ (targetCellsWithWork
      (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
      (bitWordValue (naturalCeilingWithWork (parentInitial query).1).1) query).1,
      ∀ t i, (draw (2 ^ eb) cell t i).2 ≤ S) :
    (preparedLocalGroupScaleSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi eb draw query).1 =
      (preparedLocalGroupScaleReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi eb (fun b cell t i => (draw b cell t i).1) query).1 ∧
    (preparedLocalGroupScaleSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi eb draw query).2 ≤
      (preparedLocalGroupScaleReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi eb (fun b cell t i => (draw b cell t i).1) query).2 * (S + 4) := by
  let b := 2 ^ eb
  let drawn (cell : ℕ × ℕ) : cellScaleReadDraw M b Q (nat F).value :=
    Eq.mpr (congrArg (cellScaleReadDraw M b Q) (nat_value F)) (draw b cell)
  let cells := targetCellsWithWork (canonicalMulWithWork (inversePowerTwo exponent) (nat b)).1
    (bitWordValue (naturalCeilingWithWork (parentInitial query).1).1) query
  let read := fun cell => preparedComputedCellSourceWithWork source target parent P F exponent Q
    eM eF hM hF hP tau a parentInitial child initial current R hc hi b eb rfl (drawn cell) cell
  let plain := fun cell => preparedComputedCellReadWithWork source target parent P F exponent Q
    eM eF hM hF hP tau a parentInitial child initial current R hc hi b eb rfl
      (Eq.mpr (congrArg (cellScaleDraw M b Q) (nat_value F))
        (fun t i => (draw b cell t i).1)) cell
  have one (cell : ℕ × ℕ) (hcell : cell ∈ cells.1) :
      (read cell).1 = (plain cell).1 ∧ (read cell).2 ≤ (plain cell).2 * (S + 4) := by
    simpa only [read, plain, drawn] using
      computedCellSource_cast_cost source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi b eb rfl (draw b cell) cell S (hs cell hcell)
  have h := filterMapWithWork_factor read plain cells.1 (S + 4) (by omega)
    (fun cell hcell => (one cell hcell).1) (fun cell hcell => (one cell hcell).2)
  have hcost :
      (parentInitial query).2 + (canonicalMulWithWork (inversePowerTwo exponent) (nat b)).2 +
        (naturalCeilingWithWork (parentInitial query).1).2 + cells.2 +
        (filterMapWithWork read cells.1).2 + eb + 4 ≤
      ((parentInitial query).2 + (canonicalMulWithWork (inversePowerTwo exponent) (nat b)).2 +
        (naturalCeilingWithWork (parentInitial query).1).2 + cells.2 +
        (filterMapWithWork plain cells.1).2 + eb + 4) * (S + 4) := by
    simpa only [Nat.add_assoc] using add_source_cost
      ((parentInitial query).2 + (canonicalMulWithWork (inversePowerTwo exponent) (nat b)).2 +
        (naturalCeilingWithWork (parentInitial query).1).2 + cells.2)
      (eb + 4) (filterMapWithWork read cells.1).2 (filterMapWithWork plain cells.1).2 S h.2
  simpa only [preparedLocalGroupScaleSourceWithWork, preparedLocalGroupScaleReadWithWork,
    b, drawn, cells, read, plain] using And.intro h.1 hcost

theorem preparedLocalCellGroupsSourceWithWork_eq_cost_on (N : ℕ)
    (draw : CellGroupReadDraws M F Q) (query : TargetInterval target.length)
    (S : ℕ)
    (hs : ∀ eb ∈ List.range (max 1 N.bits.length),
      (refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query).1).1 = true →
      ∀ cell ∈ (targetCellsWithWork
        (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
        (bitWordValue (naturalCeilingWithWork (parentInitial query).1).1) query).1,
      ∀ t i, (draw (2 ^ eb) cell t i).2 ≤ S) :
    (preparedLocalCellGroupsSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi N draw query).1 =
      (preparedLocalCellGroupsReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi N (fun b cell t i => (draw b cell t i).1) query).1 ∧
    (preparedLocalCellGroupsSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi N draw query).2 ≤
      (preparedLocalCellGroupsReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi N (fun b cell t i => (draw b cell t i).1) query).2 * (S + 4) := by
  let read := fun eb =>
    let guard := refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query).1
    if guard.1 then
      let selected := preparedLocalGroupScaleSourceWithWork source target parent P F exponent Q eM eF
        hM hF hP tau a parentInitial child initial current R hc hi eb draw query
      (selected.1, guard.2 + selected.2 + eb + 4)
    else ([], guard.2 + eb + 4)
  let plain := fun eb =>
    let guard := refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query).1
    if guard.1 then
      let selected := preparedLocalGroupScaleReadWithWork source target parent P F exponent Q eM eF
        hM hF hP tau a parentInitial child initial current R hc hi eb
        (fun b cell t i => (draw b cell t i).1) query
      (selected.1, guard.2 + selected.2 + eb + 4)
    else ([], guard.2 + eb + 4)
  have one (eb : ℕ) (heb : eb ∈ List.range (max 1 N.bits.length)) : (read eb).1 = (plain eb).1 ∧ (read eb).2 ≤ (plain eb).2 * (S + 4) := by
    dsimp only [read, plain]
    split_ifs with hguard
    · have h := preparedLocalGroupScaleSourceWithWork_eq_cost_on source target parent P F exponent Q
        eM eF hM hF hP tau a parentInitial child initial current R hc hi eb draw query S (hs eb heb hguard)
      have hcost := add_source_cost
        (refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query).1).2 (eb + 4)
        (preparedLocalGroupScaleSourceWithWork source target parent P F exponent Q eM eF
          hM hF hP tau a parentInitial child initial current R hc hi eb draw query).2
        (preparedLocalGroupScaleReadWithWork source target parent P F exponent Q eM eF
          hM hF hP tau a parentInitial child initial current R hc hi eb
          (fun b cell t i => (draw b cell t i).1) query).2 S h.2
      simpa only [Nat.add_assoc] using And.intro h.1 hcost
    · have hvalue := Eq.refl ([] : List (BinaryBellmanAction (TargetInterval target.length)
        (Fin M × TargetInterval target.length) M))
      have hcost := Nat.le_mul_of_pos_right
        ((refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query).1).2 + eb + 4)
        (by omega : 0 < S + 4)
      simpa only using And.intro hvalue hcost
  have h := arithmeticFlatMapWithWork_factor read plain (List.range (max 1 N.bits.length))
    (S + 4) (by omega) (fun eb heb => (one eb heb).1) (fun eb heb => (one eb heb).2)
  have hcost :
      (parentInitial query).2 + (arithmeticFlatMapWithWork read (List.range (max 1 N.bits.length))).2 +
        max 1 N.bits.length + N.bits.length + 2 ≤
      ((parentInitial query).2 + (arithmeticFlatMapWithWork plain (List.range (max 1 N.bits.length))).2 +
        max 1 N.bits.length + N.bits.length + 2) * (S + 4) := by
    simpa only [Nat.add_assoc] using add_source_cost (parentInitial query).2
      (max 1 N.bits.length + N.bits.length + 2)
      (arithmeticFlatMapWithWork read (List.range (max 1 N.bits.length))).2
      (arithmeticFlatMapWithWork plain (List.range (max 1 N.bits.length))).2 S h.2
  simpa only [preparedLocalCellGroupsSourceWithWork, preparedLocalCellGroupsReadWithWork,
    read, plain] using And.intro h.1 hcost

end Local
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryOuterReadCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The outer local loops preserve the same lookup factor, including
initial-value reads at the query and at rounded representative centers. -/

namespace EditApproximation
namespace BinaryFraction

theorem cost_replace_with_read (a c old new r R : ℕ) (hc : c ≤ a * tableReadFactor R)
    (hr : r ≤ R) (ha : a + 1 ≤ old) (hn : new + a ≤ old + c + r) :
    new ≤ old * tableReadFactor R := by
  have hK : R + 1 ≤ tableReadFactor R := by unfold tableReadFactor; omega
  have h := cost_factor_with_read a c (old - a) r R (tableReadFactor R)
    hc hr (by omega) hK
  have he : a + (old - a) = old := by omega
  rw [he] at h
  exact (by omega : new ≤ r + c + (old - a)).trans h

section Group
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ)
  (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)

theorem preparedComputedCellReadWithWork_factor (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : cellScaleDraw M b Q (nat F).value) (cell : ℕ × ℕ)
    (hp : ∀ r, (parentInitial r).2 ≤ R) (hcurrent : ∀ i q, (current i q).2 ≤ R) :
    (preparedComputedCellReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb hb draw cell).2 ≤
      (preparedComputedCellGroupWithWork source target parent b P F exponent Q eM eb eF hM hb hF hP
        tau a (fun r => (parentInitial r).1) (fun i q => (child i q).1)
        (fun i q => (initial i q).1) (fun i q => (current i q).1) draw cell).2 * tableReadFactor R := by
  have h := preparedCellGroupReadWithWork_factor source target parent b P F exponent Q
    (by rw [hb]; exact Nat.two_pow_pos eb) hP tau a parentInitial child initial current
    R hc hi (groupScalesWithWork eM eb eF).1
    (computedGroupScales_value M b F eM eb eF hM hb hF) draw cell hp hcurrent
  unfold preparedComputedCellReadWithWork preparedComputedCellGroupWithWork
  dsimp only
  apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R) <;> omega

theorem preparedLocalGroupScaleReadWithWork_factor (eb : ℕ)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length)
    (hp : ∀ r, (parentInitial r).2 ≤ R) (hcurrent : ∀ i q, (current i q).2 ≤ R) :
    (preparedLocalGroupScaleReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi eb draw query).2 ≤
      (preparedLocalGroupScaleWithWork source target parent P F exponent Q eM eF eb hM hF hP tau a
        (fun r => (parentInitial r).1) (fun i q => (child i q).1)
        (fun i q => (initial i q).1) (fun i q => (current i q).1) draw query).2 * tableReadFactor R := by
  have hs := filterMapWithWork_factor
    (fun cell => preparedComputedCellReadWithWork source target parent P F exponent Q eM eF
      hM hF hP tau a parentInitial child initial current R hc hi (2 ^ eb) eb rfl
      (Eq.mpr (congrArg (cellScaleDraw M (2 ^ eb) Q) (nat_value F)) (draw (2 ^ eb) cell)) cell)
    (fun cell => preparedComputedCellGroupWithWork source target parent (2 ^ eb) P F exponent Q eM eb eF
      hM rfl hF hP tau a (fun r => (parentInitial r).1) (fun i q => (child i q).1)
      (fun i q => (initial i q).1) (fun i q => (current i q).1)
      (Eq.mpr (congrArg (cellScaleDraw M (2 ^ eb) Q) (nat_value F)) (draw (2 ^ eb) cell)) cell)
    (targetCellsWithWork (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
      (bitWordValue (naturalCeilingWithWork (parentInitial query).1).1) query).1
    (tableReadFactor R) (tableReadFactor_pos R)
    (fun cell _ => preparedComputedCellReadWithWork_eq source target parent P F exponent Q eM eF
      hM hF hP tau a parentInitial child initial current R hc hi _ eb rfl _ cell hp hcurrent)
    (fun cell _ => preparedComputedCellReadWithWork_factor source target parent P F exponent Q eM eF
      hM hF hP tau a parentInitial child initial current R hc hi _ eb rfl _ cell hp hcurrent)
  unfold preparedLocalGroupScaleReadWithWork preparedLocalGroupScaleWithWork
  dsimp only
  apply cost_replace_with_read _ _ _ _ (parentInitial query).2 R hs.2 (hp query) <;> omega

theorem preparedLocalCellGroupsReadWithWork_factor (N : ℕ)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length)
    (hp : ∀ r, (parentInitial r).2 ≤ R) (hcurrent : ∀ i q, (current i q).2 ≤ R) :
    (preparedLocalCellGroupsReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi N draw query).2 ≤
      (preparedLocalCellGroupsWithWork source target parent N P F exponent Q eM eF hM hF hP tau a
        (fun r => (parentInitial r).1) (fun i q => (child i q).1)
        (fun i q => (initial i q).1) (fun i q => (current i q).1) draw query).2 * tableReadFactor R := by
  let first := fun eb =>
    let guard := refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query).1
    if guard.1 then
      let selected := preparedLocalGroupScaleReadWithWork source target parent P F exponent Q eM eF
        hM hF hP tau a parentInitial child initial current R hc hi eb draw query
      (selected.1, guard.2 + selected.2 + eb + 4)
    else ([], guard.2 + eb + 4)
  let second := fun eb =>
    let guard := refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query).1
    if guard.1 then
      let selected := preparedLocalGroupScaleWithWork source target parent P F exponent Q eM eF eb
        hM hF hP tau a (fun r => (parentInitial r).1) (fun i q => (child i q).1)
        (fun i q => (initial i q).1) (fun i q => (current i q).1) draw query
      (selected.1, guard.2 + selected.2 + eb + 4)
    else ([], guard.2 + eb + 4)
  have h := arithmeticFlatMapWithWork_factor first second (List.range (max 1 N.bits.length))
    (tableReadFactor R) (tableReadFactor_pos R) (by
      intro eb _
      dsimp only [first, second]
      split_ifs
      · have heq := preparedLocalGroupScaleReadWithWork_eq source target parent P F exponent Q eM eF
          hM hF hP tau a parentInitial child initial current R hc hi eb draw query hp hcurrent
        simpa only using heq
      · rfl) (by
      intro eb _
      dsimp only [first, second]
      split_ifs
      · have hs := preparedLocalGroupScaleReadWithWork_factor source target parent P F exponent Q eM eF
          hM hF hP tau a parentInitial child initial current R hc hi eb draw query hp hcurrent
        apply cost_replace_factor _ _ _ _ _ hs (tableReadFactor_pos R) <;> omega
      · exact Nat.le_mul_of_pos_right _ (by have := tableReadFactor_pos R; omega))
  change (parentInitial query).2 + (arithmeticFlatMapWithWork first _).2 + _ + _ + 2 ≤
    ((arithmeticFlatMapWithWork second _).2 + _ + _ + 2) * tableReadFactor R
  apply cost_replace_with_read _ _ _ _ (parentInitial query).2 R h.2 (hp query) <;> omega

end Group

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedListBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal candidate counts of the three local loops, on every seed. -/

namespace EditApproximation
namespace BinaryFraction

theorem dyadicScales_length_bits (N : ℕ) : (dyadicScales N).length = max 1 N.bits.length := by
  have h := congrArg List.length (dyadicScalesWithWork_value N)
  simpa only [dyadicScalesWithWork, arithmeticMapWithWork_value, List.length_map,
    List.length_range] using h.symm

theorem preparedLocalCellGroupsWithWork_length_le {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q eM eF B : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P) (tau a : BinaryFraction)
    (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length)
    (hN : Nat.size N ≤ B) (hw : 0 ≤ (parentInitial query).value) :
    (preparedLocalCellGroupsWithWork source target parent N P F exponent Q eM eF hM hF hP
      tau a parentInitial child initial current draw query).1.length ≤
      (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 := by
  have hv := congrArg List.length (preparedLocalCellGroupsWithWork_value source target parent
    N P F exponent Q eM eF hM hF hP tau a parentInitial child initial current draw query)
  rw [List.length_map] at hv
  rw [hv]
  apply (localCellGroupActions_length source target parent N P F exponent Q tau.value a.value
    (fun r => (parentInitial r).value) (fun i r => (child i r).value)
    (fun i r => (initial i r).value) (fun i r => (current i r).value) draw query
    (by rw [hF]; exact Nat.one_le_two_pow) hw).trans
  apply Nat.mul_le_mul_right
  apply (List.length_filter_le _ _).trans
  rw [dyadicScales_length_bits, Nat.size_eq_bits_len]
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySourceSelectorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete selector bounds with table and scalar-source reads. The
source-cost premises range only over the guards and cells actually visited. -/

namespace EditApproximation.BinaryFraction
section Selectors
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF B E S : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (old current : Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (history : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (t : ℕ) (draw : CellGroupReadDraws M F Q)
  (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
  (q : TargetInterval target.length)
  (hb : PreparedKernelInputBounds (nx := source.length) N P F exponent H Q eM eF B E S t
    tau a eta kappa delta (fun r => (parentInitial r).1)
    (fun i r => (child i r).1) (fun i r => (initial i r).1)
    (fun s => (old s).1) (fun s => (current s).1) (fun s i => (history s i).1)
    (fun b r => (integer b r).1))
  (hp : ∀ r, (parentInitial r).2 ≤ R)

include hb hp in
theorem preparedLocalCellGroupsSourceWithWork_bounds_oai (hPdyadic : ∃ j : ℕ, P = 2 ^ j)
    (hn : ∀ input, (current input).2 ≤ R) (D : ℕ)
    (hd : ∀ eb ∈ List.range (max 1 N.bits.length),
      (refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial q).1).1 = true →
      ∀ cell ∈ (targetCellsWithWork
        (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
        (bitWordValue (naturalCeilingWithWork (parentInitial q).1).1) q).1,
      ∀ scale sample, (draw (2 ^ eb) cell scale sample).2 ≤ D) :
    let selected := preparedLocalCellGroupsSourceWithWork source target parent P F exponent Q eM eF
      hM hF hP tau a parentInitial child initial (fun i r => current (i, r)) R hc hi N draw q
    selected.1.length ≤ (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 ∧
    selected.2 ≤ preparedLocalGroupsBitBudget N M P F exponent eM eF B * tableReadFactor R * (D + 4) := by
  have hs := preparedLocalCellGroupsSourceWithWork_eq_cost_on source target parent P F exponent Q eM eF
    hM hF hP tau a parentInitial child initial (fun i r => current (i, r)) R hc hi N draw q D hd
  have heq := preparedLocalCellGroupsReadWithWork_eq source target parent P F exponent Q eM eF
    hM hF hP tau a parentInitial child initial (fun i r => current (i, r)) R hc hi N
    (fun b cell scale sample => (draw b cell scale sample).1) q hp (fun i r => hn (i, r))
  have hr := preparedLocalCellGroupsReadWithWork_factor source target parent P F exponent Q eM eF
    hM hF hP tau a parentInitial child initial (fun i r => current (i, r)) R hc hi N
    (fun b cell scale sample => (draw b cell scale sample).1) q hp (fun i r => hn (i, r))
  have hcost := preparedLocalCellGroupsWithWork_cost source target parent N P F exponent Q eM eF B hM hF hP
    tau a (fun r => (parentInitial r).1) (fun i r => (child i r).1) (fun i r => (initial i r).1)
    (fun i r => (current (i, r)).1) (fun b cell scale sample => (draw b cell scale sample).1) q
    (by have := hb.largeBits; omega) hb.inputSize hb.sourceSize hb.targetSize hb.aritySize hb.sampleSize
    hb.precisionSize hb.factorSize hb.thetaSize hb.scaleSizes hb.tauSize hb.factorWidth hb.parentSize
    hb.massSize hb.initialSize (fun i r => hb.currentSize (i, r)) (hb.parentNonneg q) hPdyadic
  constructor
  · rw [hs.1, heq]
    exact preparedLocalCellGroupsWithWork_length_le source target parent N P F exponent Q eM eF B
      hM hF hP tau a (fun r => (parentInitial r).1) (fun i r => (child i r).1)
      (fun i r => (initial i r).1) (fun i r => (current (i, r)).1)
      (fun b cell scale sample => (draw b cell scale sample).1) q hb.inputSize (hb.parentNonneg q)
  · exact hs.2.trans (Nat.mul_le_mul_right (D + 4)
      (hr.trans (Nat.mul_le_mul_right (tableReadFactor R) hcost)))

end Selectors
end EditApproximation.BinaryFraction

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWork_bounds_oai.{u_1} := @OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWork_bounds_oai.{u_1}
