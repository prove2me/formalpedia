-- Prove2me | solution 1 for OAI.EditApproximation.BinaryFraction.querySharedCellInputsWithWork_value
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:21:53.70768+00:00
-- url     : https://prove2.me/submissions/a6e99080-1235-4342-9108-1d17576033b1

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
import Definitions.Def_OAIQ361V3Ea000

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySharedGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Boolean endpoint enumeration for the whole-cell shared-read cover.
The inner interval is centered at each computed left endpoint plus the
child length, exactly as in the published query's gap guard. -/

namespace EditApproximation



namespace BinaryFraction



theorem queryGroupRoundedStatesWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b exponent : ℕ) (cell : ℕ × ℕ)
    (i : Fin M) (h : BinaryFraction) :
    (queryGroupRoundedStatesWithWork (ny := target.length) parent b exponent cell i h).1 =
      groupRoundedStateList source target parent b exponent cell i h.value := by
  unfold queryGroupRoundedStatesWithWork
  dsimp only
  rw [queryGapStatesWithWork_value _ _ _ _ _ _ (roundedSpacingWithWork_pos _ _)]
  simp only [roundedSpacingWithWork_value, sourceChildWithWork_value, saturatingSubtractWithWork_value,
    canonicalMulWithWork_value, nat_value, naturalFloorWithWork_value, inversePowerTwo_value,
    binaryNaturalAddWithWork_value, binaryNaturalMulWithWork_value, naturalCeilingWithWork_value,
    groupRoundedStateList, groupRoundSpacing,
    substring_length source _ _ (sourceChild parent i).valid]
  simp only [Nat.cast_ofNat, mul_assoc]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryGroupInputs
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryNaturalLEWithWork_value _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A shared estimator requests every child when its exact sample count
equals the arity; otherwise it requests the sampled child labels. The
Boolean test and each draw-table lookup are included in the counter. -/

namespace EditApproximation
namespace BinaryFraction



theorem queryGroupLabelsWithWork_value (M Q b : ℕ) (h : BinaryFraction)
    (draw : Fin (groupSampleCount M Q b h.value) → Fin M × ℕ) :
    (queryGroupLabelsWithWork M Q b h draw).1.toFinset =
      groupQueriedChildLabels M Q b h.value (fun i => (draw i).1) := by
  have ht : (naturalEqualWithWork (bitWordValue (groupSampleCountWithWork M Q b h).1) M).1 = true ↔
      groupSampleCount M Q b h.value = M := by
    rw [naturalEqualWithWork_value, groupSampleCountWithWork_value]
  unfold queryGroupLabelsWithWork groupQueriedChildLabels
  by_cases he : groupSampleCount M Q b h.value = M
  · rw [ite_eq_left (ht.mpr he), ite_eq_left he]
    ext i
    simp
  · rw [ite_eq_right (fun hx => he (ht.mp hx)), ite_eq_right he]
    simp only [arithmeticMapWithWork_value]
    ext i
    simp



theorem queryGroupInputsWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b exponent Q : ℕ) (cell : ℕ × ℕ)
    (h : BinaryFraction) (draw : Fin (groupSampleCount M Q b h.value) → Fin M × ℕ) :
    (queryGroupInputsWithWork (ny := target.length) parent b exponent Q cell h draw).1.toFinset =
      groupCurrentInputCover source target parent b exponent Q cell h.value (fun i => (draw i).1) := by
  have hl := queryGroupLabelsWithWork_value M Q b h draw
  simp only [queryGroupInputsWithWork, arithmeticFlatMapWithWork_value,
    arithmeticMapWithWork_value, queryGroupRoundedStatesWithWork_value source target]
  ext input
  simp only [List.mem_toFinset, List.mem_flatMap, List.mem_map, groupCurrentInputCover,
    Finset.mem_biUnion, Finset.mem_image]
  simp only [← hl, List.mem_toFinset]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySharedInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The shared-current request list is built from counted whole-cell
enumerations and sorted by the original child encoding. -/

namespace EditApproximation



namespace BinaryFraction



theorem queryGroupInputsTransportWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b exponent Q : ℕ) (cell : ℕ × ℕ)
    (word : BinaryFraction) (scale : ℚ) (hv : word.value = scale)
    (draw : Fin (groupSampleCount M Q b scale) → Fin M × ℕ) :
    (queryGroupInputsTransportWithWork (ny := target.length) parent b exponent Q cell word scale hv draw).1.toFinset =
      groupCurrentInputCover source target parent b exponent Q cell scale (fun i => (draw i).1) := by
  subst scale
  exact queryGroupInputsWithWork_value source target parent b exponent Q cell word draw



theorem querySharedCellInputsWithWork_value_oai {α : Type*} (source target : List α)
    (M F Q eM eb eF : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
    (parent : TargetInterval source.length) (exponent : ℕ) (cell : ℕ × ℕ)
    (draw : ∀ scale : Fin (groupDyadicScales M (2 ^ eb) F).length,
      Fin (groupSampleCount M Q (2 ^ eb) (groupDyadicScaleAt M (2 ^ eb) F scale)) → Fin M × ℕ) :
    (querySharedCellInputsWithWork (ny := target.length) M F Q eM eb eF hM hF parent exponent cell draw).1.toFinset =
      Finset.univ.biUnion (fun scale => groupCurrentInputCover source target parent (2 ^ eb) exponent Q cell
        (groupDyadicScaleAt M (2 ^ eb) F scale) (fun sample => (draw scale sample).1)) := by
  simp only [querySharedCellInputsWithWork, arithmeticFlatMapWithWork_value, queryFinRange_value]
  ext input
  simp only [List.mem_toFinset, List.mem_flatMap, List.mem_finRange, true_and,
    Finset.mem_biUnion, Finset.mem_univ]
  apply exists_congr
  intro scale
  rw [← List.mem_toFinset, queryGroupInputsTransportWithWork_value source target]



end BinaryFraction
end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.BinaryFraction.querySharedCellInputsWithWork_value_oai.{u_1} := @OAI.EditApproximation.BinaryFraction.querySharedCellInputsWithWork_value_oai.{u_1}
