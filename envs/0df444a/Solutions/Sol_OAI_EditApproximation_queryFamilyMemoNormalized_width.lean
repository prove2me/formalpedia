-- Prove2me | solution 1 for OAI.EditApproximation.queryFamilyMemoNormalized_width
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:46:33.895888+00:00
-- url     : https://prove2.me/submissions/1bbf8c8f-de56-4e96-a2f7-44b3ad623348

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Nat
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_queryChargedWarmup_refines
import Theorems.Thm_OAI_EditApproximation_queryFamilyBoundedActive_refines
import Theorems.Thm_OAI_EditApproximation_queryPhysicalInitial_refines

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_NumericalWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete numerical representation and arithmetic work

These are integer bit-length and exact rational-operation bounds for the
finite optimizer. They are not a RAM theorem: the costed evaluator below
counts rational arithmetic operations, while bit-operation costs also
require the charged evaluation model used by the surrounding algorithm.
-/

namespace EditApproximation

open Finset

theorem natural_product_bit_length (a b : ℕ) :
    Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  apply Nat.size_le.mpr
  calc
    a * b ≤ a * 2 ^ Nat.size b := Nat.mul_le_mul_left a (Nat.lt_size_self b).le
    _ < 2 ^ Nat.size a * 2 ^ Nat.size b :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) (by positivity)
    _ = 2 ^ (Nat.size a + Nat.size b) := (pow_add _ _ _).symm

theorem natural_power_bit_length (a n : ℕ) :
    Nat.size (a ^ n) ≤ n * Nat.size a + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hmul := natural_product_bit_length (a ^ n) a
    nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_UnreducedRational
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.nat_representation _root_.OAI.EditApproximation.BinaryFraction.representation_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.UnreducedRational.optimizerStep_value _root_.OAI.EditApproximation.UnreducedRational.value_nat _root_.OAI.EditApproximation.UnreducedRational.value_one _root_.OAI.EditApproximation.UnreducedRational.value_pow _root_.OAI.EditApproximation.UnreducedRational.value_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Exact fractions with positive, unreduced denominators. These operations
perform no greatest-common-divisor computation. The representation lemmas
apply to the intermediate fractions, not merely their reduced Rat values. -/

namespace EditApproximation



namespace UnreducedRational

theorem num_abs_le (a : UnreducedRational) (V : ℕ) (hvalue : |a.value| ≤ V) :
    a.num.natAbs ≤ V * a.den := by
  have hscaled := mul_le_mul_of_nonneg_right hvalue
    (show (0 : ℚ) ≤ a.den by exact_mod_cast a.den_pos.le)
  have hnum : |a.value| * (a.den : ℚ) = (a.num.natAbs : ℚ) := by
    unfold value
    rw [abs_div, abs_of_pos (by exact_mod_cast a.den_pos : (0 : ℚ) < a.den)]
    rw [div_mul_cancel₀ _ (by exact_mod_cast a.den_pos.ne' : (a.den : ℚ) ≠ 0)]
    simp [Int.cast_abs]
  rw [hnum] at hscaled
  exact_mod_cast hscaled

theorem storageBits_le (a : UnreducedRational) (V D : ℕ)
    (hvalue : |a.value| ≤ V) (hden : Nat.size a.den ≤ D) :
    a.storageBits ≤ Nat.size V + 2 * D + 1 := by
  have hnum := (Nat.size_le_size (a.num_abs_le V hvalue)).trans
    (natural_product_bit_length V a.den)
  unfold storageBits
  omega

end UnreducedRational

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCanonicalWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.denominatorInteger_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Removing only leading zero bits of an integer word. This is unrelated
to rational reduction: no common divisor is computed. -/

namespace EditApproximation



theorem trimBitWordWithWork_canonical (bits : List Bool) :
    (trimBitWordWithWork bits).1 = (bitWordValue bits).bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    by_cases hzero : bitWordValue bits = 0
    · rw [trimBitWordWithWork, ih, hzero]
      cases bit <;> simp [bitWordValue, hzero]
    · have hnonempty : (bitWordValue bits).bits ≠ [] := by
        intro h
        have hv := bitWordValue_bits (bitWordValue bits)
        rw [h] at hv
        exact hzero hv.symm
      have hvalue : bitWordValue (bit :: bits) = Nat.bit bit (bitWordValue bits) := by
        cases bit <;> simp [bitWordValue, Nat.bit, Nat.add_comm]
      rw [trimBitWordWithWork, ih, ite_eq_right (by simp [hnonempty]), hvalue,
        Nat.bits_append_bit _ _ (fun h => False.elim (hzero h))]

theorem trimBitWordWithWork_length (bits : List Bool) :
    (trimBitWordWithWork bits).1.length = Nat.size (bitWordValue bits) := by
  rw [trimBitWordWithWork_canonical, Nat.size_eq_bits_len]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_CanonicalFractionWork
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_representation _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.UnreducedRational.value_pow _root_.OAI.EditApproximation.UnreducedRational.value_sub _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Fractions retain their unreduced numerator and denominator, but discard
leading zero bits after each operation. This exposes actual storage length
without charging or performing rational normalization. -/

namespace EditApproximation
namespace BinaryFraction



theorem canonicalizeWithWork_width (a : BinaryFraction) :
    (canonicalizeWithWork a).1.width =
      max (Nat.size a.representation.num.natAbs) (Nat.size a.representation.den) := by
  have hnum : a.numerator.value.natAbs = bitWordValue a.numerator.bits := by
    cases h : a.numerator.negative <;> simp [SignedBinary.value, signedMagnitude, h]
  simp only [canonicalizeWithWork, width, trimBitWordWithWork_length, representation, hnum]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalGroupCones
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Cell-keyed shared draws permit direct local group enumeration. The
complete and local finite programs use the same draw at every cell label. -/

namespace EditApproximation

theorem targetCell_of_cellTargetStates {n g : ℕ} {side : ℚ}
    (cell : ℕ × ℕ) (hg : 0 < g) (hside : 0 < side) (r : TargetInterval n)
    (hr : r ∈ cellTargetStates n g side cell) : targetCell side r = cell := by
  have hc := (cellTargetStates_mem cell hg r).mp hr
  apply Prod.ext
  · apply (Nat.floor_eq_iff (div_nonneg (Nat.cast_nonneg _) hside.le)).2
    exact ⟨(le_div_iff₀ hside).2 hc.2.2.1, (div_lt_iff₀ hside).2 hc.2.2.2.1⟩
  · apply (Nat.floor_eq_iff (div_nonneg (Nat.cast_nonneg _) hside.le)).2
    exact ⟨(le_div_iff₀ hside).2 hc.2.2.2.2.1, (div_lt_iff₀ hside).2 hc.2.2.2.2.2⟩

theorem chooseCellGroupAction_center {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial current : Fin M → TargetInterval target.length → ℚ) (cell : ℕ × ℕ)
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (action : PhysicalRationalAction M target.length)
    (hselected : chooseCellGroupAction source target parent b P F exponent Q tau a
      parentInitial child initial current cell draw = some action) :
    action.center ∈ cellRepresentativeStates target.length P F b a parentInitial
      ((2 : ℚ) ^ (-(exponent : ℤ))) cell := by
  unfold chooseCellGroupAction at hselected
  dsimp only at hselected
  split_ifs at hselected with hempty
  have heq := Option.some.inj hselected
  rw [← heq]
  exact (unskippedBandList_mem_iff _ _).mp
    (chooseUnskippedGroup_spec Q current _ hempty draw).1

theorem representativeCells_mem {n N P F b : ℕ} (a theta : ℚ)
    (initial : TargetInterval n → ℚ) (r : TargetInterval n)
    (hr : (b, r) ∈ representativeList N P F a initial) :
    targetCell (theta * b) r ∈ representativeCells N P F b a theta initial := by
  apply List.mem_eraseDups.mpr
  apply List.mem_map.mpr
  exact ⟨(b, r), List.mem_filter.mpr ⟨hr, by simp⟩, rfl⟩



section CellPrograms

variable {α : Type*} {M : ℕ} (source target : List α)
  (parent : TargetInterval source.length) (N P F exponent Q : ℕ) (tau a : ℚ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial current : Fin M → TargetInterval target.length → ℚ)
  (draw : CellGroupDraws M F Q)

local notation "theta" => (2 : ℚ) ^ (-(exponent : ℤ))



theorem cellGroupAction_location (b : ℕ) (hb : b ∈ dyadicScales N) (cell : ℕ × ℕ)
    (action : PhysicalRationalAction M target.length)
    (hselected : chooseCellGroupAction source target parent b P F exponent Q tau a
      parentInitial child initial current cell (draw b cell) = some action) :
    (b, action.center) ∈ representativeList N P F a parentInitial ∧
      targetCell (theta * b) action.center = cell := by
  have hcenter := chooseCellGroupAction_center source target parent b P F exponent Q tau a
    parentInitial child initial current cell (draw b cell) action hselected
  have hrep := cellRepresentativeStates_mem_representatives a parentInitial theta cell action.center hb hcenter
  have hbpos : 0 < b := by
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hb
    positivity
  have hcell := (List.mem_filter.mp hcenter).1
  exact ⟨hrep, targetCell_of_cellTargetStates cell (by unfold seedGridSpacing; omega)
    (by positivity) action.center hcell⟩

theorem localCellGroupActions_subset (q : TargetInterval target.length) :
    ∀ action ∈ localCellGroupActions source target parent N P F exponent Q tau a parentInitial
      child initial current draw q,
      action ∈ completeCellGroupActions source target parent N P F exponent Q tau a parentInitial
        child initial current draw := by
  intro action ha
  obtain ⟨b, hb, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨cell, _, hselected⟩ := List.mem_filterMap.mp ha
  have hb' := (List.mem_filter.mp hb).1
  have hlocation := cellGroupAction_location source target parent N P F exponent Q tau a
    parentInitial child initial current draw b hb' cell action hselected
  have hcell := representativeCells_mem a theta parentInitial action.center hlocation.1
  rw [hlocation.2] at hcell
  exact List.mem_flatMap.mpr ⟨b, hb', List.mem_filterMap.mpr ⟨cell, hcell, hselected⟩⟩

theorem completeCellGroupActions_wide :
    ∀ action ∈ completeCellGroupActions source target parent N P F exponent Q tau a parentInitial
      child initial current draw,
      action ∈ rationalActualWideActions parent (representativeList N P F a parentInitial) P := by
  intro action ha
  obtain ⟨b, hb, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨cell, _, hselected⟩ := List.mem_filterMap.mp ha
  exact chooseCellGroupAction_wide_mem source target parent N b P F exponent Q tau a parentInitial
    child initial current cell (draw b cell) hb action hselected

end CellPrograms

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryFixedDenominator
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Exact cache-value compression to a prescribed denominator.  It performs
one Boolean multiplication and one Boolean long division, followed only by
leading-zero removal.  No rational gcd or reduced-rational conversion is used. -/

namespace EditApproximation
namespace BinaryFraction

theorem raw_den_dvd_scaled_num (a : BinaryFraction) (D : ℕ) (hD : a.value.den ∣ D) :
    bitWordValue a.denominator ∣ bitWordValue a.numerator.bits * D := by
  have hd : (a.representation.den : ℤ) ≠ 0 := by exact_mod_cast a.representation.den_pos.ne'
  obtain ⟨c, hn, hd'⟩ := Rat.num_den_mk (q := a.value) (n := a.representation.num)
    (d := (a.representation.den : ℤ)) hd (by
      rw [Rat.divInt_eq_div, Int.cast_natCast]
      exact (representation_value a).symm)
  obtain ⟨k, hk⟩ := hD
  have hi : (a.representation.den : ℤ) ∣ a.representation.num * (D : ℤ) := by
    refine ⟨a.value.num * k, ?_⟩
    rw [hn, hd', hk, Nat.cast_mul]
    ring
  have habs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hi)
  have hnum : a.representation.num.natAbs = bitWordValue a.numerator.bits := by
    cases h : a.numerator.negative <;> simp [representation, SignedBinary.value, signedMagnitude, h]
  change bitWordValue a.denominator ∣ (a.representation.num * (D : ℤ)).natAbs at habs
  simpa only [Int.natAbs_mul, Int.natAbs_natCast, hnum] using habs



theorem fixedDenominatorWithWork_value (a : BinaryFraction) (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) (hD : a.value.den ∣ bitWordValue denominator) :
    (fixedDenominatorWithWork a denominator hden).1.value = a.value := by
  let product := bitMulWithWork a.numerator.bits denominator
  let quotient := bitDivModWithWork a.denominator product.1
  have hdvd := raw_den_dvd_scaled_num a (bitWordValue denominator) hD
  have h := bitDivModWithWork_value a.denominator product.1 a.denominator_pos
  have hm : bitWordValue product.1 = bitWordValue a.numerator.bits * bitWordValue denominator :=
    bitMulWithWork_value _ _
  have hmod : bitWordValue quotient.2.1 = 0 := by
    have hz : bitWordValue product.1 % bitWordValue a.denominator = 0 := by
      rw [hm]
      exact Nat.mod_eq_zero_of_dvd hdvd
    rw [h.1, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add] at hz
    simp only [Nat.mod_mod] at hz
    exact (Nat.mod_eq_of_lt h.2).symm.trans hz
  have hq : bitWordValue a.denominator * bitWordValue quotient.1 =
      bitWordValue a.numerator.bits * bitWordValue denominator := by
    have heq := h.1
    change bitWordValue product.1 = bitWordValue a.denominator * bitWordValue quotient.1 + bitWordValue quotient.2.1 at heq
    rw [hmod, Nat.add_zero] at heq
    exact heq.symm.trans hm
  let raw : BinaryFraction := ⟨⟨a.numerator.negative, quotient.1⟩, denominator, hden⟩
  have hc : (canonicalizeWithWork raw).1.value = raw.value := by
    rw [← representation_value, canonicalizeWithWork_representation, representation_value]
  change (canonicalizeWithWork raw).1.value = a.value
  rw [hc]
  have hdQ : (bitWordValue a.denominator : ℚ) ≠ 0 := by exact_mod_cast a.denominator_pos.ne'
  have hDQ : (bitWordValue denominator : ℚ) ≠ 0 := by exact_mod_cast hden.ne'
  have hqQ : (bitWordValue a.denominator : ℚ) * bitWordValue quotient.1 =
      (bitWordValue a.numerator.bits : ℚ) * bitWordValue denominator := by exact_mod_cast hq
  cases hs : a.numerator.negative <;>
    simp only [raw, value, SignedBinary.value, signedMagnitude, hs, Bool.false_eq_true,
      ↓reduceIte, Int.cast_natCast, Int.cast_neg] <;>
    apply (div_eq_div_iff hDQ hdQ).mpr <;> nlinarith only [hqQ]

theorem fixedDenominatorWithWork_den (a : BinaryFraction) (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) :
    (fixedDenominatorWithWork a denominator hden).1.representation.den = bitWordValue denominator := by
  unfold fixedDenominatorWithWork
  dsimp only
  rw [canonicalizeWithWork_representation]
  rfl

theorem fixedDenominatorWithWork_width (a : BinaryFraction) (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) (hD : a.value.den ∣ bitWordValue denominator)
    (V B : ℕ) (hv : |a.value| ≤ V) (hB : denominator.length ≤ B) :
    (fixedDenominatorWithWork a denominator hden).1.width ≤ Nat.size V + 2 * B + 1 := by
  let answer := (fixedDenominatorWithWork a denominator hden).1
  have hvalue : |answer.representation.value| ≤ V := by
    rw [representation_value]
    change |(fixedDenominatorWithWork a denominator hden).1.value| ≤ V
    rw [fixedDenominatorWithWork_value a denominator hden hD]
    exact hv
  have hbits : Nat.size answer.representation.den ≤ B := by
    rw [fixedDenominatorWithWork_den]
    exact (Nat.size_le.mpr (bitWordValue_lt_pow_length denominator)).trans hB
  have hstorage := UnreducedRational.storageBits_le answer.representation V B hvalue hbits
  have hwidth : answer.width ≤ answer.representation.storageBits := by
    unfold answer fixedDenominatorWithWork
    dsimp only
    rw [canonicalizeWithWork_width, canonicalizeWithWork_representation]
    unfold UnreducedRational.storageBits
    omega
  exact hwidth.trans hstorage

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPowerStorage
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Construction of a prescribed power denominator uses literal Boolean
multiplication and trimming. The subsequent cache compression therefore has
no uncharged conversion from a natural number to its binary representation. -/

namespace EditApproximation



theorem bitPowerWithWork_length (base : List Bool) (n : ℕ) :
    (bitPowerWithWork base n).1.length = Nat.size (bitWordValue base ^ n) := by
  cases n with
  | zero => simp [bitPowerWithWork]
  | succ n =>
    simp only [bitPowerWithWork, trimBitWordWithWork_length, bitMulWithWork_value,
      bitPowerWithWork_value, pow_succ]

theorem bitPowerWithWork_length_le (base : List Bool) (n B : ℕ) (hB : base.length ≤ B) :
    (bitPowerWithWork base n).1.length ≤ n * B + 1 := by
  rw [bitPowerWithWork_length]
  exact (natural_power_bit_length _ _).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left n
      ((Nat.size_le.mpr (bitWordValue_lt_pow_length base)).trans hB)) 1)

namespace BinaryFraction



theorem powerDenominatorWithWork_value (a : BinaryFraction) (base : List Bool)
    (hbase : 0 < bitWordValue base) (n : ℕ) (hden : a.value.den ∣ bitWordValue base ^ n) :
    (powerDenominatorWithWork a base hbase n).1.value = a.value := by
  apply fixedDenominatorWithWork_value
  simpa only [bitPowerWithWork_value] using hden

theorem powerDenominatorWithWork_width (a : BinaryFraction) (base : List Bool)
    (hbase : 0 < bitWordValue base) (n V B : ℕ) (hB : base.length ≤ B)
    (hden : a.value.den ∣ bitWordValue base ^ n) (hv : |a.value| ≤ V) :
    (powerDenominatorWithWork a base hbase n).1.width ≤ Nat.size V + 2 * (n * B + 1) + 1 := by
  apply fixedDenominatorWithWork_width a (bitPowerWithWork base n).1 _ _ V (n * B + 1)
  · exact hv
  · exact bitPowerWithWork_length_le base n B hB
  · simpa only [bitPowerWithWork_value] using hden

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCachedContinuation
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Cache insertion compresses the actual continuation result by executed
Boolean multiplication and division. Its cost is part of the return
counter; no rational normalization operation is assigned unit cost. -/

namespace EditApproximation
namespace BinaryFraction



theorem finishCachedWithWork_value (raw : BinaryFraction × ℕ) (base : List Bool)
    (hbase : 0 < bitWordValue base) (remaining : ℕ)
    (hden : raw.1.value.den ∣ bitWordValue base ^ remaining) :
    (finishCachedWithWork raw base hbase remaining).1.value = raw.1.value :=
  powerDenominatorWithWork_value raw.1 base hbase remaining hden

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitQuery
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Adaptive queries whose answers are stored binary fractions. Local Boolean
computations appear as explicit charged steps. The simulation relation below
preserves the ordered requests as well as the final value; it does not gather
a rational query's keys in advance. -/

namespace EditApproximation



namespace BitQuery





theorem value_bind {ι α β : Type*} (oracle : ι → BinaryFraction)
    (program : BitQuery ι α) (next : α → BitQuery ι β) :
    (program.bind next).value oracle = (next (program.value oracle)).value oracle := by
  induction program with
  | done result => rfl
  | read key continuation ih => exact ih (oracle key)
  | charge steps continuation ih => exact ih

theorem Refines.value_keys {ι β : Type*} {relation : β → ℚ → Prop}
    {program : BitQuery ι β} {expected : FiniteQuery ι}
    (h : Refines relation program expected) (oracle : ι → BinaryFraction) :
    relation (program.value oracle) (expected.value (fun key => (oracle key).value)) ∧
      program.keys oracle = expected.keys (fun key => (oracle key).value) := by
  induction h with
  | done h => exact ⟨h, rfl⟩
  | read key next expected h ih =>
    exact ⟨(ih (oracle key)).1, congrArg (List.cons key) (ih (oracle key)).2⟩
  | charge steps h ih => exact ih

end BitQuery
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitQueryKeys
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Key tagging and finite-domain restriction preserve the adaptive
reference program. Executed key tests carry their actual Boolean cost. -/

namespace EditApproximation.BitQuery



theorem Refines.mapKeysWithWork {ι κ β : Type*} {relation : β → ℚ → Prop}
    (f : ι → κ × ℕ) (g : ι → κ) (hf : ∀ key, (f key).1 = g key)
    {program : BitQuery ι β} {expected : FiniteQuery ι}
    (h : Refines relation program expected) :
    Refines relation (mapKeysWithWork f program) (FiniteQuery.mapKeys g expected) := by
  induction h with
  | done h => exact .done h
  | charge steps h ih => exact .charge steps ih
  | read key next expected h ih =>
    apply Refines.charge
    change Refines relation (.read (f key).1 _) (.read (g key) _)
    rw [hf key]
    exact .read _ _ _ ih


end EditApproximation.BitQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitQueryOn
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simulation along a fixed reachable oracle. This allows a checked
normalization at the end of a local query: its denominator invariant is
required only for the values that the ranked execution actually reaches. -/

namespace EditApproximation.BitQuery

theorem Refines.onOracle {ι β : Type*} {relation : β → ℚ → Prop}
    {program : BitQuery ι β} {expected : FiniteQuery ι}
    (h : Refines relation program expected) (oracle : ι → BinaryFraction) :
    RefinesOn oracle relation program expected := by
  induction h with
  | done h => exact .done h
  | charge steps _ ih => exact .charge steps ih
  | read key next expected _ ih => exact .read key next expected (ih (oracle key))

theorem RefinesOn.value_keys {ι β : Type*} {oracle : ι → BinaryFraction} {relation : β → ℚ → Prop}
    {program : BitQuery ι β} {expected : FiniteQuery ι}
    (h : RefinesOn oracle relation program expected) :
    relation (program.value oracle) (expected.value (fun key => (oracle key).value)) ∧
      program.keys oracle = expected.keys (fun key => (oracle key).value) := by
  induction h with
  | done h => exact ⟨h, rfl⟩
  | charge steps _ ih => exact ih
  | read key next expected _ ih => exact ⟨ih.1, congrArg (List.cons key) ih.2⟩

theorem RefinesOn.finish {ι : Type*} {oracle : ι → BinaryFraction}
    {program : BitQuery ι BinaryFraction} {expected : FiniteQuery ι}
    (h : RefinesOn oracle (fun word value => word.value = value) program expected)
    (finish : BinaryFraction → BinaryFraction × ℕ)
    (hf : (finish (program.value oracle)).1.value = (program.value oracle).value) :
    RefinesOn oracle (fun word value => word.value = value)
      (program.bind fun word => compute (finish word)) expected := by
  induction h with
  | done h => exact .charge _ (.done (hf.trans h))
  | charge steps _ ih => exact .charge steps (ih hf)
  | read key next expected _ ih => exact .read key _ _ (ih hf)

end EditApproximation.BitQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitQueryNormalize
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Executed cache normalization charges the actual Boolean rescaling.
Its exact-value premise is checked on the reachable local result. -/

namespace EditApproximation.BitQuery



theorem normalize_value {ι : Type*} (program : BitQuery ι BinaryFraction)
    (base : List Bool) (hbase : 0 < bitWordValue base) (remaining : ℕ)
    (oracle : ι → BinaryFraction)
    (hden : (program.value oracle).value.den ∣ bitWordValue base ^ remaining) :
    (normalize program base hbase remaining).value oracle =
      (BinaryFraction.finishCachedWithWork (program.value oracle, 0) base hbase remaining).1 ∧
    ((normalize program base hbase remaining).value oracle).value = (program.value oracle).value := by
  refine ⟨by simp only [normalize, value_bind, compute, value], ?_⟩
  simp only [normalize, value_bind, compute, value]
  exact BinaryFraction.finishCachedWithWork_value _ base hbase remaining hden

theorem RefinesOn.normalize {ι : Type*} {oracle : ι → BinaryFraction}
    {program : BitQuery ι BinaryFraction} {expected : FiniteQuery ι}
    (h : RefinesOn oracle (fun word value => word.value = value) program expected)
    (base : List Bool) (hbase : 0 < bitWordValue base) (remaining : ℕ)
    (hden : (program.value oracle).value.den ∣ bitWordValue base ^ remaining) :
    RefinesOn oracle (fun word value => word.value = value)
      (normalize program base hbase remaining) expected := by
  apply h.finish
  exact BinaryFraction.finishCachedWithWork_value _ base hbase remaining hden

end EditApproximation.BitQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitRankedNormalize
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The denominator condition is used only at the semantic values of
smaller requests.  Strong induction then establishes the actual binary
program's value and normalized trace without assuming its own output. -/

namespace EditApproximation

section Normalize
variable {κ : Type*} (rank : κ → ℕ)
  (raw : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
  (expected : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
  (semantic : κ → ℚ)
  (hrefines : ∀ key, BitQuery.Refines (fun word value => word.value = value) (raw key) (expected key))
  (hbody : ∀ key, (expected key).value (fun child => semantic child.val) = semantic key)
  (base : List Bool) (hbase : 0 < bitWordValue base) (remaining : κ → ℕ)
  (hden : ∀ key, (semantic key).den ∣ bitWordValue base ^ remaining key)



include hrefines hbody hden in
theorem rankedNormalizeBody_correct (key : κ) :
    (rankedBitProgramValue rank (rankedNormalizeBody rank raw base hbase remaining) key).value =
        semantic key ∧
    BitQuery.RefinesOn
      (fun child => rankedBitProgramValue rank (rankedNormalizeBody rank raw base hbase remaining) child.val)
      (fun word value => word.value = value)
      (rankedNormalizeBody rank raw base hbase remaining key) (expected key) := by
  have hall : ∀ level key, rank key = level →
      (rankedBitProgramValue rank (rankedNormalizeBody rank raw base hbase remaining) key).value =
        semantic key ∧
      BitQuery.RefinesOn
        (fun child => rankedBitProgramValue rank (rankedNormalizeBody rank raw base hbase remaining) child.val)
        (fun word value => word.value = value)
        (rankedNormalizeBody rank raw base hbase remaining key) (expected key) := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel
      let oracle := fun child : {child : κ // rank child < rank key} =>
        rankedBitProgramValue rank (rankedNormalizeBody rank raw base hbase remaining) child.val
      have horacle : (fun child => (oracle child).value) = (fun child => semantic child.val) := by
        funext child
        exact (ih (rank child.val) (hlevel ▸ child.property) child.val rfl).1
      have hraw : ((raw key).value oracle).value = semantic key := by
        have hv := ((hrefines key).value_keys oracle).1
        rw [horacle, hbody key] at hv
        exact hv
      have hd : ((raw key).value oracle).value.den ∣ bitWordValue base ^ remaining key := by
        rw [hraw]
        exact hden key
      have hn := ((hrefines key).onOracle oracle).normalize base hbase (remaining key) hd
      refine ⟨?_, hn⟩
      rw [rankedBitProgramValue]
      exact hn.value_keys.1.trans (by rw [horacle]; exact hbody key)
  exact hall (rank key) key rfl


include hrefines hbody hden in
theorem rankedNormalizeBody_width (key : κ) (B V : ℕ)
    (hB : base.length ≤ B) (hV : |semantic key| ≤ (V : ℚ)) :
    (rankedBitProgramValue rank (rankedNormalizeBody rank raw base hbase remaining) key).width ≤
      Nat.size V + 2 * (remaining key * B + 1) + 1 := by
  let oracle := fun child : {child : κ // rank child < rank key} =>
    rankedBitProgramValue rank (rankedNormalizeBody rank raw base hbase remaining) child.val
  have horacle : (fun child => (oracle child).value) = (fun child => semantic child.val) := by
    funext child
    exact (rankedNormalizeBody_correct rank raw expected semantic hrefines hbody base hbase remaining
      hden child.val).1
  have hraw : ((raw key).value oracle).value = semantic key := by
    have hv := ((hrefines key).value_keys oracle).1
    rw [horacle, hbody key] at hv
    exact hv
  have hd : ((raw key).value oracle).value.den ∣ bitWordValue base ^ remaining key := by
    rw [hraw]
    exact hden key
  have hv : |((raw key).value oracle).value| ≤ (V : ℚ) := by rw [hraw]; exact hV
  rw [rankedBitProgramValue]
  change ((BitQuery.normalize (raw key) base hbase (remaining key)).value oracle).width ≤ _
  rw [(BitQuery.normalize_value (raw key) base hbase (remaining key) oracle hd).1]
  exact BinaryFraction.powerDenominatorWithWork_width ((raw key).value oracle) base hbase
    (remaining key) V B hB hd hv

end Normalize
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SourceRankedProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Random source coordinates and recursive table entries share the same
memo evaluator. Source coordinates have rank zero; each table rank is
shifted by one. Consequently repeated source reads reuse their stored draw. -/

namespace EditApproximation

namespace SourceRanked

variable {σ κ : Type*}







 theorem body_value (tableRank : κ → ℕ)
    (tableBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
    (sourceValue : σ → ℚ) (tableValue : κ → ℚ)
    (hbody : ∀ key, (tableBody key).value (Sum.elim sourceValue (fun next => tableValue next.val)) =
      tableValue key) (key : Sum σ κ) :
    (body tableRank tableBody sourceValue key).value
      (fun next => value sourceValue tableValue next.val) = value sourceValue tableValue key := by
  cases key with
  | inl source => rfl
  | inr table =>
    rw [body, FiniteQuery.mapKeys_value]
    have horacle : (fun next => value sourceValue tableValue next.val) ∘ child tableRank table =
        Sum.elim sourceValue (fun next => tableValue next.val) := by
      funext next
      cases next <;> rfl
    rw [horacle]
    exact hbody table

end SourceRanked

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitSourceRanked
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Source draws and table requests share the same concrete binary memo.
Rank-zero sources are stored once; each tagged recursive request pays for
its tag construction before entering the shared dictionary. -/

namespace EditApproximation.SourceRanked

variable {σ κ : Type*}



theorem bitBody_refines (tableRank : κ → ℕ)
    (tableBody : (parent : κ) → BitQuery (Sum σ {key : κ // tableRank key < tableRank parent}) BinaryFraction)
    (expectedBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
    (sourceValue : σ → BinaryFraction × ℕ)
    (hbody : ∀ parent, BitQuery.Refines (fun word value => word.value = value)
      (tableBody parent) (expectedBody parent)) (key : Sum σ κ) :
    BitQuery.Refines (fun word value => word.value = value)
      (bitBody tableRank tableBody sourceValue key)
      (body tableRank expectedBody (fun source => (sourceValue source).1.value) key) := by
  cases key with
  | inl source => exact .charge _ (.done rfl)
  | inr table =>
    exact (hbody table).mapKeysWithWork (fun key => (child tableRank table key, 1))
      (child tableRank table) (fun _ => rfl)

end EditApproximation.SourceRanked

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalOnlineProgram
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Direct online queries use one rounded center per allowed scale. The
integer argument denotes the accepted output of the exact rejection sampler;
reduction modulo the requested range merely makes the finite rule total. -/

namespace EditApproximation

open Finset

theorem localOnlineCandidates_mem {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H : ℕ) (tau a eta kappa : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (children : PhysicalChildTables M target.length) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (q : TargetInterval target.length)
    (action : PhysicalRationalAction M target.length) :
    action ∈ localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      parentInitial child initial children t integer q ↔
    ∃ b, b ∈ dyadicQueryWindow N (parentInitial q) a F ∧
      (b, roundInterval (seedGridSpacing b P) q) ∈ representativeList N P F a parentInitial ∧
      keyedOnlineCandidate source target parent P F exponent H b tau eta kappa child initial
        children t (roundInterval (seedGridSpacing b P) q)
        (integer b (roundInterval (seedGridSpacing b P) q)) = some action := by
  unfold localOnlineCandidates
  constructor
  · intro ha
    obtain ⟨b, hb, hselected⟩ := List.mem_filterMap.mp ha
    dsimp only at hselected
    split_ifs at hselected with heligible
    refine ⟨b, hb, ?_, hselected⟩
    exact representativeList_mem a parentInitial _ (List.mem_filter.mp hb).1
      (roundInterval_on_grid _ q) heligible.1 heligible.2
  · rintro ⟨b, hb, hrep, hselected⟩
    have hc := representativeList_conditions a parentInitial hrep
    apply List.mem_filterMap.mpr
    refine ⟨b, hb, ?_⟩
    dsimp only
    rw [ite_eq_left hc.2.2.2]
    exact hselected

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalDenominator
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual returned values have one additional fixed denominator per tree level. -/

namespace EditApproximation

open Finset

theorem rat_den_add_dvd {D : ℕ} {x y : ℚ} (hx : x.den ∣ D) (hy : y.den ∣ D) :
    (x + y).den ∣ D := (Rat.add_den_dvd_lcm x y).trans (Nat.lcm_dvd hx hy)

theorem rat_den_min_dvd {D : ℕ} {x y : ℚ} (hx : x.den ∣ D) (hy : y.den ∣ D) :
    (min x y).den ∣ D := by
  by_cases h : x ≤ y
  · simpa only [min_eq_left h] using hx
  · simpa only [min_eq_right (le_of_not_ge h)] using hy

theorem rat_den_max_dvd {D : ℕ} {x y : ℚ} (hx : x.den ∣ D) (hy : y.den ∣ D) :
    (max x y).den ∣ D := by
  by_cases h : x ≤ y
  · simpa only [max_eq_right h] using hy
  · simpa only [max_eq_left (le_of_not_ge h)] using hx

theorem rat_den_sum_dvd {ι : Type*} (s : Finset ι) (f : ι → ℚ) (D : ℕ)
    (hf : ∀ i ∈ s, (f i).den ∣ D) : (∑ i ∈ s, f i).den ∣ D := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty, Rat.den_zero, one_dvd]
  | @insert i s hi ih =>
    rw [sum_insert hi]
    exact rat_den_add_dvd (hf i (mem_insert_self _ _))
      (ih fun j hj => hf j (mem_insert_of_mem hj))

theorem rationalMinimum_den_dvd (fallback : ℚ) (values : List ℚ) (D : ℕ)
    (hfallback : fallback.den ∣ D) (hvalues : ∀ v ∈ values, v.den ∣ D) :
    (rationalMinimum fallback values).den ∣ D := by
  induction values with
  | nil => exact hfallback
  | cons v rest ih =>
    exact rat_den_min_dvd (hvalues v (by simp)) (ih fun w hw => hvalues w (by simp [hw]))

theorem rationalActualWideActions_connection_den {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ)
    (action : PhysicalRationalAction M ny)
    (ha : action ∈ rationalActualWideActions parent representatives P) : action.connection.den = 1 := by
  obtain ⟨br, _, hmem⟩ := List.mem_flatMap.mp ha
  obtain ⟨states, _, rfl⟩ := List.mem_map.mp hmem
  exact Rat.den_natCast _

theorem rationalActionValue_den_dvd {Parent Child : Type*} {M D : ℕ}
    (distance : Parent → Parent → ℚ) (L : ℚ) (child : Child → ℚ)
    (q : Parent) (action : RationalBellmanAction Parent Child M)
    (hdistance : (distance q action.center).den = 1) (hL : L.den = 1)
    (ha : action.connection.den = 1) (hchild : ∀ i, (child (action.childState i)).den ∣ D) :
    (rationalActionValue distance L child q action).den ∣ D := by
  unfold rationalActionValue
  apply rat_den_add_dvd
  · apply rat_den_add_dvd
    · have h := Rat.mul_den_dvd L (distance q action.center)
      rw [hL, hdistance, one_mul] at h
      exact h.trans (one_dvd D)
    · rw [ha]
      exact one_dvd D
  · exact rat_den_sum_dvd univ _ D (fun i _ => hchild i)

theorem stageInitial_den_one {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (state : PhysicalEntry M J target.length) :
    (stageInitial source target U N P F A state).den = 1 := by
  have hmin (fallback : ℚ) (values : List ℚ) (hf : fallback.den = 1)
      (hv : ∀ v ∈ values, v.den = 1) : (rationalMinimum fallback values).den = 1 :=
    Nat.eq_one_of_dvd_one (rationalMinimum_den_dvd fallback values 1 (by rw [hf])
      (fun v h => by rw [hv v h]))
  unfold stageInitial physicalInitialTable
  dsimp only
  split_ifs
  · exact Rat.den_natCast _
  · unfold localInitialConeTable
    split_ifs
    · exact Rat.den_zero
    · apply hmin
      · simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
          Rat.den_natCast ((32 * F + 1) * N)
      · intro v hv
        obtain ⟨r, _, rfl⟩ := List.mem_map.mp hv
        unfold initialConeValue scaledSeedValue
        apply Nat.eq_one_of_dvd_one
        apply rat_den_add_dvd
        · apply rat_den_max_dvd
          · simp only [Rat.den_natCast, dvd_refl]
          · have heq : rationalStateGap (physicalSource source state.1) target r =
                (((r.hi : ℤ) - r.lo - (physicalSource source state.1).length : ℤ) : ℚ) := by
              simp only [rationalStateGap, Int.cast_sub, Int.cast_natCast]
            rw [heq, ← Int.cast_abs]
            simp only [Rat.den_intCast, dvd_refl]
        · have heq : (32 * F : ℚ) * targetEndpointDistance state.2 r =
              ((32 * F * targetEndpointDistance state.2 r : ℕ) : ℚ) := by push_cast; rfl
          rw [heq, Rat.den_natCast]

theorem rat_inverse_shift_den_dvd (m : ℕ) (hm : 0 < m) :
    (1 / (1 + 1 / (m : ℚ))).den ∣ m + 1 := by
  have hmp : (0 : ℚ) < m := by exact_mod_cast hm
  have heq : (1 / (1 + 1 / (m : ℚ))) = (m : ℚ) / (m + 1 : ℕ) := by
    push_cast
    field_simp
  rw [heq]
  have h : (((m : ℚ) / (m + 1 : ℕ)).den : ℤ) ∣ (m + 1 : ℕ) := by
    simpa only [Rat.divInt_eq_div, Int.cast_natCast] using Rat.den_dvd (m : ℤ) (m + 1 : ℕ)
  exact Int.natCast_dvd_natCast.mp h

theorem rationalRefinementUpdate_den_dvd (m D : ℕ) (hm : 0 < m)
    (cone : ℚ) (online : Option ℚ) (hcone : cone.den ∣ D)
    (honline : ∀ v, online = some v → v.den ∣ D) :
    (rationalRefinementUpdate (1 / (m : ℚ)) cone online).den ∣ D * (m + 1) := by
  have hstep : D ∣ D * (m + 1) := dvd_mul_right _ _
  cases online with
  | none => exact hcone.trans hstep
  | some v =>
    apply rat_den_min_dvd (hcone.trans hstep)
    apply rat_den_max_dvd _ ((honline v rfl).trans hstep)
    rw [div_eq_mul_one_div]
    exact (Rat.mul_den_dvd cone _).trans (Nat.mul_dvd_mul hcone (rat_inverse_shift_den_dvd m hm))

theorem rationalOnlineMinimum_den_dvd (values : List ℚ) (D : ℕ)
    (hvalues : ∀ v ∈ values, v.den ∣ D) (v : ℚ)
    (heq : rationalOnlineMinimum values = some v) : v.den ∣ D := by
  cases values with
  | nil => cases heq
  | cons first rest =>
    have hv : rationalMinimum first rest = v := Option.some.inj heq
    rw [← hv]
    exact rationalMinimum_den_dvd first rest D (hvalues first (by simp))
      (fun w hw => hvalues w (by simp [hw]))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalDenominator
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Denominator and bit bounds for the local evaluator on every incoming
seed.  The proofs use the literal local candidates and do not pass through
the good-seed equality with the complete evaluator. -/

namespace EditApproximation

open Finset

theorem physicalLocalWarmup_den_one {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (t : ℕ) (state : PhysicalEntry M J target.length) :
    (physicalLocalWarmup source target U N P F A t state).den = 1 := by
  induction t generalizing state with
  | zero => exact stageInitial_den_one source target U N P F A state
  | succ t ih =>
    rw [physicalLocalWarmup]
    split_ifs
    · exact stageInitial_den_one source target U N P F A state
    · apply Nat.eq_one_of_dvd_one
      apply rationalMinimum_den_dvd
      · rw [stageInitial_den_one source target U N P F A]
      · intro v hv
        obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
        exact rationalActionValue_den_dvd _ _ _ _ _ (Rat.den_natCast _)
          (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using Rat.den_natCast (128 * F))
          (rationalActualWideActions_connection_den _ _ _ action ha)
          (fun i => by rw [ih])
    · exact stageInitial_den_one source target U N P F A state

theorem rationalLocalWideStep_den_dvd {α : Type*} (source target : List α) {M D : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q m : ℕ) (hm : 0 < m)
    (tau a : ℚ) (parentInitial : TargetInterval target.length → ℚ)
    (childMass childInitial old current : Fin M → TargetInterval target.length → ℚ)
    (draw : CellGroupDraws M F Q) (online : List (PhysicalRationalAction M target.length))
    (hinitial : ∀ q, (parentInitial q).den ∣ D)
    (hold : ∀ i r, (old i r).den ∣ D) (hcurrent : ∀ i r, (current i r).den ∣ D)
    (honline : ∀ action ∈ online, action.connection.den = 1)
    (q : TargetInterval target.length) :
    (rationalLocalWideStep source target parent N P F exponent Q tau a (1 / (m : ℚ))
      parentInitial childMass childInitial old current draw online q).den ∣ D * (m + 1) := by
  have hvalue (child : Fin M → TargetInterval target.length → ℚ)
      (hchild : ∀ i r, (child i r).den ∣ D)
      (action : PhysicalRationalAction M target.length) (hconn : action.connection.den = 1) :
      (rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F)
        (fun is => child is.1 is.2) q action).den ∣ D :=
    rationalActionValue_den_dvd _ _ _ _ _ (Rat.den_natCast _)
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using Rat.den_natCast (128 * F))
      hconn (fun i => hchild _ _)
  unfold rationalLocalWideStep
  apply rationalRefinementUpdate_den_dvd m D hm
  · apply rationalMinimum_den_dvd
    · apply rationalMinimum_den_dvd _ _ D (hinitial q)
      intro v hv
      obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
      exact hvalue old hold action (rationalActualWideActions_connection_den _ _ _ action ha)
    · intro v hv
      obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
      have hwide := completeCellGroupActions_wide source target parent N P F exponent Q tau a
        parentInitial childMass childInitial current draw action
        (localCellGroupActions_subset source target parent N P F exponent Q tau a parentInitial
          childMass childInitial current draw q action ha)
      exact hvalue current hcurrent action (rationalActualWideActions_connection_den _ _ _ action hwide)
  · intro v hv
    apply rationalOnlineMinimum_den_dvd _ D _ v hv
    intro value hvalueMem
    obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hvalueMem
    exact hvalue current hcurrent action (honline action ha)

theorem keyedOnlineCandidate_connection_den {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b : ℕ) (tau eta kappa : ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (children : PhysicalChildTables M target.length) (t : ℕ)
    (r : TargetInterval target.length) (integer : ℕ) (action : PhysicalRationalAction M target.length)
    (h : keyedOnlineCandidate source target parent P F exponent H b tau eta kappa
      child initial children t r integer = some action) : action.connection.den = 1 := by
  unfold keyedOnlineCandidate at h
  dsimp only at h
  split_ifs at h
  split at h
  · cases h
  · cases Option.some.inj h
    exact Rat.den_zero

theorem localOnlineCandidates_connection_den {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H : ℕ) (tau a eta kappa : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (children : PhysicalChildTables M target.length) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (q : TargetInterval target.length)
    (action : PhysicalRationalAction M target.length)
    (ha : action ∈ localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      parentInitial child initial children t integer q) : action.connection.den = 1 := by
  obtain ⟨b, _, _, hcandidate⟩ :=
    (localOnlineCandidates_mem source target parent N P F exponent H tau a eta kappa
      parentInitial child initial children t integer q action).mp ha
  exact keyedOnlineCandidate_connection_den source target parent P F exponent H b tau eta kappa
    child initial children t _ _ action hcandidate

theorem physicalLocalOnline_connection_den {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F exponent H T : ℕ) (A tau eta kappa : ℚ)
    (integer : PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
    (node : PhysicalNode M J) (children : PhysicalChildTables M target.length)
    (t : ℕ) (q : TargetInterval target.length) (action : PhysicalRationalAction M target.length)
    (ha : action ∈ physicalLocalOnline source target U N P F exponent H T A tau eta kappa
      integer node children t q) : action.connection.den = 1 := by
  unfold physicalLocalOnline at ha
  split_ifs at ha with hbelow
  · exact localOnlineCandidates_connection_den source target (physicalSourceInterval source.length node)
      N P F exponent H tau (refinementFactor A F) eta kappa _ _ _ children (t - 1) _ q action ha
  · exact False.elim (List.not_mem_nil ha)

theorem physicalLocalRefinement_den_dvd {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F exponent Q : ℕ) (A tau : ℚ) (T ell : ℕ) (hell : 0 < ell)
    (draw : PhysicalInternalNode M J → ℕ → CellGroupDraws M F Q)
    (online : PhysicalNode M J → PhysicalChildTables M target.length → ℕ →
      TargetInterval target.length → List (PhysicalRationalAction M target.length))
    (honline : ∀ node children t q action, action ∈ online node children t q → action.connection.den = 1)
    (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length) :
    (physicalLocalRefinement source target U N P F exponent Q A tau
      (1 / (ell : ℚ) ^ 10) T draw online node t q).den ∣ (ell ^ 10 + 1) ^ (J - node.1.val) := by
  rw [physicalLocalRefinement]
  split_ifs with hbelow hleaf
  · rw [stageInitial_den_one source target U N P F A]
    exact one_dvd _
  · dsimp only
    cases t with
    | zero =>
      rw [physicalLocalWarmup_den_one source target U N P F A]
      exact one_dvd _
    | succ t =>
      have hheight : J - node.1.val = (J - (node.1.val + 1)) + 1 := by omega
      rw [hheight]
      conv_rhs => rw [pow_succ]
      have hdelta : (1 / (ell : ℚ) ^ 10) = 1 / ((ell ^ 10 : ℕ) : ℚ) := by rw [Nat.cast_pow]
      rw [hdelta]
      apply rationalLocalWideStep_den_dvd source target _ N P F exponent Q (ell ^ 10)
        (pow_pos hell 10) tau (refinementFactor A F)
      · intro r
        rw [stageInitial_den_one source target U N P F A]
        exact one_dvd _
      · intro i r
        simpa only [Nat.cast_pow, physicalChild] using
          physicalLocalRefinement_den_dvd source target U N P F exponent Q A tau T ell hell
            draw online honline (physicalChild node hbelow i) t r
      · intro i r
        simpa only [Nat.cast_pow, physicalChild] using
          physicalLocalRefinement_den_dvd source target U N P F exponent Q A tau T ell hell
            draw online honline (physicalChild node hbelow i) (t + 1) r
      · exact honline _ _ _ _
  · rw [stageInitial_den_one source target U N P F A]
    exact one_dvd _
termination_by J - node.1.val
decreasing_by
  all_goals
    unfold physicalChild
    dsimp only
    omega

theorem physicalLocalOnlineRefinement_den_dvd {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F exponent H Q : ℕ) (A tau eta kappa : ℚ) (T ell : ℕ) (hell : 0 < ell)
    (draw : PhysicalInternalNode M J → ℕ → CellGroupDraws M F Q)
    (integer : PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
    (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length) :
    (physicalLocalRefinement source target U N P F exponent Q A tau (1 / (ell : ℚ) ^ 10)
      T draw (physicalLocalOnline source target U N P F exponent H T A tau eta kappa integer)
      node t q).den ∣ (ell ^ 10 + 1) ^ (J - node.1.val) :=
  physicalLocalRefinement_den_dvd source target U N P F exponent Q A tau T ell hell draw _
    (physicalLocalOnline_connection_den source target U N P F exponent H T A tau eta kappa integer) node t q

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryChargedFamily
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! All physical table branches run Boolean arithmetic and issue
address-charged adaptive requests.  Coarse entries are supplied by the
separately executed coarse initializer. -/

namespace EditApproximation

section Family
variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R]
  (source target : List ℕ) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ)
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)



theorem queryChargedFamilyTable_refines
    (ha : ∀ pass, pass ≤ passes → (a pass).value = refinementFactor (A pass).value F)
    (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
    (hp : target.length ≤ 2 ^ positionBits)
    (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx)
    (initial : PhysicalEntry M J target.length → ℕ)
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S}) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryChargedFamilyTable (R := R) source target N P F exponent H Q eM eF hP hM hF
        A a tau eta kappa delta multiplier occurrence symbolBits positionBits parent)
      (chargedRandomGlobalQuery (R := R) source target N P F exponent H Q T S (passes + 1) copies
        (fun pass => (A pass).value) multiplier tau.value eta.value kappa.value delta.value
        (physicalFamilyGroupRead target N P F exponent H Q passes copies)
        (physicalFamilyOnlineRead target N P F exponent H Q passes copies) initial (.inr parent)) := by
  have hinit := queryPhysicalInitial_refines source target N P F (A parent.val.pass)
    (a parent.val.pass) multiplier parent occurrence symbolBits positionBits parent.val.state hP
    (ha parent.val.pass (by have := parent.property.1; omega)) hs ht hp htable
  unfold queryChargedFamilyTable chargedRandomGlobalQuery
  dsimp only
  apply BitQuery.Refines.charge
  by_cases hi : parent.val.index ≤ T
  · rw [ite_eq_left hi, dite_eq_left ((queryNaturalLEWithWork_value parent.val.index T).mpr hi)]
    apply BitQuery.Refines.mapKeysWithWork _ _ (fun _ => rfl)
    exact queryChargedWarmup_refines source target N P F (A parent.val.pass) (a parent.val.pass)
      multiplier parent occurrence symbolBits positionBits (fun pass => (A pass).value) rfl hP
      (ha parent.val.pass (by have := parent.property.1; omega)) hs ht hp htable
  · rw [ite_eq_right hi, dite_eq_right (fun h => hi ((queryNaturalLEWithWork_value parent.val.index T).mp h))]
    apply BitQuery.Refines.charge
    by_cases hb : parent.val.node.1.val < J
    · rw [ite_eq_left hb, dite_eq_left ((binaryNaturalCompareWithWork_lt _ _).mpr hb)]
      apply BitQuery.Refines.charge
      have hshort : (wordLEWithWork
          (saturatingSubtractWithWork (physicalSourceInterval source.length parent.val.node).hi
            (physicalSourceInterval source.length parent.val.node).lo).1 [true]).1 = true ↔
          (physicalSourceInterval source.length parent.val.node).hi -
            (physicalSourceInterval source.length parent.val.node).lo ≤ 1 := by
        rw [wordLEWithWork_value, saturatingSubtractWithWork_value]
        rfl
      by_cases hw : (physicalSourceInterval source.length parent.val.node).hi -
          (physicalSourceInterval source.length parent.val.node).lo ≤ 1
      · rw [ite_eq_left hw, ite_eq_left (hshort.mpr hw)]
        exact hinit.mapKeysWithWork _ _ (fun _ => rfl)
      · rw [ite_eq_right hw, ite_eq_right (fun h => hw (hshort.mp h))]
        apply BitQuery.Refines.mapKeysWithWork _ _ (fun _ => rfl)
        exact queryFamilyBoundedActive_refines (R := R) source target N P F exponent H Q eM eF
          hP hM hF tau (a parent.val.pass) eta kappa delta T S passes copies parent
          (Nat.lt_of_not_ge hi) hb (fun pass => (A pass).value) multiplier initial (ha parent.val.pass (by have := parent.property.1; omega)) hw
    · rw [ite_eq_right hb, dite_eq_right (fun h => hb ((binaryNaturalCompareWithWork_lt _ _).mp h))]
      exact hinit.mapKeysWithWork _ _ (fun _ => rfl)

theorem queryChargedFamilyGlobal_refines
    (ha : ∀ pass, pass ≤ passes → (a pass).value = refinementFactor (A pass).value F)
    (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
    (hp : target.length ≤ 2 ^ positionBits)
    (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx)
    (coarse : PhysicalEntry M J target.length → BinaryFraction × ℕ)
    (initial : PhysicalEntry M J target.length → ℕ)
    (hc : ∀ entry, (coarse entry).1.value = initial entry)
    (request : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryChargedFamilyGlobal (R := R) source target N P F exponent H Q eM eF hP hM hF
        A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse request)
      (chargedRandomGlobalQuery (R := R) source target N P F exponent H Q T S (passes + 1) copies
        (fun pass => (A pass).value) multiplier tau.value eta.value kappa.value delta.value
        (physicalFamilyGroupRead target N P F exponent H Q passes copies)
        (physicalFamilyOnlineRead target N P F exponent H Q passes copies) initial request) := by
  cases request with
  | inl entry => exact .charge _ (.done (hc entry))
  | inr parent =>
    exact queryChargedFamilyTable_refines (R := R) source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits ha hs ht hp htable initial parent

end Family
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRequestGrid
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The canonical cache grid for every request, including terminal and
warmup branches.  This invariant holds for all incoming seeds and draws. -/

namespace EditApproximation



theorem localRequestValue_den_dvd {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
    (source target : List α) (N P F exponent H Q T S copies ell : ℕ)
    (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa : ℚ)
    (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
    (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
    (initial : PhysicalEntry M J target.length → ℕ) (hell : 0 < ell)
    (request : PhysicalTableRequest M J target.length) :
    (localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa (1 / (ell : ℚ) ^ 10) group integer initial request).den ∣
      (ell ^ 10 + 1) ^ request.remainingDepth := by
  unfold localRequestValue unifiedPhysicalValue
  split
  · rw [physicalLocalWarmup_den_one]
    exact one_dvd _
  · exact physicalLocalOnlineRefinement_den_dvd source target _ N P F exponent H Q _ tau eta kappa
      T ell hell _ _ request.node (request.index - T) request.state

theorem chargedRequestValue_den_dvd {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
    (source target : List α) (N P F exponent H Q T S passes copies ell : ℕ)
    (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa : ℚ)
    (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
    (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
    (initial : PhysicalEntry M J target.length → ℕ) (hell : 0 < ell)
    (request : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedRequestValue source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa (1 / (ell : ℚ) ^ 10) group integer initial request).den ∣
      (ell ^ 10 + 1) ^ chargedPhysicalRemaining request := by
  cases request with
  | inl entry => simp only [chargedRequestValue, chargedPhysicalRemaining, Rat.den_natCast, one_dvd]
  | inr request =>
    exact localRequestValue_den_dvd (R := R) source target N P F exponent H Q T S copies ell
      factor multiplier tau eta kappa group integer initial hell request.val

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryFamilyMemo
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! One binary memo stores independent scalar draws, coarse values, and
all recursive tables.  The raw implementation preserves the exact
reference trace; normalization is justified on its reachable values. -/

namespace EditApproximation

section Family
variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R]
  (source target : List ℕ) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ)
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (coarse : PhysicalEntry M J target.length → BinaryFraction × ℕ)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)





theorem queryFamilyMemoRaw_refines
    (ha : ∀ pass, pass ≤ passes → (a pass).value = refinementFactor (A pass).value F)
    (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
    (hp : target.length ≤ 2 ^ positionBits)
    (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx)
    (initial : PhysicalEntry M J target.length → ℕ)
    (hc : ∀ entry, (coarse entry).1.value = initial entry)
    (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryFamilyMemoRaw source target N P F exponent H Q eM eF hP hM hF
        A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse draw key)
      (SourceRanked.body ChargedPhysicalRequest.rank
        (physicalFamilyProgram source target N P F exponent H Q T S passes copies
          (fun pass => (A pass).value) multiplier tau.value eta.value kappa.value delta.value initial)
        (physicalFamilyAnswer target N P F exponent H Q passes copies draw) key) := by
  have hr := SourceRanked.bitBody_refines ChargedPhysicalRequest.rank
    (queryChargedFamilyGlobal (R := R) source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse)
    (physicalFamilyProgram source target N P F exponent H Q T S passes copies
      (fun pass => (A pass).value) multiplier tau.value eta.value kappa.value delta.value initial)
    (queryFamilySourceWordWithWork target N P F exponent H Q draw)
    (fun parent => queryChargedFamilyGlobal_refines source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits ha hs ht hp htable
      coarse initial hc parent) key
  have hsources : (fun key => (queryFamilySourceWordWithWork target N P F exponent H Q draw key).1.value) =
      physicalFamilyAnswer target N P F exponent H Q passes copies draw := by
    funext key
    exact BinaryFraction.nat_value _
  rw [hsources] at hr
  exact hr



end Family
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryFamilyNormalize
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete mixed memo is normalized on the physical
table grid.  Its actual ranked binary values and adaptive reference trace
agree on every coarse seed and every finite scalar draw. -/

namespace EditApproximation

section Family
variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R]
  (source target : List ℕ) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ)
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (coarse : PhysicalEntry M J target.length → BinaryFraction × ℕ)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)
  (initial : PhysicalEntry M J target.length → ℕ)
  (ha : ∀ pass, pass ≤ passes → (a pass).value = refinementFactor (BinaryFraction.value (A pass)) F)
  (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
  (hp : target.length ≤ 2 ^ positionBits)
  (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx)
  (hc : ∀ entry, (coarse entry).1.value = initial entry)
  (ell : ℕ) (hell : 0 < ell) (hdelta : delta.value = 1 / (ell : ℚ) ^ 10)
  (base : List Bool) (hbase : bitWordValue base = ell ^ 10 + 1)

local notation "raw" => queryFamilyMemoRaw source target N P F exponent H Q eM eF hP hM hF
  A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse draw
local notation "reference" => SourceRanked.body ChargedPhysicalRequest.rank
  (physicalFamilyProgram source target N P F exponent H Q T S passes copies
    (fun pass => BinaryFraction.value (A pass)) multiplier tau.value eta.value kappa.value delta.value initial)
  (physicalFamilyAnswer target N P F exponent H Q passes copies draw)
local notation "semantic" => SourceRanked.value
  (physicalFamilyAnswer target N P F exponent H Q passes copies draw)
  (physicalFamilyRequestValue source target N P F exponent H Q T S passes copies
    (fun pass => BinaryFraction.value (A pass)) multiplier tau.value eta.value kappa.value delta.value initial hP draw)
local notation "normalized" => queryFamilyMemoNormalized source target N P F exponent H Q eM eF hP hM hF
  A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse draw
  base (familyBase_pos ell base hbase)

include ha hs ht hp htable hc hell hdelta in
theorem queryFamilyMemoNormalized_width_oai
    (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q)
    (B V : ℕ) (hB : base.length ≤ B) (hV : |semantic key| ≤ (V : ℚ)) :
    (rankedBitProgramValue (SourceRanked.rank ChargedPhysicalRequest.rank) normalized key).width ≤
      Nat.size V + 2 * (queryFamilyMemoRemaining (M := M) (J := J) (R := R)
        (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q key * B + 1) + 1 := by
  have hraw (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q) :
      BitQuery.Refines (fun word value => word.value = value) (raw key) (reference key) :=
    queryFamilyMemoRaw_refines source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse draw
      ha hs ht hp htable initial hc key
  have hbody (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q) :
      (reference key).value (fun child => semantic child.val) = semantic key := by
    apply SourceRanked.body_value
    intro request
    exact physicalFamilyProgram_value source target N P F exponent H Q T S passes copies
      (fun pass => BinaryFraction.value (A pass)) multiplier tau.value eta.value kappa.value delta.value initial hP draw request
  have hd (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q) :
      (semantic key).den ∣ bitWordValue base ^ queryFamilyMemoRemaining (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q key := by
    cases key with
    | inl source =>
      change ((draw source).val : ℚ).den ∣ _
      rw [Rat.den_natCast]
      exact one_dvd _
    | inr request =>
      change (physicalFamilyRequestValue source target N P F exponent H Q T S passes copies
        (fun pass => BinaryFraction.value (A pass)) multiplier tau.value eta.value kappa.value delta.value initial hP draw
        request).den ∣ bitWordValue base ^ chargedPhysicalRemaining request
      unfold physicalFamilyRequestValue
      rw [hdelta, hbase]
      exact chargedRequestValue_den_dvd source target N P F exponent H Q T S (passes + 1) copies ell
        (fun pass => BinaryFraction.value (A pass)) multiplier tau.value eta.value kappa.value _ _ initial hell request
  exact rankedNormalizeBody_width (SourceRanked.rank ChargedPhysicalRequest.rank) raw reference
    semantic hraw hbody base (familyBase_pos ell base hbase)
    (queryFamilyMemoRemaining (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q)
    hd key B V hB hV


end Family
end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.queryFamilyMemoNormalized_width_oai := @OAI.EditApproximation.queryFamilyMemoNormalized_width_oai
