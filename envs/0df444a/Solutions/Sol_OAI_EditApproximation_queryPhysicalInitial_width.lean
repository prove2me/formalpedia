-- Prove2me | solution 1 for OAI.EditApproximation.queryPhysicalInitial_width
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:29:47.335198+00:00
-- url     : https://prove2.me/submissions/59b894e7-b3b2-417e-9112-d514cdd02500

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
import Definitions.Def_EditApproxScheme_07
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_OAIQ361V3Ea002

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
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRawNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The optimizer's numerical loops executed on Boolean fraction storage.
The value proofs identify the unreduced numerator and denominator, not just
the represented rational. Thus the raw storage bounds apply to this code. -/

namespace EditApproximation
namespace BinaryFraction

theorem nat_width_le_storageBits (n : ℕ) : (nat n).width ≤ (nat n).representation.storageBits := by
  rw [nat_representation]
  have hw : (nat n).width = max (Nat.size n) 1 := by
    simp only [nat, width, SignedBinary.ofInt, Int.natAbs_natCast, ← Nat.size_eq_bits_len,
      List.length_cons, List.length_nil]
  rw [hw]
  simp only [UnreducedRational.nat, UnreducedRational.storageBits, Int.natAbs_natCast, Nat.size_one]
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_UnreducedStorage
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.nat_representation _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial raw storage bounds used by the Boolean numerical loops. -/

namespace EditApproximation
namespace UnreducedRational

open Finset

theorem storageBits_nat (n : ℕ) : (nat n).storageBits = Nat.size n + 2 := by
  simp [nat, storageBits]

end UnreducedRational
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryUpdateWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bit cost of the actual coordinate update, including construction of
its rational step and complement. -/

namespace EditApproximation
namespace BinaryFraction

theorem nat_width_le (n : ℕ) : (nat n).width ≤ Nat.size n + 2 := by
  have h := nat_width_le_storageBits n
  rw [nat_representation, UnreducedRational.storageBits_nat] at h
  exact h

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryInitialKernel
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal initial-cone arithmetic on gathered integer seed entries. The
local grid list is supplied by its bounded enumerator; all values, ceilings,
spatial charges and the fallback minimum are computed on binary storage. -/

namespace EditApproximation
namespace BinaryFraction



theorem initialMinimumWithWork_value {α : Type*} (source target : List α)
    (U : TargetInterval target.length → ℕ) (N P F : ℕ) (A : ℚ) (a : BinaryFraction)
    (query : TargetInterval target.length) :
    (initialMinimumWithWork source.length U N F a query
      (localInitialConeCenters N P A U query)).1.value =
      localInitialConeTable source target U N P F A a.value query := by
  have hzero : (naturalEqualWithWork (U query) 0).1 = true ↔ U query = 0 :=
    naturalEqualWithWork_value _ _
  unfold initialMinimumWithWork localInitialConeTable
  by_cases hz : U query = 0
  · rw [ite_eq_left (hzero.mpr hz), ite_eq_left hz]
    rw [← representation_value, zero_representation, UnreducedRational.value_zero]
  · rw [ite_eq_right (fun h => hz (hzero.mp h)), ite_eq_right hz]
    simp only [minimumWithWork_value, canonicalMulWithWork_value, canonicalAddWithWork_value,
      arithmeticMapWithWork_value, List.map_map, Function.comp_def, initialConeWithWork_value,
      nat_value, one, Nat.cast_one, Nat.cast_ofNat]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryScaleGrid
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal dyadic scales and the finite initial-cone center list, with
binary rational comparisons and bounded grid enumeration. -/

namespace EditApproximation

namespace BinaryFraction



@[simp] theorem initialProgramWithWork_value {α : Type*} (source target : List α)
    (N P F : ℕ) (A a : BinaryFraction) (U : TargetInterval target.length → ℕ)
    (q : TargetInterval target.length) (hP : 0 < P) :
    (initialProgramWithWork source.length N P F A a U q).1.value =
      localInitialConeTable source target U N P F A.value a.value q := by
  simp only [initialProgramWithWork, initialCentersWithWork_value N P A U q hP]
  exact initialMinimumWithWork_value source target U N P F A.value a q

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryFixedDenominator
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialProgramWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
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
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
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
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalDenominator
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
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

theorem rationalMinimum_den_dvd (fallback : ℚ) (values : List ℚ) (D : ℕ)
    (hfallback : fallback.den ∣ D) (hvalues : ∀ v ∈ values, v.den ∣ D) :
    (rationalMinimum fallback values).den ∣ D := by
  induction values with
  | nil => exact hfallback
  | cons v rest ih =>
    exact rat_den_min_dvd (hvalues v (by simp)) (ih fun w hw => hvalues w (by simp [hw]))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCachedShellWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Initial and warmup returns are integers on every seed. Their cache
representation is produced by the counted fixed-denominator routine, rather
than by an uncharged conversion of a rational value. -/

namespace EditApproximation

theorem localInitialConeTable_den_one {α : Type*} (source target : List α)
    (U : TargetInterval target.length → ℕ) (N P F : ℕ) (A a : ℚ)
    (query : TargetInterval target.length) :
    (localInitialConeTable source target U N P F A a query).den = 1 := by
  unfold localInitialConeTable
  split_ifs
  · exact Rat.den_zero
  · apply Nat.eq_one_of_dvd_one
    apply rationalMinimum_den_dvd
    · have heq : (32 * F + 1 : ℚ) * N = (((32 * F + 1) * N : ℕ) : ℚ) := by
        push_cast
        rfl
      rw [heq, Rat.den_natCast]
    · intro v hv
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hv
      unfold initialConeValue scaledSeedValue
      apply rat_den_add_dvd
      · apply rat_den_max_dvd
        · simp only [Rat.den_natCast, dvd_refl]
        · have heq : rationalStateGap source target r =
              (((r.hi : ℤ) - r.lo - source.length : ℤ) : ℚ) := by
            simp only [rationalStateGap, Int.cast_sub, Int.cast_natCast]
          rw [heq, ← Int.cast_abs]
          simp only [Rat.den_intCast, dvd_refl]
      · have heq : (32 * F : ℚ) * targetEndpointDistance query r =
            ((32 * F * targetEndpointDistance query r : ℕ) : ℚ) := by
          push_cast
          rfl
        rw [heq, Rat.den_natCast]

namespace BinaryFraction

attribute [local irreducible] initialProgramWithWork localWarmupKernelWithWork

theorem cachedInitialProgramWithWork_value_width {α : Type*} (source target : List α)
    (N P F : ℕ) (A a : BinaryFraction) (U : TargetInterval target.length → ℕ)
    (query : TargetInterval target.length) (hP : 0 < P) :
    (cachedInitialProgramWithWork source.length N P F A a U query).1.value =
        localInitialConeTable source target U N P F A.value a.value query ∧
    (cachedInitialProgramWithWork source.length N P F A a U query).1.width ≤
        Nat.size ((32 * F + 1) * N) + 3 := by
  let raw := initialProgramWithWork source.length N P F A a U query
  have hraw := initialProgramWithWork_value source target N P F A a U query hP
  have hd : raw.1.value.den ∣ bitWordValue [true] ^ 0 := by
    rw [hraw, localInitialConeTable_den_one]
    exact one_dvd _
  have hv : |raw.1.value| ≤ (((32 * F + 1) * N : ℕ) : ℚ) := by
    rw [hraw, abs_of_nonneg (localInitialConeTable_nonneg source target U N P F A.value a.value query)]
    unfold localInitialConeTable
    split_ifs
    · exact Nat.cast_nonneg _
    · simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
        rationalMinimum_le_fallback ((32 * F + 1 : ℚ) * N) _
  exact ⟨(finishCachedWithWork_value raw [true] (by decide) 0 hd).trans hraw,
    by
      change (powerDenominatorWithWork raw.1 [true] (by decide) 0).1.width ≤ _
      simpa only [Nat.zero_mul, Nat.zero_add, Nat.one_mul, Nat.mul_one, Nat.add_assoc, Nat.reduceAdd] using
        powerDenominatorWithWork_width raw.1 [true] (by decide) 0 ((32 * F + 1) * N) 1
        (by decide) hd hv⟩

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_OccurrenceLeaf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Constant-size leaf descriptors use the preprocessed occurrence index.
The target interval is represented by endpoints; it is never copied or
scanned while evaluating a singleton leaf. -/

namespace EditApproximation



theorem indexedSingletonCostWithWork_spec (table : BinaryMemo PositionCounts)
    (symbolBits positionBits a lo hi : ℕ) :
    (indexedSingletonCostWithWork table symbolBits positionBits a lo hi).1 =
        indexedSingletonCost table symbolBits positionBits a lo hi ∧
      (indexedSingletonCostWithWork table symbolBits positionBits a lo hi).2 ≤
        2 * symbolBits + 4 * positionBits + 9 := by
  by_cases h : lo = hi
  · simp only [indexedSingletonCostWithWork, indexedSingletonCost, h, ite_true, if_true]
    exact ⟨True.intro, by omega⟩
  · simp only [indexedSingletonCostWithWork, indexedSingletonCost, h, ite_false, if_false]
    rw [occurrenceQueryWithWork_spec]
    exact ⟨rfl, by omega⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_IndexedTerminalWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open Filter

/-- Empty and singleton terminal states use the already prepared occurrence
index. Endpoints are read directly; no target substring is copied. -/


 theorem indexedLeafWithWork_value (table : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (symbol : Option ℕ) (lo hi : ℕ) :
    (indexedLeafWithWork table symbolBits positionBits symbol lo hi).1 =
      indexedLeafCost table symbolBits positionBits symbol lo hi := by
  cases symbol with
  | none => rfl
  | some a => exact (indexedSingletonCostWithWork_spec table symbolBits positionBits a lo hi).1

 theorem indexedLeafWithWork_cost (table : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (symbol : Option ℕ) (lo hi : ℕ) :
    (indexedLeafWithWork table symbolBits positionBits symbol lo hi).2 ≤
      2 * symbolBits + 4 * positionBits + 10 := by
  cases symbol with
  | none => change 2 ≤ _; omega
  | some a => exact (indexedSingletonCostWithWork_spec table symbolBits positionBits a lo hi).2.trans (by omega)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryIndexedLeaf
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

/-- The indexed terminal result is written directly as a binary rational. -/


theorem indexedLeafWithWork_le (table : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (symbol : Option ℕ) (lo hi : ℕ) :
    (indexedLeafWithWork table symbolBits positionBits symbol lo hi).1 ≤ hi + 1 := by
  rw [indexedLeafWithWork_value]
  cases symbol with
  | none => change hi - lo ≤ hi + 1; omega
  | some a =>
    simp only [indexedLeafCost, indexedSingletonCost]
    split_ifs <;> omega

theorem binaryIndexedLeafWithWork_bounds (table : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (symbol : Option ℕ) (lo hi : ℕ) :
    (binaryIndexedLeafWithWork table symbolBits positionBits symbol lo hi).1.width ≤ Nat.size (hi + 1) + 2 ∧
    (binaryIndexedLeafWithWork table symbolBits positionBits symbol lo hi).2 ≤
      2 * symbolBits + 4 * positionBits + Nat.size (hi + 1) + 12 := by
  have hv := Nat.size_le_size (indexedLeafWithWork_le table symbolBits positionBits symbol lo hi)
  have hc := indexedLeafWithWork_cost table symbolBits positionBits symbol lo hi
  constructor
  · exact (BinaryFraction.nat_width_le _).trans (Nat.add_le_add_right hv 2)
  · change _ + _ + 2 ≤ _
    omega

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryInitialReads
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Inline initial-cone evaluation reads the gathered previous-pass seed
words explicitly. Each query seed is loaded once per routine and each
visited center load contributes its measured lookup cost. -/

namespace EditApproximation
namespace BinaryFraction



theorem initialGridReadWithWork_eq_cost {n : ℕ} (P : ℕ) (A : BinaryFraction)
    (read : TargetInterval n → List Bool × ℕ) (radius : ℕ) (q : TargetInterval n) (b R : ℕ)
    (hR : ∀ r, (read r).2 ≤ R) :
    (initialGridReadWithWork P A read radius q b).1 =
      (initialGridPlainWithWork P A (fun r => bitWordValue (read r).1) radius q b).1 ∧
    (initialGridReadWithWork P A read radius q b).2 ≤
      (initialGridPlainWithWork P A (fun r => bitWordValue (read r).1) radius q b).2 * (R + 1) := by
  let spacing := seedGridSpacingWithWork b P
  let points := gridStateBoxWithWork n (bitWordValue spacing.1) radius q.lo q.hi
  have h := filterWithWork_add_read
    (fun r => initialCenterGuardWithWork b (bitWordValue (read r).1) A)
    (fun r => (read r).2) points.1 R (fun r _ => hR r)
  constructor
  · simpa only [initialGridReadWithWork, initialGridPlainWithWork, spacing, points] using h.1
  · change spacing.2 + points.2 + _ + 2 ≤ (spacing.2 + points.2 + _ + 2) * (R + 1)
    nlinarith only [h.2]



theorem initialCentersReadWithWork_eq_cost {n : ℕ} (N P : ℕ) (A : BinaryFraction)
    (read : TargetInterval n → List Bool × ℕ) (q : TargetInterval n) (R : ℕ)
    (hR : ∀ r, (read r).2 ≤ R) :
    (initialCentersReadWithWork N P A read q).1 =
      (initialCentersWithWork N P A (fun r => bitWordValue (read r).1) q).1 ∧
    (initialCentersReadWithWork N P A read q).2 ≤
      (initialCentersWithWork N P A (fun r => bitWordValue (read r).1) q).2 * (R + 2) := by
  let Uq := bitWordValue (read q).1
  let scales := dyadicScalesWithWork N
  let active := filterWithWork (fun b => initialScaleGuardWithWork Uq b A) scales.1
  let plain := initialGridPlainWithWork P A (fun r => bitWordValue (read r).1) Uq q
  have h := arithmeticFlatMapWithWork_factor (initialGridReadWithWork P A read Uq q)
    plain active.1 (R + 1) (by omega)
    (fun b _ => (initialGridReadWithWork_eq_cost P A read Uq q b R hR).1)
    (fun b _ => (initialGridReadWithWork_eq_cost P A read Uq q b R hR).2)
  have hq := hR q
  refine ⟨h.1, ?_⟩
  change (read q).2 + scales.2 + active.2 + _ + 3 ≤
    (scales.2 + active.2 + (arithmeticFlatMapWithWork plain active.1).2 + 3) * (R + 2)
  nlinarith only [h.2, hq]



theorem initialConeReadWithWork_eq_cost {n : ℕ} (sourceLength : ℕ)
    (read : TargetInterval n → List Bool × ℕ) (a L : BinaryFraction)
    (query center : TargetInterval n) (R : ℕ) (hR : (read center).2 ≤ R) :
    (initialConeReadWithWork sourceLength read a L query center).1 =
      (initialConeWithWork sourceLength (fun r => bitWordValue (read r).1) a L query center).1 ∧
    (initialConeReadWithWork sourceLength read a L query center).2 ≤
      (initialConeWithWork sourceLength (fun r => bitWordValue (read r).1) a L query center).2 + R := by
  constructor
  · rfl
  · have heq : initialConeWithWork sourceLength (fun _ => bitWordValue (read center).1) a L query center =
        initialConeWithWork sourceLength (fun r => bitWordValue (read r).1) a L query center := rfl
    change (read center).2 + _ ≤ _ + R
    rw [heq]
    omega



theorem initialMinimumReadWithWork_eq_cost {n : ℕ} (sourceLength : ℕ)
    (read : TargetInterval n → List Bool × ℕ) (N F : ℕ) (a : BinaryFraction)
    (query : TargetInterval n) (centers : List (TargetInterval n)) (R : ℕ)
    (hR : ∀ r, (read r).2 ≤ R) :
    (initialMinimumReadWithWork sourceLength read N F a query centers).1 =
      (initialMinimumWithWork sourceLength (fun r => bitWordValue (read r).1) N F a query centers).1 ∧
    (initialMinimumReadWithWork sourceLength read N F a query centers).2 ≤
      (initialMinimumWithWork sourceLength (fun r => bitWordValue (read r).1) N F a query centers).2 *
        (R + 2) := by
  let L := canonicalMulWithWork (nat 32) (nat F)
  have hmap := arithmeticMapWithWork_extra
    (initialConeReadWithWork sourceLength read a L.1 query)
    (initialConeWithWork sourceLength (fun r => bitWordValue (read r).1) a L.1 query)
    (fun _ => R) centers
    (fun r _ => (initialConeReadWithWork_eq_cost sourceLength read a L.1 query r R (hR r)).1)
    (fun r _ => (initialConeReadWithWork_eq_cost sourceLength read a L.1 query r R (hR r)).2)
  have hs : (centers.map (fun _ => R)).sum = centers.length * R := by
    simp only [List.map_const', List.sum_replicate, smul_eq_mul]
  rw [hs] at hmap
  have hlen := arithmeticMapWithWork_length_le_cost
    (initialConeWithWork sourceLength (fun r => bitWordValue (read r).1) a L.1 query) centers
  have hquery := hR query
  unfold initialMinimumReadWithWork initialMinimumWithWork
  dsimp only
  split_ifs
  · constructor
    · rfl
    · nlinarith only [hquery]
  · constructor
    · simp only [L, hmap.1]
    · dsimp only
      rw [show (canonicalMulWithWork (nat 32) (nat F)) = L from rfl, hmap.1]
      have hprod := Nat.mul_le_mul_right R hlen
      nlinarith only [hmap.2, hquery, hprod]



theorem initialProgramReadWithWork_eq_cost {n : ℕ} (sourceLength N P F : ℕ) (A a : BinaryFraction)
    (read : TargetInterval n → List Bool × ℕ) (query : TargetInterval n) (R : ℕ)
    (hR : ∀ r, (read r).2 ≤ R) :
    (initialProgramReadWithWork sourceLength N P F A a read query).1 =
      (initialProgramWithWork sourceLength N P F A a (fun r => bitWordValue (read r).1) query).1 ∧
    (initialProgramReadWithWork sourceLength N P F A a read query).2 ≤
      (initialProgramWithWork sourceLength N P F A a (fun r => bitWordValue (read r).1) query).2 *
        (R + 2) := by
  have hc := initialCentersReadWithWork_eq_cost N P A read query R hR
  have hm := initialMinimumReadWithWork_eq_cost sourceLength read N F a query
    (initialCentersWithWork N P A (fun r => bitWordValue (read r).1) query).1 R hR
  unfold initialProgramReadWithWork initialProgramWithWork
  dsimp only
  rw [hc.1]
  constructor
  · exact hm.1
  · nlinarith only [hc.2, hm.2]

theorem finishCachedWithWork_read_factor (read plain : BinaryFraction × ℕ)
    (base : List Bool) (hbase : 0 < bitWordValue base) (remaining K : ℕ)
    (hK : 1 ≤ K) (hvalue : read.1 = plain.1) (hcost : read.2 ≤ plain.2 * K) :
    (finishCachedWithWork read base hbase remaining).1 =
      (finishCachedWithWork plain base hbase remaining).1 ∧
    (finishCachedWithWork read base hbase remaining).2 ≤
      (finishCachedWithWork plain base hbase remaining).2 * K := by
  unfold finishCachedWithWork
  dsimp only
  rw [hvalue]
  refine ⟨rfl, ?_⟩
  nlinarith only [hK, hcost]



theorem cachedInitialProgramReadWithWork_eq_cost {n : ℕ} (sourceLength N P F : ℕ) (A a : BinaryFraction)
    (read : TargetInterval n → List Bool × ℕ) (query : TargetInterval n) (R : ℕ)
    (hR : ∀ r, (read r).2 ≤ R) :
    (cachedInitialProgramReadWithWork sourceLength N P F A a read query).1 =
      (cachedInitialProgramWithWork sourceLength N P F A a (fun r => bitWordValue (read r).1) query).1 ∧
    (cachedInitialProgramReadWithWork sourceLength N P F A a read query).2 ≤
      (cachedInitialProgramWithWork sourceLength N P F A a (fun r => bitWordValue (read r).1) query).2 *
        (R + 2) := by
  have h := initialProgramReadWithWork_eq_cost sourceLength N P F A a read query R hR
  exact finishCachedWithWork_read_factor _ _ [true] (by decide) 0 (R + 2) (by omega) h.1 h.2

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitQuery
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
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

theorem value_collect {ι κ β : Type*} (oracle : ι → BinaryFraction)
    (reader : κ → BitQuery ι BinaryFraction) (inputs : List κ)
    (next : List BinaryFraction → BitQuery ι β) :
    (collect reader inputs next).value oracle =
      (next (inputs.map fun key => (reader key).value oracle)).value oracle := by
  induction inputs generalizing next with
  | nil => rfl
  | cons key inputs ih => simp only [collect, value_bind, value, ih, List.map_cons]

end BitQuery
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInitialProgramCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open BinaryFraction

theorem queryInitialConeProgramAt_width {ι : Type*} {n : ℕ}
    (sourceLength N P F : ℕ) (A a : BinaryFraction)
    (reader : TargetInterval n → BitQuery ι BinaryFraction) (q : TargetInterval n)
    (oracle : ι → BinaryFraction) (hP : 0 < P) :
    ((queryInitialConeProgramAt sourceLength N P F A a reader q).value oracle).width ≤
      Nat.size ((32 * F + 1) * N) + 3 := by
  classical
  let value := (reader q).value oracle
  let keys := queryInitialConeCentersWithWork N P A value q
  let words := keys.1.map fun r => (reader r).value oracle
  let seed := queryInitialSeedReadWithWork value q keys.1 words
  let R := Finset.univ.sup (fun r => (seed r).2)
  have hR (r : TargetInterval n) : (seed r).2 ≤ R :=
    Finset.le_sup (f := fun r => (seed r).2) (Finset.mem_univ r)
  have heq := (cachedInitialProgramReadWithWork_eq_cost sourceLength N P F A a seed q R hR).1
  have hw0 := fun (U : TargetInterval (List.replicate n ()).length → ℕ) r =>
    (cachedInitialProgramWithWork_value_width (List.replicate sourceLength ())
      (List.replicate n ()) N P F A a U r hP).2
  generalize hy : (List.replicate n ()).length = ny at hw0
  simp only [List.length_replicate] at hy
  subst ny
  have hw := hw0 (fun r => bitWordValue (seed r).1) q
  simp only [List.length_replicate] at hw
  simp only [queryInitialConeProgramAt, BitQuery.value_bind, BitQuery.value_collect,
    BitQuery.compute, BitQuery.value]
  change (cachedInitialProgramReadWithWork sourceLength N P F A a seed q).1.width ≤ _
  rw [heq]
  exact hw

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryPhysicalInitialCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Initial
variable (source target : List ℕ) {M J passes copies T S : ℕ}
  (N P F Amax B C : ℕ) (A a : BinaryFraction) (multiplier : ℕ → ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (oracle : {child : ChargedPhysicalRequest M J target.length passes copies T S //
    child.rank < ChargedPhysicalRequest.rank (.inr parent)} → BinaryFraction)
  (readWork : {child : ChargedPhysicalRequest M J target.length passes copies T S //
    child.rank < ChargedPhysicalRequest.rank (.inr parent)} → ℕ)

theorem queryPhysicalInitial_width_oai (q : TargetInterval target.length)
    (hP : 0 < P) (hleaf : Nat.size (target.length + 1) + 2 ≤ B)
    (hinit : Nat.size ((32 * F + 1) * N) + 3 ≤ B) :
    ((queryPhysicalInitial source target N P F A a multiplier parent occurrence symbolBits positionBits q).value
      oracle).width ≤ B := by
  unfold queryPhysicalInitial
  simp only [BitQuery.value]
  split
  · exact (binaryIndexedLeafWithWork_bounds occurrence symbolBits positionBits _ q.lo q.hi).1.trans
      ((Nat.add_le_add_right (Nat.size_le_size (Nat.add_le_add_right q.valid 1)) 2).trans hleaf)
  · exact (queryInitialConeProgramAt_width _ N P F A a (queryChargedSeedAt parent N multiplier) q
      oracle hP).trans hinit

end Initial
end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.queryPhysicalInitial_width_oai := @OAI.EditApproximation.queryPhysicalInitial_width_oai
