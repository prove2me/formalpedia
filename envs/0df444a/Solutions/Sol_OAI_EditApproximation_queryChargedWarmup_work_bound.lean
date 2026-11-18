-- Prove2me | solution 1 for OAI.EditApproximation.queryChargedWarmup_work_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:42:37.656754+00:00
-- url     : https://prove2.me/submissions/15c632b2-1269-4bb7-b78c-6b9b117a5b68

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
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_OAIQ361V3Ea002
import Theorems.Thm_OAI_EditApproximation_queryInitialConeProgramAt_work_bound
import Theorems.Thm_OAI_EditApproximation_queryPhysicalInitial_width
import Theorems.Thm_OAI_EditApproximation_queryWarmupProgram_work_bound

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryArithmeticWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal Boolean ripple addition. The counter counts Boolean gates and
bit writes, not unit-cost arithmetic on unbounded integers. -/

namespace EditApproximation







theorem bitAddWithWork_cost (left right : List Bool) (carry : Bool) :
    (bitAddWithWork left right carry).2 ≤ 9 * (left.length + right.length) + 1 := by
  induction left generalizing right carry with
  | nil =>
    simp only [bitAddWithWork]
    induction right generalizing carry with
    | nil => cases carry <;> simp [bitAddNilLeftWithWork]
    | cons b bs ih =>
      simp only [bitAddNilLeftWithWork, List.length_cons, List.length_nil]
      have h := ih (bitCarry false b carry)
      simp only [List.length_nil] at h
      omega
  | cons a as ih =>
    cases right with
    | nil =>
      simp only [bitAddWithWork, List.length_cons, List.length_nil]
      have h := ih [] (bitCarry a false carry)
      simp only [List.length_nil] at h
      omega
    | cons b bs =>
      simp only [bitAddWithWork, List.length_cons]
      have h := ih bs (bitCarry a b carry)
      omega

theorem bitAddWithWork_length (left right : List Bool) (carry : Bool) :
    (bitAddWithWork left right carry).1.length ≤ max left.length right.length + 1 := by
  induction left generalizing right carry with
  | nil =>
    simp only [bitAddWithWork]
    induction right generalizing carry with
    | nil => cases carry <;> simp [bitAddNilLeftWithWork]
    | cons b bs ih =>
      simp only [bitAddNilLeftWithWork, List.length_cons, List.length_nil, Nat.zero_max]
      have h := ih (bitCarry false b carry)
      simp only [List.length_nil, Nat.zero_max] at h
      omega
  | cons a as ih =>
    cases right with
    | nil =>
      simp only [bitAddWithWork, List.length_cons, List.length_nil, Nat.max_zero]
      have h := ih [] (bitCarry a false carry)
      simp only [List.length_nil, Nat.max_zero] at h
      omega
    | cons b bs =>
      simp only [bitAddWithWork, List.length_cons]
      have h := ih bs (bitCarry a b carry)
      omega

theorem bitMulWithWork_length (left right : List Bool) :
    (bitMulWithWork left right).1.length ≤ 2 * left.length + right.length + 1 := by
  induction left with
  | nil => simp [bitMulWithWork]
  | cons bit bits ih =>
    cases bit
    · simp only [bitMulWithWork, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
    · simp only [bitMulWithWork, ↓reduceIte, List.length_cons]
      have h := bitAddWithWork_length (false :: (bitMulWithWork bits right).1) right false
      simp only [List.length_cons] at h
      omega

theorem bitMulWithWork_cost (left right : List Bool) :
    (bitMulWithWork left right).2 ≤ 20 * (left.length + 1) * (left.length + right.length + 1) := by
  induction left with
  | nil => simp [bitMulWithWork]; omega
  | cons bit bits ih =>
    have hlength := bitMulWithWork_length bits right
    have hadd := bitAddWithWork_cost (false :: (bitMulWithWork bits right).1) right false
    simp only [List.length_cons] at hadd
    cases bit
    · simp only [bitMulWithWork, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      nlinarith only [ih]
    · simp only [bitMulWithWork, ↓reduceIte, List.length_cons]
      nlinarith only [ih, hlength, hadd]



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_NumericalWork
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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_UnreducedRational
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

theorem mul_den_bits (a b : UnreducedRational) :
    Nat.size (a.mul b).den ≤ Nat.size a.den + Nat.size b.den :=
  natural_product_bit_length _ _

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

theorem trimBitWordWithWork_cost (bits : List Bool) :
    (trimBitWordWithWork bits).2 = 3 * bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    simp only [trimBitWordWithWork, List.length_cons, ih]
    omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySubtractWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Ripple-borrow subtraction, used after the magnitude comparison in
signed-integer addition. No unit-cost operation on unbounded integers is
used by this Boolean routine. -/

namespace EditApproximation





theorem bitSubtractWithWork_cost (left right : List Bool) (borrow : Bool) :
    (bitSubtractWithWork left right borrow).2.2 ≤ 9 * (left.length + right.length) + 1 := by
  induction left generalizing right borrow with
  | nil =>
    induction right generalizing borrow with
    | nil => simp [bitSubtractWithWork, bitSubtractNilLeftWithWork]
    | cons b bs ih =>
      have h := ih (bitBorrow false b borrow)
      simp only [bitSubtractWithWork, bitSubtractNilLeftWithWork, List.length_cons, List.length_nil] at *
      omega
  | cons a as ih =>
    cases right with
    | nil =>
      have h := ih [] (bitBorrow a false borrow)
      simp only [bitSubtractWithWork, List.length_cons, List.length_nil] at *
      omega
    | cons b bs =>
      have h := ih bs (bitBorrow a b borrow)
      simp only [bitSubtractWithWork, List.length_cons] at *
      omega



theorem binaryNaturalSubtractWithWork_cost (a b : ℕ) :
    (binaryNaturalSubtractWithWork a b).2 ≤ 9 * (Nat.size a + Nat.size b) + 1 := by
  simpa only [binaryNaturalSubtractWithWork, Nat.size_eq_bits_len] using
    bitSubtractWithWork_cost a.bits b.bits false

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_SignedBinaryWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Signed integers represented by a sign bit and a Boolean magnitude word.
Arithmetic uses Boolean ripple and shift-add routines. -/

namespace EditApproximation





namespace SignedBinary











theorem mulWithWork_cost (a b : SignedBinary) :
    (a.mulWithWork b).2 ≤ 24 * (a.bits.length + b.bits.length + 1) ^ 2 := by
  have hmul := bitMulWithWork_cost a.bits b.bits
  change (bitMulWithWork a.bits b.bits).2 + 4 ≤ _
  nlinarith only [hmul]

theorem mulWithWork_length (a b : SignedBinary) :
    (a.mulWithWork b).1.bits.length ≤ 2 * a.bits.length + b.bits.length + 1 :=
  bitMulWithWork_length a.bits b.bits

end SignedBinary
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryFractionWork
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
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





theorem mulWithWork_cost (a b : BinaryFraction) (B : ℕ) (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (a.mulWithWork b).2 ≤ 1000 * (B + 1) ^ 2 := by
  have han : a.numerator.bits.length ≤ B := (le_max_left _ _).trans ha
  have had : a.denominator.length ≤ B := (le_max_right _ _).trans ha
  have hbn : b.numerator.bits.length ≤ B := (le_max_left _ _).trans hb
  have hbd : b.denominator.length ≤ B := (le_max_right _ _).trans hb
  have hnum := SignedBinary.mulWithWork_cost a.numerator b.numerator
  have hden := bitMulWithWork_cost a.denominator b.denominator
  change (a.numerator.mulWithWork b.numerator).2 + (bitMulWithWork a.denominator b.denominator).2 + 4 ≤ _
  nlinarith only [han, had, hbn, hbd, hnum, hden,
    Nat.mul_self_le_mul_self (show a.numerator.bits.length + b.numerator.bits.length + 1 ≤ 2 * B + 1 by omega),
    Nat.mul_le_mul (show a.denominator.length + 1 ≤ B + 1 by omega)
      (show a.denominator.length + b.denominator.length + 1 ≤ 2 * B + 1 by omega)]







end BinaryFraction
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

theorem canonicalizeWithWork_cost (a : BinaryFraction) :
    (canonicalizeWithWork a).2 ≤ 6 * a.width + 4 := by
  have hn : a.numerator.bits.length ≤ a.width := le_max_left _ _
  have hd : a.denominator.length ≤ a.width := le_max_right _ _
  simp only [canonicalizeWithWork, trimBitWordWithWork_cost]
  omega





theorem rawMul_width (a b : BinaryFraction) (B : ℕ) (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (a.mulWithWork b).1.width ≤ 3 * B + 1 := by
  have han : a.numerator.bits.length ≤ B := (le_max_left _ _).trans ha
  have had : a.denominator.length ≤ B := (le_max_right _ _).trans ha
  have hbn : b.numerator.bits.length ≤ B := (le_max_left _ _).trans hb
  have hbd : b.denominator.length ≤ B := (le_max_right _ _).trans hb
  have hnum := SignedBinary.mulWithWork_length a.numerator b.numerator
  have hden := bitMulWithWork_length a.denominator b.denominator
  dsimp only [mulWithWork, width]
  apply max_le <;> omega

theorem canonicalMulWithWork_cost (a b : BinaryFraction) (B : ℕ) (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (canonicalMulWithWork a b).2 ≤ 2000 * (B + 1) ^ 2 := by
  have hr := mulWithWork_cost a b B ha hb
  have hw := rawMul_width a b B ha hb
  have hc := canonicalizeWithWork_cost (a.mulWithWork b).1
  change (a.mulWithWork b).2 + (canonicalizeWithWork (a.mulWithWork b).1).2 ≤ _
  nlinarith only [hr, hw, hc]

theorem canonicalizeWithWork_width_le_storageBits (a : BinaryFraction) :
    (canonicalizeWithWork a).1.width ≤ a.representation.storageBits := by
  rw [canonicalizeWithWork_width]
  unfold UnreducedRational.storageBits
  exact max_le (by omega) (by omega)

theorem canonicalMulWithWork_width_le_storageBits (a b : BinaryFraction) :
    (canonicalMulWithWork a b).1.width ≤
      (a.representation.mul b.representation).storageBits := by
  have h := canonicalizeWithWork_width_le_storageBits (a.mulWithWork b).1
  rw [mulWithWork_representation] at h
  exact h

theorem canonicalMulWithWork_self_width (a b : BinaryFraction) :
    (canonicalMulWithWork a b).1.width ≤ (canonicalMulWithWork a b).1.representation.storageBits := by
  rw [canonicalMulWithWork_representation]
  exact canonicalMulWithWork_width_le_storageBits a b

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

theorem storageBits_mul (a b : UnreducedRational) :
    (a.mul b).storageBits ≤ a.storageBits + b.storageBits := by
  have hnum := natural_product_bit_length a.num.natAbs b.num.natAbs
  have hden := mul_den_bits a b
  simp only [mul, storageBits, Int.natAbs_mul] at *
  omega

end UnreducedRational
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRawCost
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bit-operation bounds for the literal Boolean arithmetic calls and
bounded-width power loops used inside the entropy optimizer. -/

namespace EditApproximation
namespace BinaryFraction

theorem representation_storageBits_le (a : BinaryFraction) :
    a.representation.storageBits ≤ 2 * a.width + 1 := by
  have hn : Nat.size (bitWordValue a.numerator.bits) ≤ a.numerator.bits.length :=
    Nat.size_le.mpr (bitWordValue_lt_pow_length _)
  have hd : Nat.size (bitWordValue a.denominator) ≤ a.denominator.length :=
    Nat.size_le.mpr (bitWordValue_lt_pow_length _)
  have hmag : a.numerator.value.natAbs = bitWordValue a.numerator.bits := by
    cases h : a.numerator.negative <;> simp [SignedBinary.value, signedMagnitude, h]
  have hnw : a.numerator.bits.length ≤ a.width := le_max_left _ _
  have hdw : a.denominator.length ≤ a.width := le_max_right _ _
  simp only [representation, UnreducedRational.storageBits, hmag]
  omega

end BinaryFraction
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryAffineGuard
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Boolean tests for the affine errors in band membership.  The literal
product, both subtractions and final comparison have charged bit work. -/

namespace EditApproximation
namespace BinaryFraction

theorem canonicalMulWithWork_width (a b : BinaryFraction) (B : ℕ)
    (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (a.canonicalMulWithWork b).1.width ≤ 4 * B + 2 := by
  have hs := UnreducedRational.storageBits_mul a.representation b.representation
  have ha' := representation_storageBits_le a
  have hb' := representation_storageBits_le b
  have hw := canonicalMulWithWork_self_width a b
  rw [canonicalMulWithWork_representation] at hw
  omega



end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryDivisionWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Binary long division. A high-prefix quotient and remainder are extended
by one source bit, then compared with the positive divisor and reduced by
at most one ripple-borrow subtraction. -/

namespace EditApproximation



theorem bitDivModWithWork_lengths (divisor bits : List Bool) :
    (bitDivModWithWork divisor bits).1.length = bits.length ∧
      (bitDivModWithWork divisor bits).2.1.length ≤ bits.length + divisor.length := by
  induction bits with
  | nil => simp [bitDivModWithWork]
  | cons bit bits ih =>
    simp only [bitDivModWithWork]
    split_ifs
    · simp only [List.length_cons]
      exact ⟨by omega, by omega⟩
    · have hs := bitSubtractWithWork_length (bit :: (bitDivModWithWork divisor bits).2.1) divisor false
      simp only [List.length_cons] at hs ⊢
      exact ⟨by omega, by omega⟩

theorem bitDivModWithWork_cost (divisor bits : List Bool) :
    (bitDivModWithWork divisor bits).2.2 ≤
      30 * (bits.length + 1) * (bits.length + divisor.length + 1) := by
  induction bits with
  | nil => simp [bitDivModWithWork]; omega
  | cons bit bits ih =>
    have hl := (bitDivModWithWork_lengths divisor bits).2
    have hc := bitCompareWithWork_cost (bit :: (bitDivModWithWork divisor bits).2.1) divisor
    have hs := bitSubtractWithWork_cost (bit :: (bitDivModWithWork divisor bits).2.1) divisor false
    simp only [List.length_cons] at hc hs
    simp only [bitDivModWithWork, List.length_cons]
    split_ifs <;> nlinarith only [ih, hl, hc, hs]



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCeilingWork
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Exact natural ceilings from the executed binary quotient and remainder.
Negative fractions have natural ceiling zero, as in the seed update. -/

namespace EditApproximation



theorem bitCeilDivWithWork_length (divisor bits : List Bool) :
    (bitCeilDivWithWork divisor bits).1.length ≤ bits.length + 2 := by
  have hq := (bitDivModWithWork_lengths divisor bits).1
  have ha := bitAddWithWork_length (bitDivModWithWork divisor bits).1 [true] false
  unfold bitCeilDivWithWork
  dsimp only
  split_ifs <;> dsimp only
  · omega
  · simp only [List.length_cons, List.length_nil] at ha
    omega

theorem bitCeilDivWithWork_cost (divisor bits : List Bool) :
    (bitCeilDivWithWork divisor bits).2 ≤
      100 * (bits.length + divisor.length + 1) ^ 2 := by
  have hdiv := bitDivModWithWork_cost divisor bits
  have hl := bitDivModWithWork_lengths divisor bits
  have hc := bitCompareWithWork_cost (bitDivModWithWork divisor bits).2.1 []
  have ha := bitAddWithWork_cost (bitDivModWithWork divisor bits).1 [true] false
  simp only [List.length_nil, List.length_cons, Nat.add_zero] at hc ha
  unfold bitCeilDivWithWork
  dsimp only
  split_ifs <;> dsimp only <;> nlinarith only [hdiv, hl.1, hl.2, hc, ha]

namespace BinaryFraction



theorem naturalCeilingWithWork_cost (a : BinaryFraction) :
    (a.naturalCeilingWithWork).2 ≤ 500 * (a.width + 1) ^ 2 := by
  have hn : a.numerator.bits.length ≤ a.width := le_max_left _ _
  have hd : a.denominator.length ≤ a.width := le_max_right _ _
  have hc := bitCeilDivWithWork_cost a.denominator a.numerator.bits
  unfold naturalCeilingWithWork
  split_ifs <;> dsimp only
  · nlinarith only [Nat.zero_le a.width]
  · have hm := Nat.mul_self_le_mul_self (show a.numerator.bits.length + a.denominator.length + 1 ≤
        2 * a.width + 1 by omega)
    nlinarith only [hc, hm, Nat.zero_le a.width]

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedPhysicalRequest
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Coarse seed computations are explicit cache requests, alongside the
bounded warmup/refinement requests. Their rank is below every table request,
so first exposure of a same-node coarse entry is a genuine leaf of the lazy program. -/

namespace EditApproximation



namespace ChargedPhysicalRequest









 theorem coarse_rank_lt {M J ny passes copies T S : ℕ} (entry : PhysicalEntry M J ny)
    (request : {request : PhysicalTableRequest M J ny // request.Bounded passes copies T S})
    (hnode : entry.1 = request.val.node) :
    rank (Sum.inl entry : ChargedPhysicalRequest M J ny passes copies T S) < rank (Sum.inr request) := by
  change J - entry.1.1.val + 0 < request.val.remainingDepth + (request.val.rank T S + 1)
  rw [hnode]
  unfold PhysicalTableRequest.remainingDepth
  omega

end ChargedPhysicalRequest

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryMedianKernel
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.queryNaturalLEWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Binary multiplication, natural ceiling, sorting and clamping for the
literal seed median. The stored words are sorted without decoding them. -/

namespace EditApproximation

theorem wordLEWithWork_cost (a b : List Bool) :
    (wordLEWithWork a b).2 ≤ 4 * (a.length + b.length) + 2 := by
  have h := bitCompareWithWork_cost b a
  change _ + 1 ≤ _
  omega



theorem wordMinWithWork_length (a b : List Bool) :
    (wordMinWithWork a b).1.length ≤ max a.length b.length := by
  unfold wordMinWithWork
  dsimp only
  split_ifs <;> omega



theorem wordInsertWithWork_words (a : List Bool) (words : List (List Bool)) (B : ℕ)
    (ha : a.length ≤ B) (hwords : ∀ b ∈ words, b.length ≤ B) :
    ∀ b ∈ (wordInsertWithWork a words).1, b.length ≤ B := by
  induction words with
  | nil =>
    intro b hb
    have heq : b = a := by simpa only [wordInsertWithWork, List.mem_singleton] using hb
    exact heq ▸ ha
  | cons b rest ih =>
    unfold wordInsertWithWork
    dsimp only
    split_ifs
    · intro c hc
      rcases List.mem_cons.mp hc with heq | hc
      · exact heq ▸ ha
      · exact hwords c hc
    · intro c hc
      rcases List.mem_cons.mp hc with heq | hc
      · exact heq ▸ hwords b (by simp)
      · exact ih (fun d hd => hwords d (by simp [hd])) c hc

theorem wordInsertWithWork_cost (a : List Bool) (words : List (List Bool)) (B : ℕ)
    (ha : a.length ≤ B) (hwords : ∀ b ∈ words, b.length ≤ B) :
    (wordInsertWithWork a words).2 ≤ (words.length + 1) * (8 * B + 4) := by
  induction words with
  | nil => simp only [wordInsertWithWork, List.length_nil, zero_add, one_mul]; omega
  | cons b rest ih =>
    have hb := hwords b (by simp)
    have hcmp := wordLEWithWork_cost a b
    have htail := ih (fun c hc => hwords c (by simp [hc]))
    unfold wordInsertWithWork
    dsimp only
    simp only [List.length_cons]
    rw [show rest.length + 1 + 1 = (rest.length + 1) + 1 by omega, Nat.add_mul, Nat.one_mul]
    split_ifs <;> omega



theorem wordSortWithWork_length (words : List (List Bool)) :
    (wordSortWithWork words).1.length = words.length := by
  have h := congrArg List.length (wordSortWithWork_value words)
  simpa only [List.length_map, List.length_insertionSort] using h

theorem wordSortWithWork_words (words : List (List Bool)) (B : ℕ)
    (hwords : ∀ b ∈ words, b.length ≤ B) :
    ∀ b ∈ (wordSortWithWork words).1, b.length ≤ B := by
  induction words with
  | nil => simp only [wordSortWithWork, List.not_mem_nil, false_implies, implies_true]
  | cons a rest ih =>
    exact wordInsertWithWork_words a (wordSortWithWork rest).1 B (hwords a (by simp))
      (ih (fun b hb => hwords b (by simp [hb])))

theorem wordSortWithWork_cost (words : List (List Bool)) (B : ℕ)
    (hwords : ∀ b ∈ words, b.length ≤ B) :
    (wordSortWithWork words).2 ≤ (words.length + 1) ^ 2 * (8 * B + 6) := by
  induction words with
  | nil => simp only [wordSortWithWork, List.length_nil, zero_add, one_pow, one_mul]; omega
  | cons a rest ih =>
    have hr : ∀ b ∈ rest, b.length ≤ B := fun b hb => hwords b (by simp [hb])
    have ht := ih hr
    have hi := wordInsertWithWork_cost a (wordSortWithWork rest).1 B (hwords a (by simp))
      (wordSortWithWork_words rest B hr)
    rw [wordSortWithWork_length] at hi
    change _ + _ + 2 ≤ _
    simp only [List.length_cons]
    nlinarith only [ht, hi, Nat.zero_le rest.length, Nat.zero_le B]

namespace BinaryFraction

theorem naturalCeilingWithWork_length (a : BinaryFraction) :
    (a.naturalCeilingWithWork).1.length ≤ a.width + 2 := by
  have hn : a.numerator.bits.length ≤ a.width := le_max_left _ _
  have h := bitCeilDivWithWork_length a.denominator a.numerator.bits
  unfold naturalCeilingWithWork
  split_ifs
  · change 0 ≤ a.width + 2
    omega
  · change (bitCeilDivWithWork a.denominator a.numerator.bits).1.length ≤ a.width + 2
    omega



theorem scaledCeilingWithWork_bounds (multiplier : ℕ) (a : BinaryFraction) (B : ℕ)
    (hm : Nat.size multiplier + 2 ≤ B) (ha : a.width ≤ B) :
    (scaledCeilingWithWork multiplier a).1.length ≤ 4 * B + 4 ∧
      (scaledCeilingWithWork multiplier a).2 ≤ scaledCeilingBitBudget B := by
  have hm' : (nat multiplier).width ≤ B := (nat_width_le _).trans hm
  have hpw := canonicalMulWithWork_width (nat multiplier) a B hm' ha
  have hpc := canonicalMulWithWork_cost (nat multiplier) a B hm' ha
  have hcw := naturalCeilingWithWork_length (canonicalMulWithWork (nat multiplier) a).1
  have hcc := naturalCeilingWithWork_cost (canonicalMulWithWork (nat multiplier) a).1
  have hs := Nat.pow_le_pow_left (show (canonicalMulWithWork (nat multiplier) a).1.width + 1 ≤
      4 * B + 3 by omega) 2
  constructor
  · change (naturalCeilingWithWork (canonicalMulWithWork (nat multiplier) a).1).1.length ≤ _
    omega
  · change _ + _ + _ + 3 ≤ _
    unfold scaledCeilingBitBudget
    omega

theorem medianSeedWithWork_bounds (N multiplier : ℕ) (values : List BinaryFraction) (B : ℕ)
    (hN : Nat.size N ≤ B) (hm : Nat.size multiplier + 2 ≤ B)
    (hv : ∀ a ∈ values, a.width ≤ B) :
    (medianSeedWithWork N multiplier values).1.length ≤ 4 * B + 4 ∧
      (medianSeedWithWork N multiplier values).2 ≤ medianSeedBitBudget values.length B := by
  let rounded := arithmeticMapWithWork (scaledCeilingWithWork multiplier) values
  have hlen : rounded.1.length = values.length := by
    simp only [rounded, arithmeticMapWithWork_value, List.length_map]
  have hrounded : ∀ word ∈ rounded.1, word.length ≤ 4 * B + 4 := by
    intro word hword
    simp only [rounded, arithmeticMapWithWork_value] at hword
    obtain ⟨a, ha, heq⟩ := List.mem_map.mp hword
    subst word
    exact (scaledCeilingWithWork_bounds multiplier a B hm (hv a ha)).1
  have hmc := arithmeticMapWithWork_cost (scaledCeilingWithWork multiplier) values
    (scaledCeilingBitBudget B) (fun a ha => (scaledCeilingWithWork_bounds multiplier a B hm (hv a ha)).2)
  have hsort := wordSortWithWork_cost rounded.1 (4 * B + 4) hrounded
  rw [hlen] at hsort
  let middle := (wordSortWithWork rounded.1).1.getD (values.length / 2) []
  have hmid : middle.length ≤ 4 * B + 4 := by
    by_cases hi : values.length / 2 < (wordSortWithWork rounded.1).1.length
    · dsimp only [middle]
      rw [List.getD_eq_getElem _ _ hi]
      exact wordSortWithWork_words rounded.1 (4 * B + 4) hrounded _ (List.getElem_mem hi)
    · simp only [middle, List.getD_eq_default _ _ (Nat.le_of_not_gt hi), List.length_nil]
      omega
  have hc := wordLEWithWork_cost N.bits middle
  have hn : N.bits.length ≤ B := by simpa only [← Nat.size_eq_bits_len] using hN
  have hl := wordMinWithWork_length N.bits middle
  constructor
  · change (wordMinWithWork N.bits middle).1.length ≤ _
    omega
  · change rounded.2 + (wordSortWithWork rounded.1).2 + values.length +
      ((wordLEWithWork N.bits middle).2 + 1) + Nat.size N + 3 ≤ _
    unfold medianSeedBitBudget
    change rounded.2 ≤ _ at hmc
    omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Local endpoint lists executed with binary division, multiplication,
subtraction and validity comparisons. Only the bounded grid-index range
is visited. -/

namespace EditApproximation



theorem saturatingSubtractWithWork_cost (a b : ℕ) :
    (saturatingSubtractWithWork a b).2 ≤ 13 * (Nat.size a + Nat.size b) + 4 := by
  have htest := binaryNaturalCompareWithWork_cost a b
  have hsub := binaryNaturalSubtractWithWork_cost a b
  unfold saturatingSubtractWithWork
  dsimp only
  split_ifs <;> omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySeedMedianWork
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The natural seed cache stores a trimmed result, so repeated median
passes do not accumulate leading zero words. The trimming scan is charged. -/

namespace EditApproximation
namespace BinaryFraction



theorem seedMedianWithWork_length (N multiplier : ℕ) (values : List BinaryFraction) :
    (seedMedianWithWork N multiplier values).1.length ≤ Nat.size N := by
  simp only [seedMedianWithWork, trimBitWordWithWork_length, medianSeedWithWork_value]
  exact Nat.size_le_size (Nat.min_le_left _ _)

theorem seedMedianWithWork_cost (N multiplier : ℕ) (values : List BinaryFraction) (B : ℕ)
    (hN : Nat.size N ≤ B) (hm : Nat.size multiplier + 2 ≤ B)
    (hv : ∀ a ∈ values, a.width ≤ B) :
    (seedMedianWithWork N multiplier values).2 ≤ seedMedianBitBudget values.length B := by
  have hmedian := medianSeedWithWork_bounds N multiplier values B hN hm hv
  have htrim := trimBitWordWithWork_cost (medianSeedWithWork N multiplier values).1
  change (medianSeedWithWork N multiplier values).2 +
    (trimBitWordWithWork (medianSeedWithWork N multiplier values).1).2 + 1 ≤ _
  unfold seedMedianBitBudget
  omega

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

theorem work_bind {ι α β : Type*} (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (program : BitQuery ι α) (next : α → BitQuery ι β) :
    (program.bind next).work oracle readWork =
      program.work oracle readWork + (next (program.value oracle)).work oracle readWork := by
  induction program with
  | done result => simp only [bind, work, value, Nat.zero_add]
  | read key continuation ih => simp only [bind, work, value, ih, Nat.add_assoc]
  | charge steps continuation ih => simp only [bind, work, value, ih, Nat.add_assoc]

/- A local charged step executes a Boolean routine with an explicit cost. -/


theorem value_collect {ι κ β : Type*} (oracle : ι → BinaryFraction)
    (reader : κ → BitQuery ι BinaryFraction) (inputs : List κ)
    (next : List BinaryFraction → BitQuery ι β) :
    (collect reader inputs next).value oracle =
      (next (inputs.map fun key => (reader key).value oracle)).value oracle := by
  induction inputs generalizing next with
  | nil => rfl
  | cons key inputs ih => simp only [collect, value_bind, value, ih, List.map_cons]

theorem work_collect {ι κ β : Type*} (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (reader : κ → BitQuery ι BinaryFraction) (inputs : List κ)
    (next : List BinaryFraction → BitQuery ι β) :
    (collect reader inputs next).work oracle readWork =
      (inputs.map fun key => (reader key).work oracle readWork + 3).sum +
      (next (inputs.map fun key => (reader key).value oracle)).work oracle readWork := by
  induction inputs generalizing next with
  | nil => simp only [collect, List.map_nil, List.sum_nil, Nat.zero_add]
  | cons key inputs ih =>
    simp only [collect, work_bind, work, ih, List.map_cons, List.sum_cons, Nat.add_assoc]

end BitQuery
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseDescriptorWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

theorem saturatingSubtractWithWork_length (a b : ℕ) :
    (saturatingSubtractWithWork a b).1.length ≤ max (Nat.size a) (Nat.size b) := by
  unfold saturatingSubtractWithWork
  dsimp only
  split_ifs
  · exact Nat.zero_le _
  · simpa only [binaryNaturalSubtractWithWork, bitSubtractWithWork_length,
      Nat.size_eq_bits_len] using (le_refl (max (Nat.size a) (Nat.size b)))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_MemoCodeWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Address generation is charged separately from binary trie traversal.
The loops visit only coordinates in a key, never the ambient key space. -/
namespace EditApproximation



 theorem physicalNodeCodeWithWork_cost {M J : ℕ} (node : PhysicalNode M J) :
    (physicalNodeCodeWithWork node).2 ≤ 5 * J + 5 := by
  have h := node.1.isLt
  simp only [physicalNodeCodeWithWork, treeLayerCodeWithWork_cost, parameterPowerWithWork_spec]
  omega



 theorem physicalEntryCodeWithWork_cost {M J n : ℕ} (entry : PhysicalEntry M J n) :
    (physicalEntryCodeWithWork entry).2 ≤ 5 * J + 13 := by
  have h := physicalNodeCodeWithWork_cost entry.1
  change (physicalNodeCodeWithWork entry.1).2 + 8 ≤ _
  omega



 theorem physicalTableCodeWithWork_cost {M J n : ℕ} (copies T S : ℕ)
    (request : PhysicalTableRequest M J n) :
    (physicalTableCodeWithWork copies T S request).2 ≤ 7 * J + 29 := by
  have he := physicalEntryCodeWithWork_cost (request.node, request.state)
  simp only [physicalTableCodeWithWork, parameterPowerWithWork_spec]
  omega



 theorem chargedPhysicalCodeWithWork_cost {M J n passes copies T S : ℕ}
    (request : ChargedPhysicalRequest M J n passes copies T S) :
    (chargedPhysicalCodeWithWork request).2 ≤ 7 * J + 32 := by
  cases request with
  | inl entry => have h := physicalEntryCodeWithWork_cost entry
                 change (physicalEntryCodeWithWork entry).2 + 2 ≤ _
                 omega
  | inr request => have h := physicalTableCodeWithWork_cost copies T S request.val
                   change (physicalTableCodeWithWork copies T S request.val).2 + 3 ≤ _
                   omega



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryChargedSeedCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BitQuery.Heap.footprint_bind _root_.OAI.EditApproximation.BitQuery.Heap.footprint_charge _root_.OAI.EditApproximation.BitQuery.Heap.footprint_chargeOf _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_compute _root_.OAI.EditApproximation.BitQuery.Heap.footprint_computeOf _root_.OAI.EditApproximation.BitQuery.Heap.footprint_done _root_.OAI.EditApproximation.BitQuery.Heap.footprint_mapKeysWithWork _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalMedianUpdateTable_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalBoundedWithWork_value _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.querySupportedChildWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Seed
variable {M J n passes copies T S : ℕ}
  (parent : {r : PhysicalTableRequest M J n // r.Bounded passes copies T S})
  (oracle : {child : ChargedPhysicalRequest M J n passes copies T S //
    child.rank < ChargedPhysicalRequest.rank (.inr parent)} → BinaryFraction)
  (readWork : {child : ChargedPhysicalRequest M J n passes copies T S //
    child.rank < ChargedPhysicalRequest.rank (.inr parent)} → ℕ)

theorem queryChargedRead_work_bound (C : ℕ) (hc : ∀ key, readWork key ≤ C) (key) :
    (queryChargedRead parent key).work oracle readWork ≤ 7 * J + 33 + C := by
  have h := chargedPhysicalCodeWithWork_cost key.val
  have hr := hc key
  simp only [queryChargedRead, BitQuery.work]
  omega

private theorem seed_sum_bound {κ : Type*} (keys : List κ) (cost : κ → ℕ) (C : ℕ)
    (hc : ∀ key, cost key ≤ C) : (keys.map cost).sum ≤ keys.length * C := by
  induction keys with
  | nil => simp
  | cons key keys ih =>
    have h := hc key
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem queryChargedSeedAt_bounds (N B C : ℕ) (multiplier : ℕ → ℕ) (q : TargetInterval n)
    (hB : 1 ≤ B) (hN : Nat.size N ≤ B) (hp : Nat.size parent.val.pass ≤ B)
    (hm : Nat.size (multiplier (parent.val.pass - 1)) + 2 ≤ B)
    (hv : ∀ key, (oracle key).width ≤ B) (hc : ∀ key, readWork key ≤ C) :
    ((queryChargedSeedAt parent N multiplier q).value oracle).width ≤ B ∧
      (queryChargedSeedAt parent N multiplier q).work oracle readWork ≤
        queryChargedSeedBitBudget copies J B C := by
  have heq := naturalEqualWithWork_cost parent.val.pass 0 B hp (by simp)
  have hr (key) := queryChargedRead_work_bound parent oracle readWork C hc key
  unfold queryChargedSeedAt
  split
  · constructor
    · exact hv _
    · simp only [BitQuery.work]
      have := hr ⟨.inl (parent.val.node, q), ChargedPhysicalRequest.coarse_rank_lt _ parent rfl⟩
      change (naturalEqualWithWork parent.val.pass 0).2 + 1 +
        (queryChargedRead parent _).work oracle readWork ≤ _
      unfold queryChargedSeedBitBudget
      omega
  · rename_i hpass
    let hpos := Nat.pos_of_ne_zero (fun h => hpass ((naturalEqualWithWork_value _ _).mpr h))
    let reader := queryChargedPreviousRead parent hpos q
    let words := (List.finRange copies).map fun copy => (reader copy).value oracle
    have hlen : words.length = copies := by simp only [words, List.length_map, List.length_finRange]
    have hwords : ∀ word ∈ words, word.width ≤ B := by
      intro word hw
      obtain ⟨copy, _, rfl⟩ := List.mem_map.mp hw
      exact hv _
    have hmedian := BinaryFraction.seedMedianWithWork_cost N (multiplier (parent.val.pass - 1)) words B hN hm hwords
    have hlength := BinaryFraction.seedMedianWithWork_length N (multiplier (parent.val.pass - 1)) words
    have hsum := seed_sum_bound (List.finRange copies) (fun copy => (reader copy).work oracle readWork + 3)
      (7 * J + 33 + C + 3) (fun copy => Nat.add_le_add_right (hr _) 3)
    simp only [List.length_finRange] at hsum
    rw [hlen] at hmedian
    constructor
    · simp only [BitQuery.value, BitQuery.value_collect, BitQuery.compute,
        BinaryFraction.querySeedMedianWithWork, BinaryFraction.ofNaturalWord_width]
      exact max_le (hlength.trans hN) hB
    · simp only [BitQuery.work, BitQuery.work_collect, BitQuery.compute, Nat.add_zero]
      change (naturalEqualWithWork parent.val.pass 0).2 + 1 +
        (copies + 1 + (((List.finRange copies).map fun copy => (reader copy).work oracle readWork + 3).sum +
          (BinaryFraction.querySeedMedianWithWork N (multiplier (parent.val.pass - 1)) words).2)) ≤ _
      unfold BinaryFraction.querySeedMedianWithWork queryChargedSeedBitBudget
      dsimp only
      omega

end Seed
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryIndexedSlice
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A terminal source interval is accessed through its stored endpoint.
Its substring is used only in the specification, never materialized. -/

namespace EditApproximation



theorem querySliceHeadWithWork_cost {α : Type*} (source : List α)
    (interval : TargetInterval source.length) (B : ℕ) (hB : Nat.size source.length ≤ B) :
    (querySliceHeadWithWork source interval).2 ≤ 10 * B + 4 := by
  have hl := (Nat.size_le_size (interval.ordered.trans interval.valid)).trans hB
  have hh := (Nat.size_le_size interval.valid).trans hB
  have hc := binaryNaturalCompareWithWork_cost interval.lo interval.hi
  change _ + _ + _ + 3 ≤ _
  omega



theorem queryIndexedSliceWithWork_cost (source : List ℕ)
    (interval : TargetInterval source.length) (targetLength : ℕ) (q : TargetInterval targetLength)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits B : ℕ)
    (hB : Nat.size source.length ≤ B) :
    (queryIndexedSliceWithWork source interval targetLength q occurrence symbolBits positionBits).2 ≤
      10 * B + 2 * symbolBits + 4 * positionBits + Nat.size (targetLength + 1) + 17 := by
  have hs := querySliceHeadWithWork_cost source interval B hB
  have hr := (binaryIndexedLeafWithWork_bounds occurrence symbolBits positionBits
    (querySliceHeadWithWork source interval).1 q.lo q.hi).2
  have hh := Nat.size_le_size (Nat.add_le_add_right q.valid 1)
  change (querySliceHeadWithWork source interval).2 + _ + 1 ≤ _
  omega

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

/-- The slice test reads only the stored endpoints; it does not materialize the substring. -/
theorem querySliceTest_cost {α : Type*} (source : List α) (interval : TargetInterval source.length)
    (B : ℕ) (hB : Nat.size source.length ≤ B) :
    (saturatingSubtractWithWork interval.hi interval.lo).2 +
      (wordLEWithWork (saturatingSubtractWithWork interval.hi interval.lo).1 [true]).2 + 2 ≤ 30 * B + 20 := by
  have hlo := (Nat.size_le_size (interval.ordered.trans interval.valid)).trans hB
  have hhi := (Nat.size_le_size interval.valid).trans hB
  have hs := saturatingSubtractWithWork_cost interval.hi interval.lo
  have hl := (saturatingSubtractWithWork_length interval.hi interval.lo).trans (max_le hhi hlo)
  have ht := wordLEWithWork_cost (saturatingSubtractWithWork interval.hi interval.lo).1 [true]
  simp only [List.length_cons, List.length_nil] at ht
  omega

section Initial
variable (source target : List ℕ) {M J passes copies T S : ℕ}
  (N P F Amax B C : ℕ) (A a : BinaryFraction) (multiplier : ℕ → ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (oracle : {child : ChargedPhysicalRequest M J target.length passes copies T S //
    child.rank < ChargedPhysicalRequest.rank (.inr parent)} → BinaryFraction)
  (readWork : {child : ChargedPhysicalRequest M J target.length passes copies T S //
    child.rank < ChargedPhysicalRequest.rank (.inr parent)} → ℕ)

theorem queryPhysicalInitial_work_bound (q : TargetInterval target.length)
    (hB : 8 ≤ B) (hP : 0 < P) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B)
    (hF : Nat.size F ≤ B) (hs : Nat.size source.length ≤ B) (ht : Nat.size (target.length + 1) ≤ B)
    (hA : A.width ≤ B) (ha : a.width ≤ B) (hAone : 1 ≤ A.value) (hAmax : A.value ≤ Amax)
    (hp : Nat.size parent.val.pass ≤ B) (hm : Nat.size (multiplier (parent.val.pass - 1)) + 2 ≤ B)
    (hv : ∀ key, (oracle key).width ≤ B) (hc : ∀ key, readWork key ≤ C) :
    (queryPhysicalInitial source target N P F A a multiplier parent occurrence symbolBits positionBits q).work
        oracle readWork ≤ queryPhysicalInitialBitBudget P F Amax copies J symbolBits positionBits B C := by
  let interval := physicalSourceInterval source.length parent.val.node
  have htest := querySliceTest_cost source interval B hs
  have hseed (r : TargetInterval target.length) :=
    queryChargedSeedAt_bounds parent oracle readWork N B C multiplier r (by omega) hN hp hm hv hc
  have hlength : Nat.size (bitWordValue (saturatingSubtractWithWork interval.hi interval.lo).1) ≤ B := by
    rw [saturatingSubtractWithWork_value]
    exact (Nat.size_le_size ((Nat.sub_le _ _).trans interval.valid)).trans hs
  have hi := queryInitialConeProgramAt_work_bound
    (bitWordValue (saturatingSubtractWithWork interval.hi interval.lo).1) N P F Amax B
    (queryChargedSeedBitBudget copies J B C) hP A a (queryChargedSeedAt parent N multiplier) q
    oracle readWork hB hN hPb hF hlength
    ((Nat.size_le_size (Nat.le_succ target.length)).trans ht) hA ha hAone hAmax
    (fun r => (hseed r).1) (fun r => (hseed r).2)
  have hl := (queryIndexedSliceWithWork_cost source interval target.length q occurrence symbolBits positionBits B hs).trans
    (Nat.add_le_add_right (Nat.add_le_add_left ht _) 17)
  unfold queryPhysicalInitial
  simp only [BitQuery.work]
  split
  · simp only [BitQuery.compute, BitQuery.work, Nat.add_zero]
    change (saturatingSubtractWithWork interval.hi interval.lo).2 +
      (wordLEWithWork (saturatingSubtractWithWork interval.hi interval.lo).1 [true]).2 + 2 +
      (queryIndexedSliceWithWork source interval target.length q occurrence symbolBits positionBits).2 ≤ _
    exact (Nat.add_le_add htest hl).trans (by unfold queryPhysicalInitialBitBudget; omega)
  · change (saturatingSubtractWithWork interval.hi interval.lo).2 +
      (wordLEWithWork (saturatingSubtractWithWork interval.hi interval.lo).1 [true]).2 + 2 + _ ≤ _
    exact (Nat.add_le_add htest hi).trans (by unfold queryPhysicalInitialBitBudget; omega)

end Initial
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryChargedWarmupCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryMemo.mapValues_insert _root_.OAI.EditApproximation.BinaryMemo.mapValues_left _root_.OAI.EditApproximation.BinaryMemo.mapValues_lookup _root_.OAI.EditApproximation.BinaryMemo.mapValues_nodes _root_.OAI.EditApproximation.BinaryMemo.mapValues_right _root_.OAI.EditApproximation.BinaryMemo.mapValues_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_bind _root_.OAI.EditApproximation.BitQuery.Heap.footprint_charge _root_.OAI.EditApproximation.BitQuery.Heap.footprint_chargeOf _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_done _root_.OAI.EditApproximation.BitQuery.Heap.footprint_mapKeysWithWork _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.physicalMedianUpdateTable_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryNaturalLEWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalBoundedWithWork_value _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySupportedChildWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Warmup
variable (source target : List ℕ) {M J passes copies T S : ℕ}
  (N P F Amax B C : ℕ) (A a : BinaryFraction) (multiplier : ℕ → ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (oracle : {child : ChargedPhysicalRequest M J target.length passes copies T S //
    child.rank < ChargedPhysicalRequest.rank (.inr parent)} → BinaryFraction)
  (readWork : {child : ChargedPhysicalRequest M J target.length passes copies T S //
    child.rank < ChargedPhysicalRequest.rank (.inr parent)} → ℕ)

theorem queryChargedWarmup_work_bound_oai
    (hB : 10 ≤ B) (hP : 0 < P) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B)
    (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hs : Nat.size source.length + 2 ≤ B) (ht : Nat.size target.length + 2 ≤ B)
    (ht' : Nat.size (target.length + 1) + 2 ≤ B)
    (hinit : Nat.size ((32 * F + 1) * N) + 3 ≤ B)
    (hM : Nat.size M ≤ B) (hJ : Nat.size J ≤ B) (hi : Nat.size parent.val.index ≤ B)
    (hA : A.width ≤ B) (ha : a.width ≤ B) (hAone : 1 ≤ A.value) (hAmax : A.value ≤ Amax)
    (hp : Nat.size parent.val.pass ≤ B) (hm : Nat.size (multiplier (parent.val.pass - 1)) + 2 ≤ B)
    (hv : ∀ key, (oracle key).width ≤ B) (hc : ∀ key, readWork key ≤ C) :
    (queryChargedWarmup source target N P F A a multiplier parent occurrence symbolBits positionBits).work
      oracle readWork ≤ queryChargedWarmupBitBudget M P F Amax copies J symbolBits positionBits B C := by
  let I := queryPhysicalInitialBitBudget P F Amax copies J symbolBits positionBits B C
  let reader := queryPhysicalInitial source target N P F A a multiplier parent occurrence symbolBits positionBits
  have hiR (q : TargetInterval target.length) : (reader q).work oracle readWork ≤ I :=
    queryPhysicalInitial_work_bound source target N P F Amax B C A a multiplier parent occurrence
      symbolBits positionBits oracle readWork q (by omega) hP hN hPb (by omega) (by omega) (by omega)
      hA ha hAone hAmax hp hm hv hc
  have hiW (q : TargetInterval target.length) : ((reader q).value oracle).width ≤ B :=
    queryPhysicalInitial_width source target N P F B A a multiplier parent occurrence symbolBits positionBits
      oracle q hP ht' hinit
  have hzero := naturalEqualWithWork_cost parent.val.index 0 B hi (by simp)
  have hn := (Nat.size_le_size (Nat.le_of_lt_succ parent.val.node.1.isLt)).trans hJ
  have hdepth := binaryNaturalCompareWithWork_cost parent.val.node.1.val J
  have hdepth' : (binaryNaturalCompareWithWork parent.val.node.1.val J).2 ≤ 8 * B + 10 := by omega
  have htest := querySliceTest_cost source (physicalSourceInterval source.length parent.val.node) B (by omega)
  unfold queryChargedWarmup
  simp only [BitQuery.work]
  split
  · change (naturalEqualWithWork parent.val.index 0).2 + 1 + (reader parent.val.state).work oracle readWork ≤ _
    have h := hiR parent.val.state
    unfold queryChargedWarmupBitBudget
    dsimp only
    dsimp only [I] at h
    omega
  · rename_i hnonzero
    have hindex : 0 < parent.val.index :=
      Nat.pos_of_ne_zero (fun h => hnonzero ((naturalEqualWithWork_value _ _).mpr h))
    split
    · split
      · have h := hiR parent.val.state
        change (naturalEqualWithWork parent.val.index 0).2 + 1 +
          ((binaryNaturalCompareWithWork parent.val.node.1.val J).2 + 1 +
          (_ + (reader parent.val.state).work oracle readWork)) ≤ _
        unfold queryChargedWarmupBitBudget
        dsimp only
        dsimp only [I] at h
        omega
      · rename_i hbelow hlong
        have hcR (input : Fin M × TargetInterval target.length) :
            (queryChargedWarmupChild parent ((binaryNaturalCompareWithWork_lt _ _).mp hbelow) hindex input).work
              oracle readWork ≤ I + 7 * J + 33 + C := by
          exact (queryChargedRead_work_bound parent oracle readWork C hc _).trans (by omega)
        have hw := queryWarmupProgram_work_bound (physicalSourceInterval source.length parent.val.node)
          N P F B (I + 7 * J + 33 + C) hP a reader
          (queryChargedWarmupChild parent ((binaryNaturalCompareWithWork_lt _ _).mp hbelow) hindex) parent.val.state
          oracle readWork hB hN hF hFpos hPb hs ht hM ha hiW (fun input => hv _)
          (fun r => (hiR r).trans (by omega)) hcR
        change (naturalEqualWithWork parent.val.index 0).2 + 1 +
          ((binaryNaturalCompareWithWork parent.val.node.1.val J).2 + 1 +
          (_ + (queryWarmupProgram _ N P F a reader _ parent.val.state).work oracle readWork)) ≤ _
        unfold queryChargedWarmupBitBudget
        dsimp only
        dsimp only [I] at hw
        omega
    · have h := hiR parent.val.state
      change (naturalEqualWithWork parent.val.index 0).2 + 1 +
        ((binaryNaturalCompareWithWork parent.val.node.1.val J).2 + 1 +
        (reader parent.val.state).work oracle readWork) ≤ _
      unfold queryChargedWarmupBitBudget
      dsimp only
      dsimp only [I] at h
      omega

end Warmup
end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.queryChargedWarmup_work_bound_oai := @OAI.EditApproximation.queryChargedWarmup_work_bound_oai
