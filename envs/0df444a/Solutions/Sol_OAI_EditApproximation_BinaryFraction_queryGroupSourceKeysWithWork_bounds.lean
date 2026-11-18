-- Prove2me | solution 1 for OAI.EditApproximation.BinaryFraction.queryGroupSourceKeysWithWork_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:29:41.42071+00:00
-- url     : https://prove2.me/submissions/a4c13fa0-83cf-4ca7-b38f-91955d9e43bd

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
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_OAIQ361V3Ea002

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

theorem binaryNaturalAddWithWork_cost (a b : ℕ) :
    (binaryNaturalAddWithWork a b).2 ≤ 9 * (Nat.size a + Nat.size b) + 1 := by
  simpa only [binaryNaturalAddWithWork, Nat.size_eq_bits_len] using
    bitAddWithWork_cost a.bits b.bits false



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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_SignedBinaryOrderWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Signed comparisons performed on Boolean magnitude words, including the
noncanonical negative-zero representation. -/

namespace EditApproximation
namespace SignedBinary



theorem nonzeroWithWork_cost (bits : List Bool) :
    (nonzeroWithWork bits).2 ≤ 4 * bits.length + 2 := by
  have h := bitCompareWithWork_cost bits []
  simp only [List.length_nil, Nat.add_zero] at h
  change (bitCompareWithWork bits []).2 + 1 ≤ _
  omega

theorem ltWithWork_cost (a b : SignedBinary) :
    (a.ltWithWork b).2 ≤ 4 * (a.bits.length + b.bits.length) + 8 := by
  have hab := bitCompareWithWork_cost a.bits b.bits
  have hba := bitCompareWithWork_cost b.bits a.bits
  have ha := nonzeroWithWork_cost a.bits
  have hb := nonzeroWithWork_cost b.bits
  cases hna : a.negative <;> cases hnb : b.negative <;>
    simp only [ltWithWork, hna, hnb, Bool.false_eq_true, ↓reduceIte] <;> omega

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







theorem invWithWork_cost (a : BinaryFraction) :
    (a.invWithWork).2 ≤ 4 * a.width + 3 := by
  have h := bitCompareWithWork_cost a.numerator.bits []
  have hn : a.numerator.bits.length ≤ a.width := le_max_left _ _
  simp only [List.length_nil, Nat.add_zero] at h
  unfold invWithWork
  dsimp only
  split_ifs <;> omega

theorem ltWithWork_cost (a b : BinaryFraction) (B : ℕ) (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (a.ltWithWork b).2 ≤ 1000 * (B + 1) ^ 2 := by
  have han : a.numerator.bits.length ≤ B := (le_max_left _ _).trans ha
  have had : a.denominator.length ≤ B := (le_max_right _ _).trans ha
  have hbn : b.numerator.bits.length ≤ B := (le_max_left _ _).trans hb
  have hbd : b.denominator.length ≤ B := (le_max_right _ _).trans hb
  have hl := SignedBinary.mulWithWork_cost a.numerator b.denominatorInteger
  have hr := SignedBinary.mulWithWork_cost b.numerator a.denominatorInteger
  have hll := SignedBinary.mulWithWork_length a.numerator b.denominatorInteger
  have hrl := SignedBinary.mulWithWork_length b.numerator a.denominatorInteger
  have hc := SignedBinary.ltWithWork_cost (a.numerator.mulWithWork b.denominatorInteger).1
    (b.numerator.mulWithWork a.denominatorInteger).1
  simp only [denominatorInteger] at hl hr hll hrl
  change (a.numerator.mulWithWork b.denominatorInteger).2 +
    (b.numerator.mulWithWork a.denominatorInteger).2 +
    ((a.numerator.mulWithWork b.denominatorInteger).1.ltWithWork
      (b.numerator.mulWithWork a.denominatorInteger).1).2 + 4 ≤ _
  simp only [denominatorInteger] at hc ⊢
  nlinarith only [hl, hr, hll, hrl, hc, han, had, hbn, hbd,
    Nat.mul_self_le_mul_self (show a.numerator.bits.length + b.denominator.length + 1 ≤ 2 * B + 1 by omega),
    Nat.mul_self_le_mul_self (show b.numerator.bits.length + a.denominator.length + 1 ≤ 2 * B + 1 by omega)]

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

theorem storageBits_zero : zero.storageBits = 2 := by decide

theorem storageBits_mul (a b : UnreducedRational) :
    (a.mul b).storageBits ≤ a.storageBits + b.storageBits := by
  have hnum := natural_product_bit_length a.num.natAbs b.num.natAbs
  have hden := mul_den_bits a b
  simp only [mul, storageBits, Int.natAbs_mul] at *
  omega

theorem storageBits_inv (a : UnreducedRational) : a.inv.storageBits ≤ a.storageBits + 2 := by
  by_cases h : a.num = 0
  · simp only [inv, h, ↓reduceDIte, storageBits_zero]
    omega
  · simp only [inv, h, ↓reduceDIte, storageBits, Int.natAbs_mul,
      Int.natAbs_sign_of_ne_zero h, Int.natAbs_natCast, Nat.one_mul]
    omega

theorem storageBits_div (a b : UnreducedRational) :
    (a.div b).storageBits ≤ a.storageBits + b.storageBits + 2 := by
  exact (storageBits_mul a b.inv).trans (by have h := storageBits_inv b; omega)

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

theorem invWithWork_width (a : BinaryFraction) : (a.invWithWork).1.width ≤ a.width + 1 := by
  unfold invWithWork
  dsimp only
  split_ifs
  · change 1 ≤ a.width + 1
    omega
  · change max a.denominator.length a.numerator.bits.length ≤ a.width + 1
    rw [max_comm]
    exact Nat.le_add_right _ _

theorem divWithWork_cost (a b : BinaryFraction) (B : ℕ) (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (a.divWithWork b).2 ≤ 2100 * (B + 2) ^ 2 := by
  have hi := invWithWork_cost b
  have hw := invWithWork_width b
  have hm := canonicalMulWithWork_cost a (b.invWithWork).1 (B + 1)
    (by omega) (by omega)
  change (b.invWithWork).2 + (canonicalMulWithWork a (b.invWithWork).1).2 + 1 ≤ _
  nlinarith only [hi, hw, hm, hb]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLogWork
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bit cost of the finite logarithm series on unreduced Boolean fractions.
Every bound is for the executed power/division/addition loops. -/

namespace EditApproximation
namespace BinaryFraction

theorem divWithWork_self_width (a b : BinaryFraction) :
    (a.divWithWork b).1.width ≤ (a.divWithWork b).1.representation.storageBits :=
  canonicalMulWithWork_self_width _ _

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandGroupSampling
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Executable shared group estimates

All dyadic powers in the prescribed closed range are enumerated, including
negative exponents. A scale is evaluated exactly when its sample count
reaches the child count; otherwise one shared array of uniform labels is
used for every member of the group. The selected member is the first
minimizer in the fixed list order.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory



theorem integerClosedRange_mem (lo hi value : ℤ) :
    value ∈ integerClosedRange lo hi ↔ lo ≤ value ∧ value ≤ hi := by
  constructor
  · intro h
    obtain ⟨i, hi', hequal⟩ := List.mem_map.mp h
    have hrange := List.mem_range.mp hi'
    omega
  · rintro ⟨hlower, hupper⟩
    apply List.mem_map.mpr
    refine ⟨(value - lo).toNat, List.mem_range.mpr ?_, ?_⟩ <;> omega



theorem groupDyadicScales_length (M b : ℕ) (F : ℚ) :
    (groupDyadicScales M b F).length =
      (Int.log 2 (64 * F * b) - Int.clog 2 ((b : ℚ) / M) + 1).toNat := by
  simp only [groupDyadicScales, List.length_map, integerClosedRange, List.length_range]

theorem groupDyadicScales_length_dyadic (eM eb eF : ℕ) :
    (groupDyadicScales (2 ^ eM) (2 ^ eb) ((2 : ℚ) ^ eF)).length = 7 + eM + eF := by
  have hlower : ((2 ^ eb : ℕ) : ℚ) / (2 ^ eM : ℕ) = (2 : ℚ) ^ ((eb : ℤ) - eM) := by
    rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0),
      zpow_natCast, zpow_natCast]
  have hupper : (64 : ℚ) * (2 : ℚ) ^ eF * (2 ^ eb : ℕ) =
      (2 : ℚ) ^ ((6 + eF + eb : ℕ) : ℤ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, zpow_natCast, pow_add, pow_add]
    norm_num
  have hlog : Int.log 2 ((2 : ℚ) ^ ((6 + eF + eb : ℕ) : ℤ)) = ((6 + eF + eb : ℕ) : ℤ) := by
    simpa only [Nat.cast_ofNat] using Int.log_zpow (R := ℚ) (by decide : 1 < 2) ((6 + eF + eb : ℕ) : ℤ)
  have hclog : Int.clog 2 ((2 : ℚ) ^ ((eb : ℤ) - eM)) = (eb : ℤ) - eM := by
    simpa only [Nat.cast_ofNat] using Int.clog_zpow (R := ℚ) (by decide : 1 < 2) ((eb : ℤ) - eM)
  rw [groupDyadicScales_length, hlower, hupper, hlog, hclog]
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryDyadicCeiling
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The dyadic envelope is found by a bounded sequence of exact Boolean
comparisons.  The scan starts at `2⁻ᴮ`, doubles at most `2B` times, and uses
the stored fraction width `B`; no real logarithm is evaluated. -/

namespace EditApproximation



theorem powerTwoWord_length (n : ℕ) : (powerTwoWord n).length = n + 1 := by
  simp [powerTwoWord]

namespace BinaryFraction



theorem inversePowerTwo_width (n : ℕ) : (inversePowerTwo n).width = n + 1 := by
  simp [inversePowerTwo, width, powerTwoWord_length]



end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryFiniteLoops
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Executed finite filters and stored fraction reductions used by the
band tests. Callback costs and list construction are included. -/

namespace EditApproximation



theorem filterWithWork_cost {α : Type*} (test : α → Bool × ℕ) (values : List α)
    (C : ℕ) (hC : ∀ a ∈ values, (test a).2 ≤ C) :
    (filterWithWork test values).2 ≤ values.length * (C + 3) := by
  induction values with
  | nil => simp [filterWithWork]
  | cons a rest ih =>
    have ha := hC a List.mem_cons_self
    have ht := ih (fun b hb => hC b (List.mem_cons_of_mem _ hb))
    change (test a).2 + (filterWithWork test rest).2 + 3 ≤ _
    simp only [List.length_cons]
    rw [Nat.add_mul, Nat.one_mul]
    omega

namespace BinaryFraction



theorem leWithWork_cost (a b : BinaryFraction) (B : ℕ) (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (a.leWithWork b).2 ≤ 1000 * (B + 1) ^ 2 + 1 :=
  Nat.add_le_add_right (ltWithWork_cost b a B hb ha) 1




end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteEnumerationWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal finite enumeration with counters. Each callback is evaluated
once and its returned work is charged; list cells and copied output cells
are charged separately. -/

namespace EditApproximation



theorem arithmeticFlatMapWithWork_cost {α β : Type*} (f : α → List β × ℕ) (values : List α)
    (C L : ℕ) (hC : ∀ a ∈ values, (f a).2 ≤ C) (hL : ∀ a ∈ values, (f a).1.length ≤ L) :
    (arithmeticFlatMapWithWork f values).2 ≤ values.length * (C + L + 3) := by
  induction values with
  | nil => simp only [arithmeticFlatMapWithWork, List.length_nil, Nat.zero_mul, le_refl]
  | cons a rest ih =>
    have ha := hC a List.mem_cons_self
    have hla := hL a List.mem_cons_self
    have htail := ih (fun b hb => hC b (List.mem_cons_of_mem a hb))
      (fun b hb => hL b (List.mem_cons_of_mem a hb))
    simp only [arithmeticFlatMapWithWork, List.length_cons]
    nlinarith only [ha, hla, htail]

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



theorem divWithWork_width_uniform (a b : BinaryFraction) (B : ℕ)
    (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (a.divWithWork b).1.width ≤ 4 * B + 4 := by
  have hs := UnreducedRational.storageBits_div a.representation b.representation
  have ha' := representation_storageBits_le a
  have hb' := representation_storageBits_le b
  have hw := divWithWork_self_width a b
  rw [divWithWork_representation] at hw
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryMedianKernel
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalCells
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCellGrid
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The whole-cell grids and nearby cell indices are generated by literal
binary quotient, endpoint and bounded-range operations. -/

namespace EditApproximation
namespace BinaryFraction



theorem naturalFloorWithWork_bounds (a : BinaryFraction) :
    (naturalFloorWithWork a).1.length ≤ a.width ∧
      (naturalFloorWithWork a).2 ≤ 200 * (a.width + 1) ^ 2 := by
  have hn : a.numerator.bits.length ≤ a.width := le_max_left _ _
  have hd : a.denominator.length ≤ a.width := le_max_right _ _
  have hlen := (bitDivModWithWork_lengths a.denominator a.numerator.bits).1
  have hc := bitDivModWithWork_cost a.denominator a.numerator.bits
  unfold naturalFloorWithWork
  split_ifs <;> dsimp only
  · exact ⟨Nat.zero_le _, by nlinarith only [Nat.zero_le a.width]⟩
  · exact ⟨hlen.le.trans hn, by nlinarith only [hc, hn, hd, Nat.zero_le a.width]⟩



end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalGridWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Binary work for the actual bounded endpoint-index loops. The bound is
linear in the emitted one-dimensional grid size and quadratic in bit width. -/

namespace EditApproximation

private theorem wordValue_size_le (bits : List Bool) : Nat.size (bitWordValue bits) ≤ bits.length :=
  Nat.size_le.mpr (bitWordValue_lt_pow_length bits)

theorem binaryNaturalAdd_size_le (a b : ℕ) :
    Nat.size (a + b) ≤ max (Nat.size a) (Nat.size b) + 2 := by
  have hv := wordValue_size_le (binaryNaturalAddWithWork a b).1
  have hl := bitAddWithWork_length a.bits b.bits false
  rw [binaryNaturalAddWithWork_value] at hv
  have hsmall : Nat.size (a + b) ≤ max (Nat.size a) (Nat.size b) + 1 := by
    simpa only [binaryNaturalAddWithWork, Nat.size_eq_bits_len] using hv.trans hl
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCellGridWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word-size bounds for the literal whole-cell index scans. The
cardinalities here are the emitted local ranges, not the target length. -/

namespace EditApproximation
namespace BinaryFraction

private theorem naturalWordSize_le (bits : List Bool) : Nat.size (bitWordValue bits) ≤ bits.length :=
  Nat.size_le.mpr (bitWordValue_lt_pow_length bits)

theorem cellCoordinatesWithWork_bounds (side : BinaryFraction) (p radius B : ℕ)
    (hs : side.width ≤ B) (hp : Nat.size p ≤ B) (hr : Nat.size radius ≤ B) :
    (cellCoordinatesWithWork side p radius).2 ≤
      cellCoordinateSetupBitBudget B + (localCellCoordinates side.value p radius).length ∧
      ∀ x ∈ (cellCoordinatesWithWork side p radius).1, Nat.size x ≤ 4 * B + 23 := by
  let lower := saturatingSubtractWithWork p radius
  let upper := binaryNaturalAddWithWork p radius
  let firstQ := divWithWork (nat (bitWordValue lower.1)) side
  let lastQ := divWithWork (nat (bitWordValue upper.1)) side
  let first := naturalFloorWithWork firstQ.1
  let last := naturalFloorWithWork lastQ.1
  let stop := binaryNaturalAddWithWork (bitWordValue last.1) 1
  let count := saturatingSubtractWithWork (bitWordValue stop.1) (bitWordValue first.1)
  have hl : Nat.size (bitWordValue lower.1) ≤ B := by
    rw [saturatingSubtractWithWork_value]
    exact (Nat.size_le_size (Nat.sub_le _ _)).trans hp
  have hu : Nat.size (bitWordValue upper.1) ≤ B + 2 := by
    rw [binaryNaturalAddWithWork_value]
    exact (binaryNaturalAdd_size_le p radius).trans (by omega)
  have hfl := divWithWork_width_uniform (nat (bitWordValue lower.1)) side (B + 4)
    ((nat_width_le _).trans (by omega)) (by omega)
  have hll := divWithWork_width_uniform (nat (bitWordValue upper.1)) side (B + 4)
    ((nat_width_le _).trans (by omega)) (by omega)
  have hfc := divWithWork_cost (nat (bitWordValue lower.1)) side (B + 4)
    ((nat_width_le _).trans (by omega)) (by omega)
  have hlc := divWithWork_cost (nat (bitWordValue upper.1)) side (B + 4)
    ((nat_width_le _).trans (by omega)) (by omega)
  change firstQ.1.width ≤ _ at hfl
  change lastQ.1.width ≤ _ at hll
  change firstQ.2 ≤ _ at hfc
  change lastQ.2 ≤ _ at hlc
  simp only [Nat.add_assoc, Nat.reduceAdd] at hfc hlc
  have hf := naturalFloorWithWork_bounds firstQ.1
  have hl' := naturalFloorWithWork_bounds lastQ.1
  have hfirst : Nat.size (bitWordValue first.1) ≤ 4 * B + 20 :=
    ((naturalWordSize_le _).trans hf.1).trans (by omega)
  have hlast : Nat.size (bitWordValue last.1) ≤ 4 * B + 20 :=
    ((naturalWordSize_le _).trans hl'.1).trans (by omega)
  have hstop : Nat.size (bitWordValue stop.1) ≤ 4 * B + 23 := by
    rw [binaryNaturalAddWithWork_value]
    exact (binaryNaturalAdd_size_le _ 1).trans (by simp only [Nat.size_one]; omega)
  have hfloorFirst : first.2 ≤ 200 * (4 * B + 21) ^ 2 :=
    hf.2.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have hfloorLast : last.2 ≤ 200 * (4 * B + 21) ^ 2 :=
    hl'.2.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have hlowCost := saturatingSubtractWithWork_cost p radius
  have huppCost := binaryNaturalAddWithWork_cost p radius
  have hstopCost := binaryNaturalAddWithWork_cost (bitWordValue last.1) 1
  have hcountCost := saturatingSubtractWithWork_cost (bitWordValue stop.1) (bitWordValue first.1)
  change lower.2 ≤ _ at hlowCost
  change upper.2 ≤ _ at huppCost
  change stop.2 ≤ _ at hstopCost
  change count.2 ≤ _ at hcountCost
  simp only [Nat.size_one] at hstopCost
  have hlength : (List.range' (bitWordValue first.1) (bitWordValue count.1)).length =
      (localCellCoordinates side.value p radius).length := by
    have hv := congrArg List.length (cellCoordinatesWithWork_value side p radius)
    simpa only [cellCoordinatesWithWork, lower, upper, firstQ, lastQ, first, last,
      stop, count] using hv
  constructor
  · change lower.2 + upper.2 + firstQ.2 + lastQ.2 + first.2 + last.2 + stop.2 + count.2 +
      (List.range' (bitWordValue first.1) (bitWordValue count.1)).length + Nat.size p + Nat.size radius + 9 ≤ _
    rw [hlength]
    unfold cellCoordinateSetupBitBudget
    omega
  · intro x hx
    have hx' : x ∈ List.range' (bitWordValue first.1) (bitWordValue count.1) := by
      simpa only [cellCoordinatesWithWork, lower, upper, firstQ, lastQ, first, last,
        stop, count] using hx
    obtain ⟨j, hj, hxj⟩ := List.mem_range'.mp hx'
    have hcount : bitWordValue count.1 = bitWordValue stop.1 - bitWordValue first.1 :=
      saturatingSubtractWithWork_value _ _
    have hxstop : x ≤ bitWordValue stop.1 := by omega
    exact (Nat.size_le_size hxstop).trans hstop

theorem cellCoordinatesWithWork_cost (side : BinaryFraction) (p radius B : ℕ)
    (hs : side.width ≤ B) (hp : Nat.size p ≤ B) (hr : Nat.size radius ≤ B) :
    (cellCoordinatesWithWork side p radius).2 ≤
      cellCoordinateSetupBitBudget B + (localCellCoordinates side.value p radius).length :=
  (cellCoordinatesWithWork_bounds side p radius B hs hp hr).1

theorem targetCellsWithWork_cost {n : ℕ} (side : BinaryFraction) (radius B : ℕ)
    (query : TargetInterval n) (hs : side.width ≤ B) (hn : Nat.size n ≤ B)
    (hr : Nat.size radius ≤ B) :
    (targetCellsWithWork side radius query).2 ≤ targetCellsBitBudget
      (localCellCoordinates side.value query.lo radius).length
      (localCellCoordinates side.value query.hi radius).length B := by
  let left := cellCoordinatesWithWork side query.lo radius
  let right := cellCoordinatesWithWork side query.hi radius
  have hl := cellCoordinatesWithWork_cost side query.lo radius B hs
    ((Nat.size_le_size (query.ordered.trans query.valid)).trans hn) hr
  have hh := cellCoordinatesWithWork_cost side query.hi radius B hs
    ((Nat.size_le_size query.valid).trans hn) hr
  have hm (lo : ℕ) : (arithmeticMapWithWork (fun hi => ((lo, hi), 1)) right.1).2 ≤
      right.1.length * 4 := arithmeticMapWithWork_cost _ _ 1 (fun _ _ => le_rfl)
  have hf := arithmeticFlatMapWithWork_cost
    (fun lo => arithmeticMapWithWork (fun hi => ((lo, hi), 1)) right.1) left.1
    (right.1.length * 4) right.1.length (fun lo _ => hm lo)
    (fun _ _ => by simp only [arithmeticMapWithWork_value, List.length_map]; exact le_rfl)
  change left.2 ≤ _ at hl
  change right.2 ≤ _ at hh
  change left.2 + right.2 + (arithmeticFlatMapWithWork
    (fun lo => arithmeticMapWithWork (fun hi => ((lo, hi), 1)) right.1) left.1).2 + 2 ≤ _
  have hleft : left.1.length = (localCellCoordinates side.value query.lo radius).length :=
    congrArg List.length (cellCoordinatesWithWork_value side query.lo radius)
  have hright : right.1.length = (localCellCoordinates side.value query.hi radius).length :=
    congrArg List.length (cellCoordinatesWithWork_value side query.hi radius)
  have hflat : (arithmeticFlatMapWithWork
      (fun lo => arithmeticMapWithWork (fun hi => ((lo, hi), 1)) right.1) left.1).2 ≤
      (localCellCoordinates side.value query.lo radius).length *
        (5 * (localCellCoordinates side.value query.hi radius).length + 3) := by
    calc
      _ ≤ left.1.length * (right.1.length * 4 + right.1.length + 3) := hf
      _ = _ := by rw [hleft, hright]; ring
  unfold targetCellsBitBudget
  omega


theorem targetCellsWithWork_keys {n : ℕ} (side : BinaryFraction) (radius B : ℕ)
    (query : TargetInterval n) (hs : side.width ≤ B) (hn : Nat.size n ≤ B)
    (hr : Nat.size radius ≤ B) (cell : ℕ × ℕ)
    (hcell : cell ∈ (targetCellsWithWork side radius query).1) :
    Nat.size cell.1 ≤ 4 * B + 23 ∧ Nat.size cell.2 ≤ 4 * B + 23 := by
  have hl := (cellCoordinatesWithWork_bounds side query.lo radius B hs
    ((Nat.size_le_size (query.ordered.trans query.valid)).trans hn) hr).2
  have hh := (cellCoordinatesWithWork_bounds side query.hi radius B hs
    ((Nat.size_le_size query.valid).trans hn) hr).2
  simp only [targetCellsWithWork, arithmeticFlatMapWithWork_value,
    arithmeticMapWithWork_value] at hcell
  obtain ⟨lo, hlo, hc⟩ := List.mem_flatMap.mp hcell
  obtain ⟨hi, hhi, rfl⟩ := List.mem_map.mp hc
  exact ⟨hl lo hlo, hh hi hhi⟩

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupSetup
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The literal scale list and sample counts, including scales below one.
Dyadic input exponents are carried by the computed parameter construction;
no real logarithm is evaluated by these routines. -/

namespace EditApproximation
namespace BinaryFraction



theorem signedPowerTwoWithWork_width (e : ℤ) :
    (signedPowerTwoWithWork e).1.width ≤ e.natAbs + 1 := by
  unfold signedPowerTwoWithWork
  split_ifs with h
  · simp only [width, powerTwoWord_length, List.length_cons, List.length_nil]
    have hs := Int.toNat_add_toNat_neg_eq_natAbs e
    have he : e.toNat ≤ e.natAbs := by omega
    omega
  · rw [inversePowerTwo_width]
    have hs := Int.toNat_add_toNat_neg_eq_natAbs e
    have he : (-e).toNat ≤ e.natAbs := by omega
    omega



theorem groupScalesWithWork_length (eM eb eF : ℕ) :
    (groupScalesWithWork eM eb eF).1.length = 7 + eM + eF := by
  have h := congrArg List.length (groupScalesWithWork_value eM eb eF)
  simpa only [List.length_map, groupDyadicScales_length_dyadic] using h

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupSetupWork
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit bit costs of the dyadic-scale and exact sample-count builders.
The generated count determines the finite draw type. -/

namespace EditApproximation
namespace BinaryFraction

theorem signedPowerTwoWithWork_cost (e : ℤ) :
    (signedPowerTwoWithWork e).2 ≤ e.natAbs + 3 := by
  have h := Int.toNat_add_toNat_neg_eq_natAbs e
  unfold signedPowerTwoWithWork
  split_ifs <;> dsimp only <;> omega

theorem groupScalesWithWork_bounds (eM eb eF : ℕ) :
    (∀ value ∈ (groupScalesWithWork eM eb eF).1,
      value.width ≤ eM + eb + eF + 7) ∧
    (groupScalesWithWork eM eb eF).2 ≤ groupScalesBitBudget eM eb eF := by
  let exponents := integerClosedRange ((eb : ℤ) - eM) ((6 + eF + eb : ℕ) : ℤ)
  have habs (e : ℤ) (he : e ∈ exponents) : e.natAbs ≤ eM + eb + eF + 6 := by
    have h := (integerClosedRange_mem _ _ _).mp he
    have hp : e ≤ (eM + eb + eF + 6 : ℕ) := by omega
    have ha : |e| ≤ (eM + eb + eF + 6 : ℕ) := abs_le.mpr ⟨by omega, hp⟩
    have hn : (e.natAbs : ℤ) ≤ (eM + eb + eF + 6 : ℕ) := by
      simpa only [Int.natCast_natAbs] using ha
    exact_mod_cast hn
  have hlen : exponents.length = 7 + eM + eF := by
    simp only [exponents, integerClosedRange, List.length_map, List.length_range]
    omega
  constructor
  · intro value hvalue
    simp only [groupScalesWithWork, arithmeticMapWithWork_value] at hvalue
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hvalue
    exact (signedPowerTwoWithWork_width e).trans (Nat.add_le_add_right (habs e he) 1)
  · have hmap := arithmeticMapWithWork_cost signedPowerTwoWithWork exponents
      (eM + eb + eF + 9) (fun e he => (signedPowerTwoWithWork_cost e).trans (by
        have h := habs e he
        omega))
    rw [hlen] at hmap
    change (arithmeticMapWithWork signedPowerTwoWithWork exponents).2 + exponents.length +
      Nat.size eM + Nat.size eb + Nat.size eF + 8 ≤ _
    unfold groupScalesBitBudget
    rw [hlen]
    nlinarith only [hmap]

theorem groupSampleCountWithWork_bounds (M Q b : ℕ) (h : BinaryFraction) (B : ℕ)
    (hM : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B)
    (hb : Nat.size b + 2 ≤ B) (hh : h.width ≤ B) :
    (groupSampleCountWithWork M Q b h).1.length ≤ groupSampleCountWordBudget B ∧
      (groupSampleCountWithWork M Q b h).2 ≤ groupSampleCountBitBudget B := by
  have hMw := (nat_width_le M).trans hM
  have hQw := (nat_width_le Q).trans hQ
  have hbw := (nat_width_le b).trans hb
  have hqm := canonicalMulWithWork_width (nat Q) (nat M) B hQw hMw
  have hqmc := canonicalMulWithWork_cost (nat Q) (nat M) B hQw hMw
  have hn := canonicalMulWithWork_width (canonicalMulWithWork (nat Q) (nat M)).1 h
    (4 * B + 2) hqm (by omega)
  have hnc := canonicalMulWithWork_cost (canonicalMulWithWork (nat Q) (nat M)).1 h
    (4 * B + 2) hqm (by omega)
  have hn' : (canonicalMulWithWork (canonicalMulWithWork (nat Q) (nat M)).1 h).1.width ≤
      16 * B + 10 := by omega
  have hr := divWithWork_width_uniform
    (canonicalMulWithWork (canonicalMulWithWork (nat Q) (nat M)).1 h).1 (nat b)
    (16 * B + 10) hn' (by omega)
  have hrc := divWithWork_cost
    (canonicalMulWithWork (canonicalMulWithWork (nat Q) (nat M)).1 h).1 (nat b)
    (16 * B + 10) hn' (by omega)
  let ratio := divWithWork (canonicalMulWithWork (canonicalMulWithWork (nat Q) (nat M)).1 h).1 (nat b)
  change ratio.1.width ≤ _ at hr
  change ratio.2 ≤ _ at hrc
  have hceil := naturalCeilingWithWork_length ratio.1
  have hceilc := naturalCeilingWithWork_cost ratio.1
  have hsquare := Nat.pow_le_pow_left (show ratio.1.width + 1 ≤ 64 * B + 45 by omega) 2
  have hmin := wordMinWithWork_length M.bits (naturalCeilingWithWork ratio.1).1
  have hminc := wordLEWithWork_cost M.bits (naturalCeilingWithWork ratio.1).1
  simp only [Nat.size_eq_bits_len] at hmin hminc
  constructor
  · change (wordMinWithWork M.bits (naturalCeilingWithWork ratio.1).1).1.length ≤ _
    unfold groupSampleCountWordBudget
    omega
  · change _ + _ + ratio.2 + (naturalCeilingWithWork ratio.1).2 +
      (wordMinWithWork M.bits (naturalCeilingWithWork ratio.1).1).2 +
        Nat.size M + Nat.size Q + Nat.size b + 5 ≤ _
    have hword : (wordMinWithWork M.bits (naturalCeilingWithWork ratio.1).1).2 =
        (wordLEWithWork M.bits (naturalCeilingWithWork ratio.1).1).2 + 1 := rfl
    rw [hword]
    simp only [Nat.add_assoc, Nat.reduceAdd] at hnc hrc
    unfold groupSampleCountBitBudget
    nlinarith only [hqmc, hnc, hrc, hceilc, hsquare, hminc, hceil, hM, hQ, hb, hr]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalGuardWork
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every local eligibility test is charged at the bit level, including
its rational divisions and the construction of its two thresholds. -/

namespace EditApproximation
namespace BinaryFraction

theorem refinementScaleGuardWithWork_cost (F b B : ℕ) (a w : BinaryFraction)
    (hB : 7 ≤ B) (hb : Nat.size b + 2 ≤ B) (hF : Nat.size F + 2 ≤ B)
    (ha : a.width ≤ B) (hw : w.width ≤ B) :
    (refinementScaleGuardWithWork F b a w).2 ≤ localEligibilityBitBudget B := by
  have hsixteen : (nat 16).width ≤ B := (nat_width_le 16).trans (by
    have h : Nat.size 16 = 5 := by decide
    omega)
  have height : (nat 8).width ≤ B := (nat_width_le 8).trans (by
    have h : Nat.size 8 = 4 := by decide
    omega)
  have hbn := (nat_width_le b).trans hb
  have hFn := (nat_width_le F).trans hF
  have hdw := canonicalMulWithWork_width (nat 16) (nat F) B hsixteen hFn
  have hdc := canonicalMulWithWork_cost (nat 16) (nat F) B hsixteen hFn
  have hlw := divWithWork_width_uniform w (canonicalMulWithWork (nat 16) (nat F)).1
    (4 * B + 2) (by omega) hdw
  have hlc := divWithWork_cost w (canonicalMulWithWork (nat 16) (nat F)).1
    (4 * B + 2) (by omega) hdw
  have hfw := canonicalMulWithWork_width (nat 8) a B height ha
  have hfc := canonicalMulWithWork_cost (nat 8) a B height ha
  have huw := canonicalMulWithWork_width (canonicalMulWithWork (nat 8) a).1 w
    (4 * B + 2) hfw (by omega)
  have huc := canonicalMulWithWork_cost (canonicalMulWithWork (nat 8) a).1 w
    (4 * B + 2) hfw (by omega)
  have hlow := leWithWork_cost (divWithWork w (canonicalMulWithWork (nat 16) (nat F)).1).1
    (nat b) (16 * B + 12) (by omega) (by omega)
  have hhigh := leWithWork_cost (nat b)
    (canonicalMulWithWork (canonicalMulWithWork (nat 8) a).1 w).1
    (16 * B + 12) (by omega) (by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hlc huc hlow hhigh
  change _ + _ + _ + _ + _ + _ + Nat.size b + Nat.size F + 8 ≤ _
  unfold localEligibilityBitBudget
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalRepresentativeWork
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete bit work of the query-local scale and center loops. The
one-dimensional grid size follows from the tested scale inequality. -/

namespace EditApproximation
namespace BinaryFraction

theorem queryExponentsWithWork_bounds (N F B : ℕ) (a w : BinaryFraction)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (ha : a.width ≤ B) (hw : w.width ≤ B) :
    (queryExponentsWithWork N F a w).2 ≤ queryExponentsBitBudget B ∧
      (queryExponentsWithWork N F a w).1.length ≤ B + 1 := by
  let count := max 1 N.bits.length
  have hc : count ≤ B + 1 := by
    dsimp only [count]
    rw [Nat.size_eq_bits_len]
    omega
  have hcost := filterWithWork_cost (fun e =>
    let guard := refinementScaleGuardWithWork F (2 ^ e) a w
    (guard.1, guard.2 + e + 2)) (List.range count)
    (localEligibilityBitBudget (B + 4) + B + 2) (by
      intro e he
      have he' := List.mem_range.mp he
      have hpow : Nat.size (2 ^ e) + 2 ≤ B + 4 := by
        rw [Nat.size_pow]
        omega
      have h := refinementScaleGuardWithWork_cost F (2 ^ e) (B + 4) a w
        (by omega) hpow (by omega) (by omega) (by omega)
      change (refinementScaleGuardWithWork F (2 ^ e) a w).2 + e + 2 ≤ _
      omega)
  simp only [List.length_range] at hcost
  have hlen : (filterWithWork (fun e =>
      let guard := refinementScaleGuardWithWork F (2 ^ e) a w
      (guard.1, guard.2 + e + 2)) (List.range count)).1.length ≤ count := by
    rw [filterWithWork_value]
    exact (List.length_filter_le _ _).trans_eq (List.length_range)
  constructor
  · have hcost' := hcost.trans (Nat.mul_le_mul_right _ hc)
    change (filterWithWork (fun e => ((refinementScaleGuardWithWork F (2 ^ e) a w).1,
      (refinementScaleGuardWithWork F (2 ^ e) a w).2 + e + 2)) (List.range count)).2 +
      count + N.bits.length + 2 ≤ _
    simp only [Nat.add_assoc, Nat.reduceAdd] at hcost'
    unfold queryExponentsBitBudget
    rw [Nat.size_eq_bits_len]
    simp only [Nat.add_assoc] at hcost' ⊢
    omega
  · exact hlen.trans hc

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryHistoryBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cost of generating the earlier-history input list from child grids.
The bound counts the actual nested lists before duplicate removal. -/

namespace EditApproximation

theorem arithmeticFlatMapWithWork_length {α β : Type*} (f : α → List β × ℕ)
    (xs : List α) (L : ℕ) (hL : ∀ x ∈ xs, (f x).1.length ≤ L) :
    (arithmeticFlatMapWithWork f xs).1.length ≤ xs.length * L := by
  induction xs with
  | nil => simp only [arithmeticFlatMapWithWork, List.length_nil, Nat.zero_mul, le_rfl]
  | cons x xs ih =>
    have hx := hL x List.mem_cons_self
    have ht := ih (fun y hy => hL y (List.mem_cons_of_mem _ hy))
    simp only [arithmeticFlatMapWithWork, List.length_append, List.length_cons,
      Nat.add_mul, Nat.one_mul]
    omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryCellCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bounds for the actual cell scan at an accepted query scale.
The scale-window test controls its count; the binary arithmetic controls
its coordinate widths independently of the numeric target length. -/

namespace EditApproximation.BinaryFraction

theorem queryCellCoordinates_count (F b exponent p : ℕ) (w : ℚ)
    (hF : 1 ≤ F) (hb : 1 ≤ b) (hw : 0 ≤ w) (hwindow : w / (16 * F) ≤ b) :
    (localCellCoordinates ((2 : ℚ) ^ (-(exponent : ℤ)) * b) p ⌈w⌉₊).length ≤
      (32 * F + 2) * 2 ^ exponent + 2 := by
  have hbR : (1 : ℚ) ≤ b := by exact_mod_cast hb
  have hs : 0 < (2 : ℚ) ^ (-(exponent : ℤ)) * b := by
    have hbp : (0 : ℚ) < b := by exact_mod_cast (show 0 < b by omega)
    positivity
  apply localCellCoordinates_length_le _ hs _ _ ((32 * F + 2) * 2 ^ exponent)
  apply (div_le_iff₀ hs).2
  have hw' : w ≤ 16 * (F : ℚ) * b := by
    have hf : (0 : ℚ) < F := by exact_mod_cast (show 0 < F by omega)
    nlinarith only [(div_le_iff₀ (by positivity : (0 : ℚ) < 16 * F)).mp hwindow]
  have hc : (⌈w⌉₊ : ℚ) < w + 1 := Nat.ceil_lt_add_one hw
  have heq : (((32 * F + 2) * 2 ^ exponent : ℕ) : ℚ) *
      ((2 : ℚ) ^ (-(exponent : ℤ)) * b) = (32 * (F : ℚ) + 2) * b := by
    push_cast
    rw [zpow_neg, zpow_natCast]
    field_simp
  rw [heq]
  nlinarith only [hc, hw', hbR]

theorem queryScalesWithWork_window (N F : ℕ) (a value : BinaryFraction) (b : ℕ)
    (hb : b ∈ (queryScalesWithWork N F a value).1) :
    (∃ e : ℕ, b = 2 ^ e) ∧ value.value / (16 * F) ≤ b := by
  rw [queryScalesWithWork_value] at hb
  obtain ⟨hd, hg⟩ := List.mem_filter.mp hb
  refine ⟨?_, (of_decide_eq_true hg).1⟩
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hd
  exact ⟨e, rfl⟩

theorem queryCellScan_bounds {n : ℕ} (F b exponent B : ℕ)
    (value : BinaryFraction) (q : TargetInterval n)
    (hF : 1 ≤ F) (hb : 1 ≤ b) (hbs : Nat.size b ≤ B + 1)
    (he : exponent + 1 ≤ B) (hn : Nat.size n ≤ B) (hv : value.width ≤ B)
    (hw : 0 ≤ value.value) (hwindow : value.value / (16 * F) ≤ b) :
    let side := canonicalMulWithWork (inversePowerTwo exponent) (nat b)
    let radius := naturalCeilingWithWork value
    let cells := targetCellsWithWork side.1 (bitWordValue radius.1) q
    cells.1.length ≤ ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 ∧
    side.2 + cells.2 ≤ queryCellScanBitBudget F exponent B ∧
    ∀ cell ∈ cells.1, Nat.size cell.1 ≤ 16 * B + 183 ∧ Nat.size cell.2 ≤ 16 * B + 183 := by
  let side := canonicalMulWithWork (inversePowerTwo exponent) (nat b)
  let radius := naturalCeilingWithWork value
  let cells := targetCellsWithWork side.1 (bitWordValue radius.1) q
  let K := (32 * F + 2) * 2 ^ exponent + 2
  have htheta : (inversePowerTwo exponent).width ≤ B := by rw [inversePowerTwo_width]; exact he
  have hbn : (nat b).width ≤ B + 3 := (nat_width_le b).trans (by omega)
  have hsw := canonicalMulWithWork_width (inversePowerTwo exponent) (nat b) (B + 3) (by omega) hbn
  have hsc := canonicalMulWithWork_cost (inversePowerTwo exponent) (nat b) (B + 3) (by omega) hbn
  have hrw : Nat.size (bitWordValue radius.1) ≤ B + 2 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length radius.1)).trans
      ((naturalCeilingWithWork_length value).trans (by omega))
  have hcoords (p : ℕ) : (localCellCoordinates side.1.value p (bitWordValue radius.1)).length ≤ K := by
    simp only [side, canonicalMulWithWork_value, inversePowerTwo_value, nat_value,
      radius, naturalCeilingWithWork_value]
    exact queryCellCoordinates_count F b exponent p value.value hF hb hw hwindow
  have hcc := targetCellsWithWork_cost side.1 (bitWordValue radius.1) (4 * B + 40)
    q (by change side.1.width ≤ _ at hsw; omega) (by omega) (by omega)
  have hcells : cells.2 ≤ targetCellsBitBudget K K (4 * B + 40) := hcc.trans (by
    unfold targetCellsBitBudget
    gcongr <;> apply hcoords)
  refine ⟨?_, ?_, ?_⟩
  · rw [targetCellsWithWork_value]
    simp only [canonicalMulWithWork_value, inversePowerTwo_value, nat_value,
      naturalCeilingWithWork_value]
    exact localTargetCells_query_length F b exponent q value.value hF hb hw hwindow
  · change side.2 + cells.2 ≤ _
    change side.2 ≤ _ at hsc
    exact Nat.add_le_add hsc hcells
  · intro cell hc
    have hk := targetCellsWithWork_keys side.1 (bitWordValue radius.1) (4 * B + 40) q
      (by change side.1.width ≤ _ at hsw; omega) (by omega) (by omega) cell hc
    constructor <;> omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryGroupSampleCost
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source-key builder executes all scale/sample loops. Their cost
is bounded using the computed count, which is capped by the arity. -/

namespace EditApproximation.BinaryFraction

theorem queryGroupKeySamplesWithWork_bounds (M F Q eM eb eF B : ℕ)
    (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF) (cell : ℕ × ℕ)
    (hM : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B)
    (heb : eb + 3 ≤ B) (hsb : eM + eb + eF + 7 ≤ B) :
    (queryGroupKeySamplesWithWork M F Q eM eb eF hMdef hFdef cell).1.length ≤
      (7 + eM + eF) * M ∧
    (queryGroupKeySamplesWithWork M F Q eM eb eF hMdef hFdef cell).2 ≤
      queryGroupSamplesBitBudget M eM eb eF B := by
  let b := 2 ^ eb
  let scales := groupScalesWithWork eM eb eF
  have hs : scales.1.map value = groupDyadicScales M b F := by
    simpa only [nat_value] using computedGroupScales_value M b F eM eb eF hMdef rfl hFdef
  have hlen : scales.1.length = (groupDyadicScales M b F).length := by
    simpa only [List.length_map] using congrArg List.length hs
  let indices := queryFinRange scales.1.length (groupDyadicScales M b F).length hlen
  let run := fun scale : Fin (groupDyadicScales M b F).length =>
    let word := queryScaleAt scales.1 (groupDyadicScales M b F) hs scale
    let count := groupSampleCountWithWork M Q b word
    let hc : bitWordValue count.1 = groupSampleCount M Q b (groupDyadicScaleAt M b F scale) := by
      rw [groupSampleCountWithWork_value, queryScaleAt_value]
      rfl
    let coordinates := queryFinRange (bitWordValue count.1)
      (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) hc
    let labeled := arithmeticMapWithWork (fun sample =>
      ((⟨(b, cell), scale, sample⟩ : GroupScalarKey M F Q), 2)) coordinates
    (labeled.1, scales.1.length + count.2 + labeled.2 + coordinates.length + 3)
  have hslen : scales.1.length = 7 + eM + eF := groupScalesWithWork_length eM eb eF
  have hilen : indices.length = 7 + eM + eF := by
    dsimp only [indices]
    rw [queryFinRange_value, List.length_finRange, ← hlen, hslen]
  have hsbounds := groupScalesWithWork_bounds eM eb eF
  have hword (scale : Fin (groupDyadicScales M b F).length) :
      (queryScaleAt scales.1 (groupDyadicScales M b F) hs scale).width ≤ B := by
    apply (hsbounds.1 _ ?_).trans hsb
    exact List.getElem_mem _
  have hcount (scale : Fin (groupDyadicScales M b F).length) :=
    (groupSampleCountWithWork_bounds M Q b
      (queryScaleAt scales.1 (groupDyadicScales M b F) hs scale) B hM hQ
      (by dsimp only [b]; rw [Nat.size_pow]; omega) (hword scale)).2
  have hrlen (scale : Fin (groupDyadicScales M b F).length) : (run scale).1.length ≤ M := by
    simp only [run, arithmeticMapWithWork_value, List.length_map, queryFinRange_value,
      List.length_finRange]
    exact Nat.min_le_left _ _
  have hrcost (scale : Fin (groupDyadicScales M b F).length) :
      (run scale).2 ≤ (7 + eM + eF) + groupSampleCountBitBudget B + 6 * M + 3 := by
    have hlabel := arithmeticMapWithWork_cost
      (fun sample : Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) =>
        ((⟨(b, cell), scale, sample⟩ : GroupScalarKey M F Q), 2))
      (List.finRange _) 2 (fun _ _ => le_rfl)
    simp only [List.length_finRange, Nat.reduceAdd] at hlabel
    have hlen' : groupSampleCount M Q b (groupDyadicScaleAt M b F scale) ≤ M := Nat.min_le_left _ _
    have hlabel' := hlabel.trans (Nat.mul_le_mul_right 5 hlen')
    dsimp only [run]
    simp only [queryFinRange_value, List.length_finRange, hslen]
    have hh := hcount scale
    nlinarith only [hlabel', hh, hlen']
  have hl := arithmeticFlatMapWithWork_length run indices M (fun scale _ => hrlen scale)
  have hc := arithmeticFlatMapWithWork_cost run indices
    ((7 + eM + eF) + groupSampleCountBitBudget B + 6 * M + 3) M
    (fun scale _ => hrcost scale) (fun scale _ => hrlen scale)
  rw [hilen] at hl hc
  constructor
  · exact hl
  · change scales.2 + 4 * scales.1.length + (arithmeticFlatMapWithWork run indices).2 + eb + 4 ≤ _
    rw [hslen]
    have hswork : scales.2 ≤ groupScalesBitBudget eM eb eF := hsbounds.2
    change _ ≤ groupScalesBitBudget eM eb eF + 4 * (7 + eM + eF) +
      (7 + eM + eF) * ((7 + eM + eF) + groupSampleCountBitBudget B + 7 * M + 6) + eb + 4
    rw [show 7 + eM + eF + groupSampleCountBitBudget B + 6 * M + 3 + M + 3 =
      (7 + eM + eF) + groupSampleCountBitBudget B + 7 * M + 6 by omega] at hc
    omega

theorem queryGroupSamplesBitBudget_mono (M eM eb eb' eF B B' : ℕ)
    (he : eb ≤ eb') (hB : B ≤ B') :
    queryGroupSamplesBitBudget M eM eb eF B ≤ queryGroupSamplesBitBudget M eM eb' eF B' := by
  unfold queryGroupSamplesBitBudget groupScalesBitBudget groupSampleCountBitBudget
  dsimp only
  gcongr
  exact Nat.size_le_size he

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryGroupSourceCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

theorem queryExponentsWithWork_member (N F B : ℕ) (a value : BinaryFraction)
    (hN : Nat.size N ≤ B) (eb : ℕ) (heb : eb ∈ (queryExponentsWithWork N F a value).1) :
    eb ≤ B ∧ 2 ^ eb ∈ (queryScalesWithWork N F a value).1 := by
  constructor
  · simp only [queryExponentsWithWork, filterWithWork_value] at heb
    have h := List.mem_range.mp (List.mem_filter.mp heb).1
    rw [Nat.size_eq_bits_len] at h
    omega
  · rw [queryScalesWithWork_value, ← queryExponentsWithWork_value]
    exact List.mem_map.mpr ⟨eb, heb, rfl⟩

theorem queryGroupSourceKeysWithWork_bounds_oai {n : ℕ} (M N F Q exponent eM eF B : ℕ)
    (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF) (a value : BinaryFraction) (q : TargetInterval n)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hM : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B) (hes : eM + eF + 7 ≤ B)
    (he : exponent + 1 ≤ B) (hn : Nat.size n ≤ B) (ha : a.width ≤ B)
    (hv : value.width ≤ B) (hw : 0 ≤ value.value) :
    (queryGroupSourceKeysWithWork M N F Q exponent eM eF hMdef hFdef a value q).1.length ≤
      queryGroupSourceKeysLength M F exponent eM eF B ∧
    (queryGroupSourceKeysWithWork M N F Q exponent eM eF hMdef hFdef a value q).2 ≤
      queryGroupSourceKeysBitBudget M F exponent eM eF B := by
  let scales := queryExponentsWithWork N F a value
  let radius := naturalCeilingWithWork value
  let cells := fun eb => targetCellsWithWork
    (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1 (bitWordValue radius.1) q
  let sources := fun eb => arithmeticFlatMapWithWork
    (queryGroupKeySamplesWithWork M F Q eM eb eF hMdef hFdef) (cells eb).1
  let run := fun eb =>
    let side := canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))
    ((sources eb).1, side.2 + (cells eb).2 + (sources eb).2 + eb + exponent + 4)
  let K := ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  let L := (7 + eM + eF) * M
  let W := queryGroupSamplesBitBudget M eM B eF (2 * B + 10)
  let C := queryCellScanBitBudget F exponent B + K * (W + L + 3) + B + exponent + 4
  have hs := queryExponentsWithWork_bounds N F B a value hB hN hF ha hv
  have hFpos : 1 ≤ F := by rw [hFdef]; exact Nat.succ_le_of_lt (Nat.two_pow_pos _)
  have hrun (eb : ℕ) (heb : eb ∈ scales.1) : (run eb).1.length ≤ K * L ∧ (run eb).2 ≤ C := by
    have hm := queryExponentsWithWork_member N F B a value hN eb heb
    have hwindow := queryScalesWithWork_window N F a value (2 ^ eb) hm.2
    have hcell := queryCellScan_bounds F (2 ^ eb) exponent B value q hFpos
      (Nat.succ_le_of_lt (Nat.two_pow_pos _))
      (by rw [Nat.size_pow]; omega) he hn hv hw hwindow.2
    have hsample (cell : ℕ × ℕ) :
        (queryGroupKeySamplesWithWork M F Q eM eb eF hMdef hFdef cell).1.length ≤ L ∧
        (queryGroupKeySamplesWithWork M F Q eM eb eF hMdef hFdef cell).2 ≤ W := by
      have hh := queryGroupKeySamplesWithWork_bounds M F Q eM eb eF (2 * B + 10)
        hMdef hFdef cell (by omega) (by omega) (by omega) (by omega)
      exact ⟨hh.1, hh.2.trans (queryGroupSamplesBitBudget_mono M eM eb B eF
        (2 * B + 10) (2 * B + 10) hm.1 le_rfl)⟩
    have hl := (arithmeticFlatMapWithWork_length
      (queryGroupKeySamplesWithWork M F Q eM eb eF hMdef hFdef) (cells eb).1 L
      (fun cell _ => (hsample cell).1)).trans (Nat.mul_le_mul_right _ hcell.1)
    have hc := (arithmeticFlatMapWithWork_cost
      (queryGroupKeySamplesWithWork M F Q eM eb eF hMdef hFdef) (cells eb).1 W L
      (fun cell _ => (hsample cell).2) (fun cell _ => (hsample cell).1)).trans
        (Nat.mul_le_mul_right _ hcell.1)
    have hsourcec : (sources eb).2 ≤ K * (W + L + 3) := by
      simpa only [sources] using hc
    have hcellc : (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).2 +
      (cells eb).2 ≤ queryCellScanBitBudget F exponent B := by
      simpa only [cells, radius] using hcell.2.1
    have hcost := Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hcellc hsourcec) hm.1) exponent) 4
    simpa only [run, C] using And.intro hl hcost
  have hl := (arithmeticFlatMapWithWork_length run scales.1 (K * L)
    (fun eb heb => (hrun eb heb).1)).trans (Nat.mul_le_mul_right _ hs.2)
  have hc := (arithmeticFlatMapWithWork_cost run scales.1 C (K * L)
    (fun eb heb => (hrun eb heb).2) (fun eb heb => (hrun eb heb).1)).trans
      (Nat.mul_le_mul_right _ hs.2)
  have hr := (naturalCeilingWithWork_cost value).trans
    (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (Nat.add_le_add_right hv 1) 2))
  have hcost := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hs.1 hr) hc) 2
  simpa only [queryGroupSourceKeysWithWork, scales, radius, run, cells, sources,
    queryGroupSourceKeysLength, queryGroupSourceKeysBitBudget, K, L, W, C] using And.intro hl hcost

end EditApproximation.BinaryFraction

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.BinaryFraction.queryGroupSourceKeysWithWork_bounds_oai := @OAI.EditApproximation.BinaryFraction.queryGroupSourceKeysWithWork_bounds_oai
