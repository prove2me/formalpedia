-- Prove2me | solution 1 for OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsWithWork_cost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:28:47.010111+00:00
-- url     : https://prove2.me/submissions/72d7ea30-8f3c-4b7f-a51a-18da92915827

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
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_OAIQ361V3Ea000
import Definitions.Def_OAIQ361V3Ea001
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_preparedUnskippedCandidateWithWork_uniform_cost
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_sampledGroupActionWithWork_cost

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



theorem binaryNaturalMulWithWork_cost (a b : ℕ) :
    (binaryNaturalMulWithWork a b).2 ≤ 20 * (Nat.size a + 1) * (Nat.size a + Nat.size b + 1) := by
  simpa only [binaryNaturalMulWithWork, Nat.size_eq_bits_len] using bitMulWithWork_cost a.bits b.bits

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
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_representation _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.UnreducedRational.value_pow _root_.OAI.EditApproximation.UnreducedRational.value_sub _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
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
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteAssignments
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Executable finite products of child-state lists

The wide-action lists use this literal recursive Cartesian product.
Their coordinates are child labels, so duplicate interval labels remain
distinct coordinates.
-/

namespace EditApproximation



theorem finiteAssignments_length_le {α : Type*} (M K : ℕ)
    (choices : Fin M → List α) (hchoices : ∀ i, (choices i).length ≤ K) :
    (finiteAssignments M choices).length ≤ K ^ M := by
  induction M with
  | zero => simp only [finiteAssignments, List.length_singleton, pow_zero, le_refl]
  | succ M ih =>
    have htail := ih (fun i => choices i.succ) (fun i => hchoices i.succ)
    have hflat (entries : List α) :
        (entries.flatMap fun head =>
          (finiteAssignments M (fun i => choices i.succ)).map
            fun tail => (Fin.cons head tail : Fin (M + 1) → α)).length =
        entries.length * (finiteAssignments M (fun i => choices i.succ)).length := by
      induction entries with
      | nil => simp
      | cons head rest ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, ih]
        ring
    rw [finiteAssignments, hflat, pow_succ]
    nlinarith [hchoices 0]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_WideActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Executable wide action lists

Endpoint indices are generated in the radius-`10b` grid boxes anchored
at the physical source cuts. Lists contain exactly the valid grid states
in those boxes and their Cartesian product over labeled children.
-/

namespace EditApproximation



theorem wideActionList_length_le {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (hP : 0 < P) :
    (wideActionList M parent r b P).length ≤ (40 * P + 2) ^ (2 * M) := by
  have hchoices (i : Fin M) : (wideChildStateList parent r b P i).length ≤ (40 * P + 2) ^ 2 := by
    have hlocal := gridStateBox_length_le ny (seedGridSpacing b P) (10 * b)
      (r.lo + ((sourceChild parent i).lo - parent.lo))
      (r.lo + ((sourceChild parent i).hi - parent.lo))
      (by unfold seedGridSpacing; omega)
    have hcount := seedGridSpacing_radius_count b P hP
    apply hlocal.trans
    apply Nat.pow_le_pow_left
    simpa only [show 2 * (10 * b) = 20 * b by omega] using hcount
  have h := finiteAssignments_length_le M ((40 * P + 2) ^ 2)
    (wideChildStateList parent r b P) hchoices
  simpa only [wideActionList, ← pow_mul] using h

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandGroupSampling
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
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
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source
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



theorem binaryNaturalDivModWithWork_cost (n d : ℕ) :
    (binaryNaturalDivModWithWork n d).2.2 ≤
      30 * (Nat.size n + 1) * (Nat.size n + Nat.size d + 1) := by
  simpa only [binaryNaturalDivModWithWork, Nat.size_eq_bits_len] using bitDivModWithWork_cost d.bits n.bits

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCeilingWork
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

theorem filterMapWithWork_cost {α β : Type*} (f : α → Option β × ℕ) (values : List α)
    (C : ℕ) (hC : ∀ a ∈ values, (f a).2 ≤ C) :
    (filterMapWithWork f values).2 ≤ values.length * (C + 3) := by
  induction values with
  | nil => simp only [filterMapWithWork, List.length_nil, Nat.zero_mul, le_refl]
  | cons a rest ih =>
    have ha := hC a (by simp)
    have ht := ih (fun b hb => hC b (by simp [hb]))
    change (f a).2 + (filterMapWithWork f rest).2 + 3 ≤ _
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GroupCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Whole rational cells are enumerated by bounded ranges of grid indices. -/

namespace EditApproximation



theorem cellGridPoints_length_le {side : ℚ} {g cell P : ℕ}
    (hside : 0 ≤ side) (hsize : side / g ≤ P) :
    (cellGridPoints side g cell).length ≤ P := by
  have hbase : 0 ≤ (cell : ℚ) * side / g :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hside) (Nat.cast_nonneg _)
  have hupper : ((cell : ℚ) + 1) * side / g ≤ (cell : ℚ) * side / g + P := by
    calc
      _ = (cell : ℚ) * side / g + side / g := by ring
      _ ≤ _ := add_le_add_right hsize _
  have hceil := Nat.ceil_le_ceil hupper
  rw [Nat.ceil_add_natCast hbase P] at hceil
  simp only [cellGridPoints, List.length_map, List.length_range']
  omega



theorem cellTargetStates_length_le {n g P : ℕ} {side : ℚ} (cell : ℕ × ℕ)
    (hside : 0 ≤ side) (hsize : side / g ≤ P) :
    (cellTargetStates n g side cell).length ≤ P ^ 2 := by
  have hfirst := cellGridPoints_length_le (cell := cell.1) hside hsize
  have hsecond := cellGridPoints_length_le (cell := cell.2) hside hsize
  have h := list_flatMap_length_le (cellGridPoints side g cell.1)
    (fun lo => (cellGridPoints side g cell.2).filterMap fun hi => makeTargetState n lo hi) P
    (fun lo _ => (List.length_filterMap_le _ _).trans hsecond)
  exact h.trans (by simpa only [pow_two] using Nat.mul_le_mul_right P hfirst)

theorem seedGridSpacing_covers_dyadic {b P : ℕ}
    (hb : ∃ e : ℕ, b = 2 ^ e) (hP : ∃ e : ℕ, P = 2 ^ e) :
    b ≤ P * seedGridSpacing b P := by
  obtain ⟨eb, rfl⟩ := hb
  obtain ⟨eP, rfl⟩ := hP
  by_cases horder : eP ≤ eb
  · rw [seedGridSpacing, Nat.pow_div horder (by decide : 0 < 2), max_eq_right Nat.one_le_two_pow,
      ← pow_add, Nat.add_sub_of_le horder]
  · have hle : 2 ^ eb ≤ 2 ^ eP := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    exact hle.trans (Nat.le_mul_of_pos_right _ (by unfold seedGridSpacing; omega))

theorem cellRepresentativeStates_length_le {n P F b : ℕ}
    (a : ℚ) (initial : TargetInterval n → ℚ) (theta : ℚ) (cell : ℕ × ℕ)
    (htheta : 0 ≤ theta ∧ theta ≤ 1)
    (hb : ∃ e : ℕ, b = 2 ^ e) (hP : ∃ e : ℕ, P = 2 ^ e) :
    (cellRepresentativeStates n P F b a initial theta cell).length ≤ (P + 1) ^ 2 := by
  have hg : 0 < seedGridSpacing b P := by unfold seedGridSpacing; omega
  have hgr : (0 : ℚ) < seedGridSpacing b P := by exact_mod_cast hg
  have hcover : (b : ℚ) ≤ P * (seedGridSpacing b P : ℚ) := by
    exact_mod_cast seedGridSpacing_covers_dyadic hb hP
  have hsize : theta * b / seedGridSpacing b P ≤ (P : ℚ) := by
    apply (div_le_iff₀ hgr).2
    have h := mul_le_mul_of_nonneg_right htheta.2 (Nat.cast_nonneg (α := ℚ) b)
    simp only [one_mul] at h
    exact h.trans hcover
  unfold cellRepresentativeStates
  apply (List.length_filter_le _ _).trans
  exact (cellTargetStates_length_le (n := n) cell
    (mul_nonneg htheta.1 (Nat.cast_nonneg _)) hsize).trans
      (Nat.pow_le_pow_left (Nat.le_succ P) 2)

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCellGrid
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

theorem makeStateWithWork_cost (n lo hi B : ℕ)
    (hn : Nat.size n ≤ B) (hl : Nat.size lo ≤ B) (hh : Nat.size hi ≤ B) :
    (makeStateWithWork n lo hi).2 ≤ 16 * B + 8 := by
  have hfirst := wordLEWithWork_cost lo.bits hi.bits
  have hsecond := wordLEWithWork_cost hi.bits n.bits
  simp only [Nat.size_eq_bits_len] at hfirst hsecond
  unfold makeStateWithWork
  dsimp only
  split_ifs <;> omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCellGridWork
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

theorem cellGridPointsWithWork_bounds (side : BinaryFraction) (g cell B : ℕ)
    (hs : side.width ≤ B) (hg : Nat.size g ≤ B) (hc : Nat.size cell ≤ B) :
    (cellGridPointsWithWork side g cell).2 ≤
      cellGridPointsBitBudget (cellGridPoints side.value g cell).length B ∧
      ∀ x ∈ (cellGridPointsWithWork side g cell).1, Nat.size x ≤ 17 * B + 78 := by
  let next := binaryNaturalAddWithWork cell 1
  let lower := canonicalMulWithWork (nat cell) side
  let upper := canonicalMulWithWork (nat (bitWordValue next.1)) side
  let firstQ := divWithWork lower.1 (nat g)
  let lastQ := divWithWork upper.1 (nat g)
  let first := naturalCeilingWithWork firstQ.1
  let last := naturalCeilingWithWork lastQ.1
  let count := saturatingSubtractWithWork (bitWordValue last.1) (bitWordValue first.1)
  let indices := List.range' (bitWordValue first.1) (bitWordValue count.1)
  have hnext : Nat.size (bitWordValue next.1) ≤ B + 2 := by
    rw [binaryNaturalAddWithWork_value]
    have hv := naturalWordSize_le (binaryNaturalAddWithWork cell 1).1
    rw [binaryNaturalAddWithWork_value] at hv
    have hl := bitAddWithWork_length cell.bits (1 : ℕ).bits false
    have h : Nat.size (cell + 1) ≤ max (Nat.size cell) 1 + 1 := by
      simpa only [binaryNaturalAddWithWork, Nat.size_eq_bits_len, Nat.size_one] using hv.trans hl
    omega
  have hlow := canonicalMulWithWork_width (nat cell) side (B + 4)
    ((nat_width_le cell).trans (by omega)) (by omega)
  have hupp := canonicalMulWithWork_width (nat (bitWordValue next.1)) side (B + 4)
    ((nat_width_le _).trans (by omega)) (by omega)
  change lower.1.width ≤ _ at hlow
  change upper.1.width ≤ _ at hupp
  have hfirstQ := divWithWork_width_uniform lower.1 (nat g) (4 * B + 18)
    (by omega) ((nat_width_le g).trans (by omega))
  have hlastQ := divWithWork_width_uniform upper.1 (nat g) (4 * B + 18)
    (by omega) ((nat_width_le g).trans (by omega))
  change firstQ.1.width ≤ _ at hfirstQ
  change lastQ.1.width ≤ _ at hlastQ
  have hfirst : Nat.size (bitWordValue first.1) ≤ 16 * B + 78 := by
    have h := (naturalWordSize_le first.1).trans (naturalCeilingWithWork_length firstQ.1)
    omega
  have hlast : Nat.size (bitWordValue last.1) ≤ 16 * B + 78 := by
    have h := (naturalWordSize_le last.1).trans (naturalCeilingWithWork_length lastQ.1)
    omega
  have hindex (i : ℕ) (hi : i ∈ indices) : Nat.size i ≤ 16 * B + 78 := by
    obtain ⟨j, hj, hij⟩ := List.mem_range'.mp hi
    have hcount : bitWordValue count.1 = bitWordValue last.1 - bitWordValue first.1 :=
      saturatingSubtractWithWork_value _ _
    have hle : i ≤ bitWordValue last.1 := by omega
    exact (Nat.size_le_size hle).trans hlast
  let point := fun i =>
    let product := binaryNaturalMulWithWork g i
    (bitWordValue product.1, product.2 + Nat.size i + 2)
  have hpoint (i : ℕ) (hi : i ∈ indices) : (point i).2 ≤ cellGridPointBitBudget B := by
    have hm := binaryNaturalMulWithWork_cost g i
    have his := hindex i hi
    dsimp only [point]
    unfold cellGridPointBitBudget
    nlinarith only [hm, his, hg, Nat.zero_le B]
  have hmap := arithmeticMapWithWork_cost point indices (cellGridPointBitBudget B) hpoint
  have hmaplen : indices.length = (cellGridPoints side.value g cell).length := by
    have hv := congrArg List.length (cellGridPointsWithWork_value side g cell)
    simpa only [cellGridPointsWithWork, arithmeticMapWithWork_value, List.length_map] using hv
  have hnextc := binaryNaturalAddWithWork_cost cell 1
  have hlowc := canonicalMulWithWork_cost (nat cell) side (B + 4)
    ((nat_width_le cell).trans (by omega)) (by omega)
  have huppc := canonicalMulWithWork_cost (nat (bitWordValue next.1)) side (B + 4)
    ((nat_width_le _).trans (by omega)) (by omega)
  have hfirstc := divWithWork_cost lower.1 (nat g) (4 * B + 18)
    (by omega) ((nat_width_le g).trans (by omega))
  have hlastc := divWithWork_cost upper.1 (nat g) (4 * B + 18)
    (by omega) ((nat_width_le g).trans (by omega))
  have hfc := (naturalCeilingWithWork_cost firstQ.1).trans
    (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (by omega : firstQ.1.width + 1 ≤ 16 * B + 77) 2))
  have hlc := (naturalCeilingWithWork_cost lastQ.1).trans
    (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (by omega : lastQ.1.width + 1 ≤ 16 * B + 77) 2))
  have hcc := saturatingSubtractWithWork_cost (bitWordValue last.1) (bitWordValue first.1)
  change next.2 ≤ _ at hnextc
  change lower.2 ≤ _ at hlowc
  change upper.2 ≤ _ at huppc
  change firstQ.2 ≤ _ at hfirstc
  change lastQ.2 ≤ _ at hlastc
  change first.2 ≤ _ at hfc
  change last.2 ≤ _ at hlc
  change count.2 ≤ _ at hcc
  simp only [Nat.size_one, Nat.add_assoc, Nat.reduceAdd] at hnextc hlowc huppc hfirstc hlastc
  have hsetup : next.2 + lower.2 + upper.2 + firstQ.2 + lastQ.2 + first.2 + last.2 + count.2 +
      Nat.size cell + Nat.size g + 10 ≤ cellGridSetupBitBudget B := by
    unfold cellGridSetupBitBudget
    nlinarith only [hnextc, hlowc, huppc, hfirstc, hlastc, hfc, hlc, hcc,
      hfirst, hlast, hc, hg, Nat.zero_le B]
  constructor
  · change next.2 + lower.2 + upper.2 + firstQ.2 + lastQ.2 + first.2 + last.2 + count.2 +
      (arithmeticMapWithWork point indices).2 + indices.length + Nat.size cell + Nat.size g + 10 ≤ _
    unfold cellGridPointsBitBudget
    rw [← hmaplen]
    nlinarith only [hsetup, hmap, Nat.zero_le indices.length]
  · intro x hx
    have hx' : x ∈ (arithmeticMapWithWork point indices).1 := by
      simpa only [cellGridPointsWithWork, next, lower, upper, firstQ, lastQ, first,
        last, count, indices, point] using hx
    rw [arithmeticMapWithWork_value] at hx'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    dsimp only [point]
    rw [binaryNaturalMulWithWork_value]
    have hprod := natural_product_bit_length g i
    have hidx := hindex i hi
    omega

theorem cellStatesWithWork_cost (n g B : ℕ) (side : BinaryFraction) (cell : ℕ × ℕ)
    (hn : Nat.size n ≤ B) (hg : Nat.size g ≤ B) (hs : side.width ≤ B)
    (hleft : Nat.size cell.1 ≤ B) (hright : Nat.size cell.2 ≤ B) :
    (cellStatesWithWork n g side cell).2 ≤ cellStatesBitBudget
      (cellGridPoints side.value g cell.1).length (cellGridPoints side.value g cell.2).length B := by
  let left := cellGridPointsWithWork side g cell.1
  let right := cellGridPointsWithWork side g cell.2
  have hl := cellGridPointsWithWork_bounds side g cell.1 B hs hg hleft
  have hr := cellGridPointsWithWork_bounds side g cell.2 B hs hg hright
  have htest (lo : ℕ) (hlo : lo ∈ left.1) :
      (filterMapWithWork (makeStateWithWork n lo) right.1).2 ≤
        right.1.length * (16 * (17 * B + 78) + 11) := by
    exact filterMapWithWork_cost _ _ (16 * (17 * B + 78) + 8) (fun hi hhi =>
      makeStateWithWork_cost n lo hi (17 * B + 78) (by omega) (hl.2 lo hlo) (hr.2 hi hhi))
  have hlen (lo : ℕ) : (filterMapWithWork (makeStateWithWork n lo) right.1).1.length ≤
      right.1.length := by
    rw [filterMapWithWork_value]
    exact List.length_filterMap_le _ _
  have hf := arithmeticFlatMapWithWork_cost (fun lo => filterMapWithWork (makeStateWithWork n lo) right.1)
    left.1 (right.1.length * (16 * (17 * B + 78) + 11)) right.1.length
    htest (fun lo _ => hlen lo)
  have hll : left.1.length = (cellGridPoints side.value g cell.1).length :=
    congrArg List.length (cellGridPointsWithWork_value side g cell.1)
  have hrl : right.1.length = (cellGridPoints side.value g cell.2).length :=
    congrArg List.length (cellGridPointsWithWork_value side g cell.2)
  rw [hll, hrl] at hf
  change left.2 + right.2 + (arithmeticFlatMapWithWork
    (fun lo => filterMapWithWork (makeStateWithWork n lo) right.1) left.1).2 + 2 ≤ _
  unfold cellStatesBitBudget
  have hlc : left.2 ≤ _ := hl.1
  have hrc : right.2 ≤ _ := hr.1
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupSetup
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

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryWideChildWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every child-grid list is constructed before the Cartesian product.
These bounds include the balanced endpoints, integer spacing and radius,
endpoint translations, and the two bounded grid loops. -/

namespace EditApproximation

theorem seedGridSpacingWithWork_bounds (b P B : ℕ)
    (hb : Nat.size b ≤ B) (hP : Nat.size P ≤ B) :
    (seedGridSpacingWithWork b P).1.length ≤ B + 1 ∧
      (seedGridSpacingWithWork b P).2 ≤ 100 * (B + 2) ^ 2 := by
  let quotient := binaryNaturalDivModWithWork b P
  have hl := (bitDivModWithWork_lengths P.bits b.bits).1
  change quotient.1.length = b.bits.length at hl
  rw [Nat.size_eq_bits_len] at hl
  have hd := binaryNaturalDivModWithWork_cost b P
  have ht := wordLEWithWork_cost quotient.1 [true]
  change quotient.2.2 ≤ _ at hd
  simp only [List.length_cons, List.length_nil] at ht
  unfold seedGridSpacingWithWork
  dsimp only
  constructor
  · split_ifs
    · simp only [List.length_cons, List.length_nil]
      omega
    · change quotient.1.length ≤ B + 1
      omega
  · change quotient.2.2 + (wordLEWithWork quotient.1 [true]).2 + 2 ≤ _
    nlinarith only [hd, ht, hl, hb, hP, Nat.zero_le B]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalGuardWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every local eligibility test is charged at the bit level, including
its rational divisions and the construction of its two thresholds. -/

namespace EditApproximation
namespace BinaryFraction

theorem centerEligibilityWithWork_cost (b F B : ℕ) (a initial : BinaryFraction)
    (hB : 6 ≤ B) (hb : Nat.size b + 2 ≤ B) (hF : Nat.size F + 2 ≤ B)
    (ha : a.width ≤ B) (hi : initial.width ≤ B) :
    (centerEligibilityWithWork b F a initial).2 ≤ localEligibilityBitBudget B := by
  have hfour : (nat 4).width ≤ B := (nat_width_le 4).trans (by
    have h : Nat.size 4 = 3 := by decide
    omega)
  have height : (nat 8).width ≤ B := (nat_width_le 8).trans (by
    have h : Nat.size 8 = 4 := by decide
    omega)
  have hbn := (nat_width_le b).trans hb
  have hFn := (nat_width_le F).trans hF
  have hdw := canonicalMulWithWork_width (nat 4) a B hfour ha
  have hdc := canonicalMulWithWork_cost (nat 4) a B hfour ha
  have hlw := divWithWork_width_uniform (nat b) (canonicalMulWithWork (nat 4) a).1
    (4 * B + 2) (by omega) hdw
  have hlc := divWithWork_cost (nat b) (canonicalMulWithWork (nat 4) a).1
    (4 * B + 2) (by omega) hdw
  have hfw := canonicalMulWithWork_width (nat 8) (nat F) B height hFn
  have hfc := canonicalMulWithWork_cost (nat 8) (nat F) B height hFn
  have huw := canonicalMulWithWork_width (canonicalMulWithWork (nat 8) (nat F)).1 (nat b)
    (4 * B + 2) hfw (by omega)
  have huc := canonicalMulWithWork_cost (canonicalMulWithWork (nat 8) (nat F)).1 (nat b)
    (4 * B + 2) hfw (by omega)
  have hlow := leWithWork_cost (divWithWork (nat b) (canonicalMulWithWork (nat 4) a).1).1
    initial (16 * B + 12) (by omega) (by omega)
  have hhigh := leWithWork_cost initial
    (canonicalMulWithWork (canonicalMulWithWork (nat 8) (nat F)).1 (nat b)).1
    (16 * B + 12) (by omega) (by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hlc huc hlow hhigh
  change _ + _ + _ + _ + _ + _ + Nat.size b + Nat.size F + 8 ≤ _
  unfold localEligibilityBitBudget
  omega

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCellCentersWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete work for a whole-cell representative scan, including both
endpoint grids and every initial-value eligibility test. -/

namespace EditApproximation
namespace BinaryFraction

private theorem flatMap_length_bound {α β : Type*} (f : α → List β)
    (xs : List α) (n : ℕ) (h : ∀ x ∈ xs, (f x).length ≤ n) :
    (xs.flatMap f).length ≤ xs.length * n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have hh := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem cellStatesWithWork_length (n g : ℕ) (side : BinaryFraction) (cell : ℕ × ℕ) :
    (cellStatesWithWork n g side cell).1.length ≤
      (cellGridPoints side.value g cell.1).length *
        (cellGridPoints side.value g cell.2).length := by
  simp only [cellStatesWithWork, arithmeticFlatMapWithWork_value, filterMapWithWork_value,
    makeStateWithWork_value]
  have h := flatMap_length_bound
    (fun lo => ((cellGridPointsWithWork side g cell.2).1.filterMap (makeTargetState n lo)))
    (cellGridPointsWithWork side g cell.1).1 (cellGridPointsWithWork side g cell.2).1.length
    (fun _ _ => List.length_filterMap_le _ _)
  simpa only [cellGridPointsWithWork_value] using h

theorem cellCentersWithWork_cost {n : ℕ} (P F b B : ℕ) (a theta : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction) (cell : ℕ × ℕ)
    (hB : 6 ≤ B) (hn : Nat.size n ≤ B) (hb : Nat.size b + 2 ≤ B)
    (hP : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B)
    (ha : a.width ≤ B) (htheta : theta.width ≤ B)
    (hi : ∀ q, (initial q).width ≤ B)
    (hleft : Nat.size cell.1 ≤ B) (hright : Nat.size cell.2 ≤ B) :
    (cellCentersWithWork P F b a theta initial cell).2 ≤
      cellCentersBitBudget
        (cellGridPoints (theta.value * b) (bitWordValue (seedGridSpacingWithWork b P).1) cell.1).length
        (cellGridPoints (theta.value * b) (bitWordValue (seedGridSpacingWithWork b P).1) cell.2).length B := by
  let spacing := seedGridSpacingWithWork b P
  let side := canonicalMulWithWork theta (nat b)
  let states := cellStatesWithWork n (bitWordValue spacing.1) side.1 cell
  let C := 4 * B + 40
  have hspacing := seedGridSpacingWithWork_bounds b P B (by omega) hP
  have hgs : Nat.size (bitWordValue spacing.1) ≤ C :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length spacing.1)).trans (by
      have hh : spacing.1.length ≤ B + 1 := hspacing.1
      dsimp only [C]
      omega)
  have hsidew := canonicalMulWithWork_width theta (nat b) B htheta ((nat_width_le b).trans hb)
  have hsidec := canonicalMulWithWork_cost theta (nat b) B htheta ((nat_width_le b).trans hb)
  change side.1.width ≤ 4 * B + 2 at hsidew
  have hstates := cellStatesWithWork_cost n (bitWordValue spacing.1) C side.1 cell
    (by dsimp only [C]; omega) hgs (by dsimp only [C]; omega)
    (by dsimp only [C]; omega) (by dsimp only [C]; omega)
  have hcount := cellStatesWithWork_length n (bitWordValue spacing.1) side.1 cell
  have hselected := filterWithWork_cost
    (fun r => centerEligibilityWithWork b F a (initial r)) states.1
    (localEligibilityBitBudget B)
    (fun r _ => centerEligibilityWithWork_cost b F B a (initial r) hB hb hF ha (hi r))
  change states.1.length ≤ _ at hcount
  change states.2 ≤ _ at hstates
  change side.2 ≤ _ at hsidec
  change spacing.2 + side.2 + states.2 +
    (filterWithWork (fun r => centerEligibilityWithWork b F a (initial r)) states.1).2 + 3 ≤ _
  have hsc : spacing.2 ≤ 100 * (B + 2) ^ 2 := hspacing.2
  have hv : side.1.value = theta.value * b := by
    simp only [side, canonicalMulWithWork_value, nat_value]
  rw [hv] at hstates hcount
  unfold cellCentersBitBudget
  change _ ≤ 100 * (B + 2) ^ 2 + 2000 * (B + 1) ^ 2 +
    cellStatesBitBudget
      (cellGridPoints (theta.value * b) (bitWordValue spacing.1) cell.1).length
      (cellGridPoints (theta.value * b) (bitWordValue spacing.1) cell.2).length (4 * B + 40) +
    (cellGridPoints (theta.value * b) (bitWordValue spacing.1) cell.1).length *
      (cellGridPoints (theta.value * b) (bitWordValue spacing.1) cell.2).length *
        (localEligibilityBitBudget B + 3) + 3
  have hfilter := hselected.trans (Nat.mul_le_mul_right _ hcount)
  dsimp only [C] at hstates
  omega

theorem cellCentersBitBudget_mono_count (l l' r r' B : ℕ) (hl : l ≤ l') (hr : r ≤ r') :
    cellCentersBitBudget l r B ≤ cellCentersBitBudget l' r' B := by
  unfold cellCentersBitBudget cellStatesBitBudget cellGridPointsBitBudget
  gcongr

theorem cellCentersWithWork_uniform_cost {n : ℕ} (P F b B : ℕ) (a theta : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction) (cell : ℕ × ℕ)
    (hB : 6 ≤ B) (hn : Nat.size n ≤ B) (hb : Nat.size b + 2 ≤ B)
    (hP : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B)
    (ha : a.width ≤ B) (htheta : theta.width ≤ B)
    (hi : ∀ q, (initial q).width ≤ B)
    (hleft : Nat.size cell.1 ≤ B) (hright : Nat.size cell.2 ≤ B)
    (hthetaValue : 0 ≤ theta.value ∧ theta.value ≤ 1)
    (hbdyadic : ∃ e : ℕ, b = 2 ^ e) (hPdyadic : ∃ e : ℕ, P = 2 ^ e) :
    (cellCentersWithWork P F b a theta initial cell).2 ≤ cellCentersBitBudget P P B := by
  have hPpos : 0 < P := by obtain ⟨e, rfl⟩ := hPdyadic; exact Nat.two_pow_pos e
  have hg : (0 : ℚ) < seedGridSpacing b P := by
    exact_mod_cast (show 0 < seedGridSpacing b P by unfold seedGridSpacing; omega)
  have hcover : (b : ℚ) ≤ P * (seedGridSpacing b P : ℚ) := by
    exact_mod_cast seedGridSpacing_covers_dyadic hbdyadic hPdyadic
  have hsize : theta.value * b / seedGridSpacing b P ≤ (P : ℚ) := by
    apply (div_le_iff₀ hg).2
    have hb : theta.value * b ≤ (b : ℚ) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hthetaValue.2 (Nat.cast_nonneg (α := ℚ) b)
    exact hb.trans hcover
  have hlen (j : ℕ) : (cellGridPoints (theta.value * b) (seedGridSpacing b P) j).length ≤ P :=
    cellGridPoints_length_le (mul_nonneg hthetaValue.1 (Nat.cast_nonneg _)) hsize
  have hc := cellCentersWithWork_cost P F b B a theta initial cell hB hn hb hP hF ha htheta hi hleft hright
  rw [seedGridSpacingWithWork_value b P hPpos] at hc
  exact hc.trans (cellCentersBitBudget_mono_count _ _ _ _ B (hlen cell.1) (hlen cell.2))

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalArithmeticBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compiled optimizer counter specialized to the literal representative
bands. Preparation of the input arrays remains a separate finite loop. -/

namespace EditApproximation

theorem computedBandActions_length_le {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (tau theta velocity : ℚ)
    (child : Fin M → TargetInterval ny → ℚ) :
    (computedBandActions parent r b P tau theta velocity child).length ≤
      (wideActionList M parent r b P).length := by
  dsimp only [computedBandActions]
  split_ifs <;> first | exact List.length_filter_le _ _ | exact Nat.zero_le _

theorem representativeBandActions_length_le {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P : ℕ) (tau theta : ℚ) (child : Fin M → TargetInterval target.length → ℚ) :
    (representativeBandActions source target parent r b P tau theta child).length ≤
      (wideActionList M parent r b P).length := by
  dsimp only [representativeBandActions]
  split_ifs <;> first | exact computedBandActions_length_le _ _ _ _ _ _ _ _ | exact Nat.zero_le _

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedCellGroupWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete per-cell arithmetic. The count includes construction and
testing of every candidate, and the actual finite-count sampled selector. -/

namespace EditApproximation
namespace BinaryFraction

theorem preparedCellGroupWithWork_cost {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F e Q B : ℕ)
    (hbpos : 0 < b) (tau a : BinaryFraction)
    (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (raw : List BinaryFraction)
    (hraw : raw.map value = groupDyadicScales M b (nat F).value)
    (draw : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → Fin M)
    (hPpos : 0 < P) (cell : ℕ × ℕ)
    (hB : 6 ≤ B) (hnx : Nat.size source.length + 2 ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hM : Nat.size M + 2 ≤ B)
    (hQ : Nat.size Q + 2 ≤ B) (hb : Nat.size b + 2 ≤ B)
    (hP : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B) (he : e + 1 ≤ B)
    (htau : tau.width ≤ B) (ha : a.width ≤ B)
    (hparent : ∀ q, (parentInitial q).width ≤ B)
    (hchild : ∀ i q, (child i q).width ≤ B)
    (hinitial : ∀ i q, (initial i q).width ≤ B)
    (hcurrent : ∀ i q, (current i q).width ≤ B)
    (hscale : ∀ x ∈ raw, x.width ≤ B)
    (hleft : Nat.size cell.1 ≤ B) (hright : Nat.size cell.2 ≤ B)
    (hbdyadic : ∃ j : ℕ, b = 2 ^ j) (hPdyadic : ∃ j : ℕ, P = 2 ^ j) :
    (preparedCellGroupWithWork source target parent b P F e Q hbpos tau a
      parentInitial child initial current raw hraw draw hPpos cell).2 ≤
      preparedCellGroupBitBudget M (groupDyadicScales M b (nat F).value).length e b P B := by
  let V := (40 * P + 2) ^ (2 * M)
  let centers := cellCentersWithWork P F b a (inversePowerTwo e) parentInitial cell
  let members := filterMapWithWork
    (preparedUnskippedCandidateWithWork source target parent b P e hbpos hPpos tau (nat F) child initial)
    centers.1
  have ht : (inversePowerTwo e).width ≤ B := by rw [inversePowerTwo_width]; exact he
  have htValue : 0 ≤ (inversePowerTwo e).value ∧ (inversePowerTwo e).value ≤ 1 := by
    rw [inversePowerTwo_value, zpow_neg, zpow_natCast]
    exact ⟨by positivity, inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))⟩
  have hc := cellCentersWithWork_uniform_cost P F b B a (inversePowerTwo e) parentInitial cell
    hB (by omega) hb hP hF ha ht hparent hleft hright htValue hbdyadic hPdyadic
  change centers.2 ≤ cellCentersBitBudget P P B at hc
  have hclen : centers.1.length ≤ (P + 1) ^ 2 := by
    rw [cellCentersWithWork_value P F b a (inversePowerTwo e) parentInitial cell hPpos]
    exact cellRepresentativeStates_length_le a.value (fun q => (parentInitial q).value)
      (inversePowerTwo e).value cell htValue hbdyadic hPdyadic
  have hmc := filterMapWithWork_cost
    (preparedUnskippedCandidateWithWork source target parent b P e hbpos hPpos tau (nat F) child initial)
    centers.1 (preparedUnskippedBitBudget e b M P V V B) (fun r _ =>
      preparedUnskippedCandidateWithWork_uniform_cost source target parent b P e B hbpos hPpos
        tau (nat F) child initial r hnx hny (by omega) hb hP he htau
        ((nat_width_le F).trans hF) hchild hinitial)
  change members.2 ≤ _ at hmc
  have hmlen : members.1.length ≤ (P + 1) ^ 2 := by
    have hm : members.1.length ≤ centers.1.length := by
      dsimp only [members]
      rw [filterMapWithWork_value]
      exact List.length_filterMap_le _ _
    exact hm.trans hclen
  have hmc' := hmc.trans (Nat.mul_le_mul_right _ hclen)
  unfold preparedCellGroupWithWork
  dsimp only
  by_cases hempty : members.1 = []
  · rw [dite_eq_left hempty]
    change centers.2 + members.2 + 1 ≤ _
    unfold preparedCellGroupBitBudget
    change _ ≤ cellCentersBitBudget P P B +
      (P + 1) ^ 2 * (preparedUnskippedBitBudget e b M P V V B + 3) + _ + 2
    omega
  · rw [dite_eq_right hempty]
    have hselected := sampledGroupActionWithWork_cost source target parent b P e Q tau (nat F)
      child initial current (indexedGroupScales raw M b (nat F).value hraw)
      (fun t j => draw t (Fin.cast (congrArg (groupSampleCount M Q b)
        (indexedGroupScales_value raw M b (nat F).value hraw t)) j)) members.1 hempty V B
      hM hQ hb hny (fun t => hscale _ (List.get_mem _ _))
      (fun member _ => (representativeBandActions_length_le source target parent member.center b P
        tau.value ((2 : ℚ) ^ (-(e : ℤ))) (fun i q => (child i q).value)).trans
          (wideActionList_length_le M parent member.center b P hPpos))
      (fun _ _ _ _ i => hinitial i _) hcurrent
    change (dyadicSampledGroupActionWithWork source target parent b P e Q tau (nat F)
      child initial current raw hraw draw members.1 hempty).2 ≤ _ at hselected
    have hselected' : (dyadicSampledGroupActionWithWork source target parent b P e Q tau (nat F)
        child initial current raw hraw draw members.1 hempty).2 ≤
        selectedGroupBitBudget M (groupDyadicScales M b (nat F).value).length e b ((P + 1) ^ 2) V B := by
      apply hselected.trans
      unfold selectedGroupBitBudget
      gcongr
    change centers.2 + members.2 +
      (dyadicSampledGroupActionWithWork source target parent b P e Q tau (nat F)
        child initial current raw hraw draw members.1 hempty).2 + 2 ≤ _
    unfold preparedCellGroupBitBudget
    change _ ≤ cellCentersBitBudget P P B +
      (P + 1) ^ 2 * (preparedUnskippedBitBudget e b M P V V B + 3) +
      selectedGroupBitBudget M (groupDyadicScales M b (nat F).value).length e b ((P + 1) ^ 2) V B + 2
    omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedComputedCellWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cell cost includes materializing the exact dyadic scale array;
the finite draw counts are then those of the original cell sampler. -/

namespace EditApproximation
namespace BinaryFraction

theorem preparedComputedCellGroupWithWork_cost {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F e Q eM eb eF B : ℕ)
    (hMdef : M = 2 ^ eM) (hbdef : b = 2 ^ eb) (hFdef : F = 2 ^ eF) (hPpos : 0 < P)
    (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : cellScaleDraw M b Q (nat F).value) (cell : ℕ × ℕ)
    (hB : 6 ≤ B) (hnx : Nat.size source.length + 2 ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hM : Nat.size M + 2 ≤ B)
    (hQ : Nat.size Q + 2 ≤ B) (hb : Nat.size b + 2 ≤ B)
    (hP : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B) (he : e + 1 ≤ B)
    (htau : tau.width ≤ B) (ha : a.width ≤ B)
    (hparent : ∀ q, (parentInitial q).width ≤ B)
    (hchild : ∀ i q, (child i q).width ≤ B)
    (hinitial : ∀ i q, (initial i q).width ≤ B)
    (hcurrent : ∀ i q, (current i q).width ≤ B)
    (hscale : eM + eb + eF + 7 ≤ B)
    (hleft : Nat.size cell.1 ≤ B) (hright : Nat.size cell.2 ≤ B)
    (hPdyadic : ∃ j : ℕ, P = 2 ^ j) :
    (preparedComputedCellGroupWithWork source target parent b P F e Q eM eb eF
      hMdef hbdef hFdef hPpos tau a parentInitial child initial current draw cell).2 ≤
      groupScalesBitBudget eM eb eF +
        preparedCellGroupBitBudget M (groupDyadicScales M b (nat F).value).length e b P B + 1 := by
  have hs := groupScalesWithWork_bounds eM eb eF
  have hc := preparedCellGroupWithWork_cost source target parent b P F e Q B
    (by rw [hbdef]; exact Nat.two_pow_pos eb) tau a parentInitial child initial current
    (groupScalesWithWork eM eb eF).1 (computedGroupScales_value M b F eM eb eF hMdef hbdef hFdef)
    draw hPpos cell hB hnx hny hM hQ hb hP hF he htau ha hparent hchild hinitial hcurrent
    (fun x hx => (hs.1 x hx).trans hscale) hleft hright ⟨eb, hbdef⟩ hPdyadic
  change (groupScalesWithWork eM eb eF).2 + _ + 1 ≤ _
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedLocalGroupWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bit work of the literal query-local whole-cell loops.  The tested scale
inequality bounds both coordinate ranges; every generated cell invokes the
complete counted band and sampled-action routine. -/

namespace EditApproximation
namespace BinaryFraction

private theorem queryCellCoordinates_length (F b exponent p : ℕ) (w : ℚ)
    (hF : 1 ≤ F) (hb : 1 ≤ b) (hw : 0 ≤ w) (hwindow : w / (16 * F) ≤ b) :
    (localCellCoordinates ((2 : ℚ) ^ (-(exponent : ℤ)) * b) p ⌈w⌉₊).length ≤
      (32 * F + 2) * 2 ^ exponent + 2 := by
  have hFp : (0 : ℚ) < F := by exact_mod_cast (show 0 < F by omega)
  have hbp : (0 : ℚ) < b := by exact_mod_cast (show 0 < b by omega)
  have hbR : (1 : ℚ) ≤ b := by exact_mod_cast hb
  have hs : 0 < (2 : ℚ) ^ (-(exponent : ℤ)) * b := by positivity
  apply localCellCoordinates_length_le _ hs _ _ ((32 * F + 2) * 2 ^ exponent)
  apply (div_le_iff₀ hs).2
  have hw' : w ≤ 16 * (F : ℚ) * b := by
    nlinarith only [(div_le_iff₀ (by positivity : (0 : ℚ) < 16 * F)).mp hwindow]
  have hc : (⌈w⌉₊ : ℚ) < w + 1 := Nat.ceil_lt_add_one hw
  have heq : (((32 * F + 2) * 2 ^ exponent : ℕ) : ℚ) *
      ((2 : ℚ) ^ (-(exponent : ℤ)) * b) = (32 * (F : ℚ) + 2) * b := by
    push_cast
    rw [zpow_neg, zpow_natCast]
    field_simp
  rw [heq]
  nlinarith only [hc, hw', hbR]

theorem preparedLocalGroupScaleWithWork_cost {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent Q eM eF eb B : ℕ)
    (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF) (hPpos : 0 < P)
    (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length)
    (hB : 7 ≤ B) (hnx : Nat.size source.length + 2 ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hM : Nat.size M + 2 ≤ B)
    (hQ : Nat.size Q + 2 ≤ B) (hP : Nat.size P ≤ B)
    (hF : Nat.size F + 2 ≤ B) (he : exponent + 1 ≤ B) (heb : eb ≤ B)
    (hes : eM + eF + 7 ≤ B)
    (htau : tau.width ≤ B) (ha : a.width ≤ B)
    (hparent : ∀ q, (parentInitial q).width ≤ B)
    (hchild : ∀ i q, (child i q).width ≤ B)
    (hinitial : ∀ i q, (initial i q).width ≤ B)
    (hcurrent : ∀ i q, (current i q).width ≤ B)
    (hnonneg : 0 ≤ (parentInitial query).value)
    (hwindow : (parentInitial query).value / (16 * F) ≤ (2 ^ eb : ℕ))
    (hPdyadic : ∃ j : ℕ, P = 2 ^ j) :
    (preparedLocalGroupScaleWithWork source target parent P F exponent Q eM eF eb
      hMdef hFdef hPpos tau a parentInitial child initial current draw query).2 ≤
      preparedLocalGroupScaleBitBudget M P F exponent eM eF eb B := by
  let b := 2 ^ eb
  let side := canonicalMulWithWork (inversePowerTwo exponent) (nat b)
  let radius := naturalCeilingWithWork (parentInitial query)
  let cells := targetCellsWithWork side.1 (bitWordValue radius.1) query
  let K := (32 * F + 2) * 2 ^ exponent + 2
  let C := 16 * B + 200
  have htheta : (inversePowerTwo exponent).width ≤ B :=
    by rw [inversePowerTwo_width]; exact he
  have hb : Nat.size b + 2 ≤ B + 3 := by dsimp only [b]; rw [Nat.size_pow]; omega
  have hbn : (nat b).width ≤ B + 3 := (nat_width_le b).trans hb
  have hsw := canonicalMulWithWork_width (inversePowerTwo exponent) (nat b) (B + 3)
    (by omega) hbn
  have hsc := canonicalMulWithWork_cost (inversePowerTwo exponent) (nat b) (B + 3)
    (by omega) hbn
  have hrw : Nat.size (bitWordValue radius.1) ≤ B + 2 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length radius.1)).trans
      ((naturalCeilingWithWork_length (parentInitial query)).trans (by have hh := hparent query; omega))
  have hrc := (naturalCeilingWithWork_cost (parentInitial query)).trans
    (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (Nat.add_le_add_right (hparent query) 1) 2))
  have hcoords (p : ℕ) : (localCellCoordinates side.1.value p (bitWordValue radius.1)).length ≤ K := by
    simp only [side, canonicalMulWithWork_value, inversePowerTwo_value, nat_value,
      radius, naturalCeilingWithWork_value]
    exact queryCellCoordinates_length F b exponent p (parentInitial query).value
      (by rw [hFdef]; exact Nat.succ_le_of_lt (Nat.two_pow_pos _))
      (Nat.succ_le_of_lt (Nat.two_pow_pos _)) hnonneg hwindow
  have hcc := targetCellsWithWork_cost side.1 (bitWordValue radius.1) (4 * B + 40)
    query (by change side.1.width ≤ _ at hsw; omega)
    (by omega) (by omega)
  have hcells : cells.2 ≤ targetCellsBitBudget K K (4 * B + 40) := hcc.trans (by
    unfold targetCellsBitBudget
    gcongr <;> apply hcoords)
  have hlen : cells.1.length ≤ K ^ 2 := by
    rw [targetCellsWithWork_value]
    simp only [side, canonicalMulWithWork_value, inversePowerTwo_value, nat_value,
      radius, naturalCeilingWithWork_value]
    exact localTargetCells_query_length F b exponent query (parentInitial query).value
      (by rw [hFdef]; exact Nat.succ_le_of_lt (Nat.two_pow_pos _))
      (Nat.succ_le_of_lt (Nat.two_pow_pos _)) hnonneg hwindow
  have hslen : (groupDyadicScales M b (nat F).value).length = 7 + eM + eF := by
    have hh := computedGroupScales_value M b F eM eb eF hMdef rfl hFdef
    have hlen' := congrArg List.length hh
    rw [List.length_map, groupScalesWithWork_length] at hlen'
    exact hlen'.symm
  have hcell (cell : ℕ × ℕ) (hc : cell ∈ cells.1) :=
    targetCellsWithWork_keys side.1 (bitWordValue radius.1) (4 * B + 40) query
      (by change side.1.width ≤ _ at hsw; omega)
      (by omega) (by omega) cell hc
  have hentry (cell : ℕ × ℕ) (hc : cell ∈ cells.1) :
      (preparedComputedCellGroupWithWork source target parent b P F exponent Q eM eb eF
        hMdef rfl hFdef hPpos tau a parentInitial child initial current
        (Eq.mpr (congrArg (cellScaleDraw M b Q) (nat_value F)) (draw b cell)) cell).2 ≤
      groupScalesBitBudget eM eb eF +
        preparedCellGroupBitBudget M (7 + eM + eF) exponent b P C + 1 := by
    have hk := hcell cell hc
    have hh := preparedComputedCellGroupWithWork_cost source target parent b P F exponent Q eM eb eF C
      hMdef rfl hFdef hPpos tau a parentInitial child initial current
      (Eq.mpr (congrArg (cellScaleDraw M b Q) (nat_value F)) (draw b cell)) cell
      (by dsimp only [C]; omega) (by dsimp only [C]; omega) (by dsimp only [C]; omega)
      (by dsimp only [C]; omega) (by dsimp only [C]; omega) (by dsimp only [C]; omega)
      (by dsimp only [C]; omega) (by dsimp only [C]; omega) (by dsimp only [C]; omega)
      (htau.trans (by dsimp only [C]; omega)) (ha.trans (by dsimp only [C]; omega))
      (fun q => (hparent q).trans (by dsimp only [C]; omega))
      (fun i q => (hchild i q).trans (by dsimp only [C]; omega))
      (fun i q => (hinitial i q).trans (by dsimp only [C]; omega))
      (fun i q => (hcurrent i q).trans (by dsimp only [C]; omega))
      (by dsimp only [C]; omega) (by dsimp only [C]; omega) (by dsimp only [C]; omega) hPdyadic
    simpa only [hslen] using hh
  have hfilter := filterMapWithWork_cost (fun cell =>
    preparedComputedCellGroupWithWork source target parent b P F exponent Q eM eb eF
      hMdef rfl hFdef hPpos tau a parentInitial child initial current
      (Eq.mpr (congrArg (cellScaleDraw M b Q) (nat_value F)) (draw b cell)) cell)
    cells.1 (groupScalesBitBudget eM eb eF +
      preparedCellGroupBitBudget M (7 + eM + eF) exponent b P C + 1) hentry
  have hf := hfilter.trans (Nat.mul_le_mul_right _ hlen)
  change side.2 + radius.2 + cells.2 +
    (filterMapWithWork (fun cell =>
      preparedComputedCellGroupWithWork source target parent b P F exponent Q eM eb eF
        hMdef rfl hFdef hPpos tau a parentInitial child initial current
        (Eq.mpr (congrArg (cellScaleDraw M b Q) (nat_value F)) (draw b cell)) cell) cells.1).2 + eb + 4 ≤ _
  change side.2 ≤ _ at hsc
  change radius.2 ≤ _ at hrc
  unfold preparedLocalGroupScaleBitBudget
  change _ ≤ 2000 * (B + 4) ^ 2 + 500 * (B + 1) ^ 2 +
    targetCellsBitBudget K K (4 * B + 40) + K ^ 2 *
      (groupScalesBitBudget eM eb eF + preparedCellGroupBitBudget M (7 + eM + eF) exponent b P C + 4) + eb + 4
  simp only [Nat.add_assoc, Nat.reduceAdd] at hsc hf ⊢
  omega

private theorem flatMap_cost_sum {α β : Type*} (f : α → List β × ℕ)
    (xs : List α) (C L : α → ℕ)
    (hc : ∀ x ∈ xs, (f x).2 ≤ C x) (hl : ∀ x ∈ xs, (f x).1.length ≤ L x) :
    (arithmeticFlatMapWithWork f xs).2 ≤ (xs.map (fun x => C x + L x + 3)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := hc x (by simp)
    have hxl := hl x (by simp)
    have ht := ih (fun y hy => hc y (by simp [hy])) (fun y hy => hl y (by simp [hy]))
    simp only [arithmeticFlatMapWithWork, List.map_cons, List.sum_cons]
    omega

theorem preparedLocalCellGroupsWithWork_cost_oai {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q eM eF B : ℕ)
    (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF) (hPpos : 0 < P)
    (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hnx : Nat.size source.length + 2 ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hM : Nat.size M + 2 ≤ B)
    (hQ : Nat.size Q + 2 ≤ B) (hP : Nat.size P ≤ B)
    (hF : Nat.size F + 2 ≤ B) (he : exponent + 1 ≤ B) (hes : eM + eF + 7 ≤ B)
    (htau : tau.width ≤ B) (ha : a.width ≤ B)
    (hparent : ∀ q, (parentInitial q).width ≤ B)
    (hchild : ∀ i q, (child i q).width ≤ B)
    (hinitial : ∀ i q, (initial i q).width ≤ B)
    (hcurrent : ∀ i q, (current i q).width ≤ B)
    (hnonneg : 0 ≤ (parentInitial query).value)
    (hPdyadic : ∃ j : ℕ, P = 2 ^ j) :
    (preparedLocalCellGroupsWithWork source target parent N P F exponent Q eM eF
      hMdef hFdef hPpos tau a parentInitial child initial current draw query).2 ≤
      preparedLocalGroupsBitBudget N M P F exponent eM eF B := by
  let count := max 1 N.bits.length
  let K := ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  let callback := fun eb =>
    let guard := refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query)
    if guard.1 then
      let selected := preparedLocalGroupScaleWithWork source target parent P F exponent Q eM eF eb
        hMdef hFdef hPpos tau a parentInitial child initial current draw query
      (selected.1, guard.2 + selected.2 + eb + 4)
    else ([], guard.2 + eb + 4)
  have heb (eb : ℕ) (hh : eb ∈ List.range count) : eb ≤ B := by
    have hh' := List.mem_range.mp hh
    dsimp only [count] at hh'
    rw [Nat.size_eq_bits_len] at hh'
    omega
  have hcallback (eb : ℕ) (hh : eb ∈ List.range count) :
      (callback eb).2 ≤ localEligibilityBitBudget (B + 3) +
        preparedLocalGroupScaleBitBudget M P F exponent eM eF eb B + eb + 4 ∧
      (callback eb).1.length ≤ K := by
    have he' := heb eb hh
    have hguard := refinementScaleGuardWithWork_cost F (2 ^ eb) (B + 3) a (parentInitial query)
      (hB.trans (Nat.le_add_right B 3)) (by rw [Nat.size_pow]; omega)
      (hF.trans (Nat.le_add_right B 3)) (ha.trans (Nat.le_add_right B 3))
      ((hparent query).trans (Nat.le_add_right B 3))
    dsimp only [callback]
    split_ifs with hg
    · have hwindow := ((refinementScaleGuardWithWork_value F (2 ^ eb) a (parentInitial query)).mp hg).1
      have hscale := preparedLocalGroupScaleWithWork_cost source target parent P F exponent Q eM eF eb B
        hMdef hFdef hPpos tau a parentInitial child initial current draw query
        hB hnx hny hM hQ hP hF he he' hes htau ha hparent hchild hinitial hcurrent hnonneg hwindow hPdyadic
      have hlen : (preparedLocalGroupScaleWithWork source target parent P F exponent Q eM eF eb
          hMdef hFdef hPpos tau a parentInitial child initial current draw query).1.length ≤ K := by
        unfold preparedLocalGroupScaleWithWork
        rw [filterMapWithWork_value]
        apply (List.length_filterMap_le _ _).trans
        rw [targetCellsWithWork_value]
        simp only [canonicalMulWithWork_value, inversePowerTwo_value, nat_value,
          naturalCeilingWithWork_value]
        exact localTargetCells_query_length F (2 ^ eb) exponent query (parentInitial query).value
          (by rw [hFdef]; exact Nat.succ_le_of_lt (Nat.two_pow_pos _))
          (Nat.succ_le_of_lt (Nat.two_pow_pos _)) hnonneg hwindow
      have hcost := Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.add_le_add hguard hscale) eb) 4
      simpa only using And.intro hcost hlen
    · have hcost := Nat.add_le_add_right (Nat.add_le_add_right
        (hguard.trans (Nat.le_add_right (localEligibilityBitBudget (B + 3))
          (preparedLocalGroupScaleBitBudget M P F exponent eM eF eb B))) eb) 4
      simpa only [List.length_nil] using And.intro hcost (Nat.zero_le K)
  have hsum := flatMap_cost_sum callback (List.range count)
    (fun eb => localEligibilityBitBudget (B + 3) +
      preparedLocalGroupScaleBitBudget M P F exponent eM eF eb B + eb + 4)
    (fun _ => K) (fun eb hh => (hcallback eb hh).1) (fun eb hh => (hcallback eb hh).2)
  change (arithmeticFlatMapWithWork callback (List.range count)).2 + count + N.bits.length + 2 ≤ _
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hsum count) N.bits.length) 2

end BinaryFraction
end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsWithWork_cost_oai.{u_1} := @OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsWithWork_cost_oai.{u_1}
