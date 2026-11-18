-- Prove2me | solution 1 for OAI.EditApproximation.BinaryFraction.queryWarmupInputsWithWork_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:33:33.937834+00:00
-- url     : https://prove2.me/submissions/1b768dea-d40e-4643-93f2-bb0963e43839

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
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
import Definitions.Def_OAIQ361V3Ea004

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
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
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
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
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
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalGrid
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Direct enumeration of a local grid square

The algorithm enumerates bounded ranges of grid indices. It does not
scan the unrelated target positions. The completeness theorem includes
boundary states and intervals with equal endpoints.
-/

namespace EditApproximation



theorem localTargetStates_length_le {n g radius : ℕ} (hg : 0 < g)
    (q : TargetInterval n) :
    (localTargetStates n g radius q).length ≤ (2 * radius / g + 2) ^ 2 := by
  have hpoint (p : ℕ) :
      (gridPointsBetween g (p - radius) (p + radius)).length ≤ 2 * radius / g + 2 := by
    have hlength := gridPointsBetween_length_le g (p - radius) (p + radius) hg
    have hwidth : p + radius - (p - radius) ≤ 2 * radius := by omega
    exact hlength.trans (Nat.add_le_add_right (Nat.div_le_div_right hwidth) 2)
  have hlist := list_flatMap_length_le
    (gridPointsBetween g (q.lo - radius) (q.lo + radius))
    (fun lo => (gridPointsBetween g (q.hi - radius) (q.hi + radius)).filterMap
      fun hi => makeTargetState n lo hi)
    (2 * radius / g + 2) (by
      intro lo hlo
      exact (List.length_filterMap_le _ _).trans (hpoint q.hi))
  exact hlist.trans (by simpa only [pow_two] using
    (Nat.mul_le_mul_right (2 * radius / g + 2) (hpoint q.lo)))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryFiniteLoops
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
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
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
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
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
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
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Materialization of the online coordinate array includes its equality
tests and duplicate-removal scan. Endpoints and child indices are compared
by the verified binary natural comparator. -/

namespace EditApproximation



theorem memberByWithWork_cost {α : Type*} (equal : α → α → Bool × ℕ)
    (C : ℕ) (hC : ∀ a b, (equal a b).2 ≤ C) (a : α) (xs : List α) :
    (memberByWithWork equal a xs).2 ≤ 1 + xs.length * (C + 1) := by
  induction xs with
  | nil => simp only [memberByWithWork, List.length_nil, Nat.zero_mul, Nat.add_zero, le_refl]
  | cons b xs ih =>
    have h := hC a b
    change _ + _ + 1 ≤ _
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega



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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalGridWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
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

theorem gridPointsWithWork_cost (g lo hi B : ℕ) (hg : 0 < g)
    (hgs : Nat.size g ≤ B) (hlo : Nat.size lo ≤ B) (hhi : Nat.size hi ≤ B) :
    (gridPointsWithWork g lo hi).2 ≤ gridPointsBitBudget (gridPointsBetween g lo hi).length B := by
  let lower := bitCeilDivWithWork g.bits lo.bits
  let upper := binaryNaturalDivModWithWork hi g
  let stop := binaryNaturalAddWithWork (bitWordValue upper.1) 1
  let count := saturatingSubtractWithWork (bitWordValue stop.1) (bitWordValue lower.1)
  let indices := List.range' (bitWordValue lower.1) (bitWordValue count.1)
  have hlowers : Nat.size (bitWordValue lower.1) ≤ B + 2 := by
    have h := (wordValue_size_le lower.1).trans (bitCeilDivWithWork_length g.bits lo.bits)
    exact h.trans (by simpa only [Nat.size_eq_bits_len] using Nat.add_le_add_right hlo 2)
  have huppers : Nat.size (bitWordValue upper.1) ≤ B := by
    rw [(binaryNaturalDivModWithWork_spec hi g hg).1]
    exact (Nat.size_le_size (Nat.div_le_self hi g)).trans hhi
  have hstops : Nat.size (bitWordValue stop.1) ≤ B + 3 := by
    rw [binaryNaturalAddWithWork_value]
    have h := binaryNaturalAdd_size_le (bitWordValue upper.1) 1
    have hone : Nat.size 1 = 1 := by decide
    rw [hone] at h
    omega
  have hindex (i : ℕ) (hi' : i ∈ indices) : Nat.size i ≤ B + 3 := by
    have hmem := List.mem_range'.mp hi'
    have hcount : bitWordValue count.1 = bitWordValue stop.1 - bitWordValue lower.1 :=
      saturatingSubtractWithWork_value _ _
    obtain ⟨j, hj, hij⟩ := hmem
    have hle : i ≤ bitWordValue stop.1 := by omega
    exact (Nat.size_le_size hle).trans hstops
  let points := arithmeticMapWithWork (fun i =>
    let product := binaryNaturalMulWithWork g i
    (bitWordValue product.1, product.2 + Nat.size i + 2)) indices
  have hmap := arithmeticMapWithWork_cost (fun i =>
    let product := binaryNaturalMulWithWork g i
    (bitWordValue product.1, product.2 + Nat.size i + 2)) indices
    (100 * (B + 3) ^ 2 + 2) (by
      intro i hi'
      have hcost := binaryNaturalMulWithWork_cost g i
      have his := hindex i hi'
      change (binaryNaturalMulWithWork g i).2 + Nat.size i + 2 ≤ _
      nlinarith only [hcost, hgs, his, Nat.zero_le B])
  have hlength : indices.length = (gridPointsBetween g lo hi).length := by
    have hl : bitWordValue lower.1 = lo ⌈/⌉ g := by
      -- The ceiling start is independent of the upper endpoint.
      rw [bitCeilDivWithWork_value _ _ (by simpa only [bitWordValue_bits] using hg),
        bitWordValue_bits, bitWordValue_bits]
      exact naturalCeiling_div_eq_ceilDiv lo g hg
    simp only [indices, List.length_range', count, saturatingSubtractWithWork_value,
      stop, binaryNaturalAddWithWork_value, upper,
      (binaryNaturalDivModWithWork_spec hi g hg).1, hl, gridPointsBetween_length]
  rw [hlength] at hmap
  change points.2 ≤ _ at hmap
  simp only [Nat.add_assoc, Nat.reduceAdd] at hmap
  have hlcost := bitCeilDivWithWork_cost g.bits lo.bits
  have hucost := binaryNaturalDivModWithWork_cost hi g
  have hscost := binaryNaturalAddWithWork_cost (bitWordValue upper.1) 1
  have hccost := saturatingSubtractWithWork_cost (bitWordValue stop.1) (bitWordValue lower.1)
  simp only [Nat.size_eq_bits_len] at hlcost
  change lower.2 + upper.2.2 + stop.2 + count.2 +
    points.2 + Nat.size g + Nat.size lo + Nat.size hi + 5 ≤ _
  change lower.2 ≤ _ at hlcost
  change upper.2.2 ≤ _ at hucost
  change stop.2 ≤ _ at hscost
  change count.2 ≤ _ at hccost
  have hlpow := Nat.pow_le_pow_left (show Nat.size lo + Nat.size g + 1 ≤ 2 * B + 1 by omega) 2
  have huprod := Nat.mul_le_mul (show Nat.size hi + 1 ≤ B + 1 by omega)
    (show Nat.size hi + Nat.size g + 1 ≤ 2 * B + 1 by omega)
  simp only [Nat.size_one] at hscost
  have hsetup : lower.2 + upper.2.2 + stop.2 + count.2 +
      Nat.size g + Nat.size lo + Nat.size hi + 5 ≤ 1000 * (B + 2) ^ 2 := by
    nlinarith only [hlcost, hucost, hscost, hccost, hlpow, huprod, hgs, hlo, hhi,
      hlowers, huppers, hstops, Nat.zero_le B]
  unfold gridPointsBitBudget
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

theorem gridStateBoxWithWork_cost (n g radius lo hi B : ℕ) (hg : 0 < g)
    (hn : Nat.size n ≤ B) (hgs : Nat.size g ≤ B) (hr : Nat.size radius ≤ B)
    (hl : Nat.size lo ≤ B) (hh : Nat.size hi ≤ B) :
    (gridStateBoxWithWork n g radius lo hi).2 ≤
      gridStateBoxBitBudget (2 * radius / g + 2) B := by
  let leftLow := saturatingSubtractWithWork lo radius
  let leftHigh := binaryNaturalAddWithWork lo radius
  let rightLow := saturatingSubtractWithWork hi radius
  let rightHigh := binaryNaturalAddWithWork hi radius
  let left := gridPointsWithWork g (bitWordValue leftLow.1) (bitWordValue leftHigh.1)
  let right := gridPointsWithWork g (bitWordValue rightLow.1) (bitWordValue rightHigh.1)
  let count := 2 * radius / g + 2
  have hleft : left.1 = gridPointsBetween g (lo - radius) (lo + radius) := by
    simp only [left, leftLow, leftHigh, gridPointsWithWork_value _ _ _ hg,
      saturatingSubtractWithWork_value, binaryNaturalAddWithWork_value]
  have hright : right.1 = gridPointsBetween g (hi - radius) (hi + radius) := by
    simp only [right, rightLow, rightHigh, gridPointsWithWork_value _ _ _ hg,
      saturatingSubtractWithWork_value, binaryNaturalAddWithWork_value]
  have hlen (p : ℕ) : (gridPointsBetween g (p - radius) (p + radius)).length ≤ count := by
    have h := gridPointsBetween_length_le g (p - radius) (p + radius) hg
    have hsub : p + radius - (p - radius) ≤ 2 * radius := by omega
    exact h.trans (Nat.add_le_add_right (Nat.div_le_div_right hsub) 2)
  have hllen : left.1.length ≤ count := by rw [hleft]; exact hlen lo
  have hrlen : right.1.length ≤ count := by rw [hright]; exact hlen hi
  have hleftWidth (s : ℕ) (hs : s ∈ left.1) : Nat.size s ≤ B + 2 := by
    have hp := (gridPointsBetween_sound hg (hleft ▸ hs)).2.1
    exact (Nat.size_le_size hp).trans ((binaryNaturalAdd_size_le lo radius).trans (by omega))
  have hrightWidth (s : ℕ) (hs : s ∈ right.1) : Nat.size s ≤ B + 2 := by
    have hp := (gridPointsBetween_sound hg (hright ▸ hs)).2.1
    exact (Nat.size_le_size hp).trans ((binaryNaturalAdd_size_le hi radius).trans (by omega))
  have hstate (s : ℕ) (hs : s ∈ left.1) :
      (filterMapWithWork (makeStateWithWork n s) right.1).2 ≤
        count * (16 * (B + 2) + 11) := by
    have h := filterMapWithWork_cost (makeStateWithWork n s) right.1 (16 * (B + 2) + 8)
      (fun t ht => makeStateWithWork_cost n s t (B + 2) (by omega) (hleftWidth s hs) (hrightWidth t ht))
    exact h.trans (Nat.mul_le_mul_right _ hrlen)
  have hstateLen (s : ℕ) : (filterMapWithWork (makeStateWithWork n s) right.1).1.length ≤ count := by
    rw [filterMapWithWork_value]
    exact (List.length_filterMap_le _ _).trans hrlen
  have hflat := arithmeticFlatMapWithWork_cost
    (fun s => filterMapWithWork (makeStateWithWork n s) right.1) left.1
    (count * (16 * (B + 2) + 11)) count hstate (fun s _ => hstateLen s)
  have hflat' := hflat.trans (Nat.mul_le_mul_right _ hllen)
  have hlc := gridPointsWithWork_cost g (bitWordValue leftLow.1) (bitWordValue leftHigh.1) (B + 2) hg
    (by omega) (by rw [saturatingSubtractWithWork_value]; exact (Nat.size_le_size (Nat.sub_le _ _)).trans (by omega))
    (by rw [binaryNaturalAddWithWork_value]; exact (binaryNaturalAdd_size_le lo radius).trans (by omega))
  have hrc := gridPointsWithWork_cost g (bitWordValue rightLow.1) (bitWordValue rightHigh.1) (B + 2) hg
    (by omega) (by rw [saturatingSubtractWithWork_value]; exact (Nat.size_le_size (Nat.sub_le _ _)).trans (by omega))
    (by rw [binaryNaturalAddWithWork_value]; exact (binaryNaturalAdd_size_le hi radius).trans (by omega))
  conv_rhs at hlc =>
    simp only [leftLow, leftHigh, saturatingSubtractWithWork_value, binaryNaturalAddWithWork_value]
  conv_rhs at hrc =>
    simp only [rightLow, rightHigh, saturatingSubtractWithWork_value, binaryNaturalAddWithWork_value]
  have hlc' : left.2 ≤ gridPointsBitBudget count (B + 2) := by
    apply hlc.trans
    unfold gridPointsBitBudget
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (hlen lo)) _
  have hrc' : right.2 ≤ gridPointsBitBudget count (B + 2) := by
    apply hrc.trans
    unfold gridPointsBitBudget
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (hlen hi)) _
  have hll := saturatingSubtractWithWork_cost lo radius
  have hlh := binaryNaturalAddWithWork_cost lo radius
  have hrl := saturatingSubtractWithWork_cost hi radius
  have hrh := binaryNaturalAddWithWork_cost hi radius
  change leftLow.2 ≤ _ at hll
  change leftHigh.2 ≤ _ at hlh
  change rightLow.2 ≤ _ at hrl
  change rightHigh.2 ≤ _ at hrh
  let states := arithmeticFlatMapWithWork (fun s => filterMapWithWork (makeStateWithWork n s) right.1) left.1
  change states.2 ≤ _ at hflat'
  change leftLow.2 + leftHigh.2 + rightLow.2 + rightHigh.2 + left.2 + right.2 + states.2 + 6 ≤ _
  unfold gridStateBoxBitBudget
  change _ ≤ 96 * (B + 1) + 2 * gridPointsBitBudget count (B + 2) +
    count * (count * (16 * (B + 2) + 11) + count + 3) + 6
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryWideGridWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial per-child bit work before the explicitly counted Cartesian
product. All interval endpoints and arities are bounded by their input
word sizes; no good-seed premise occurs in these bounds. -/

namespace EditApproximation

theorem balancedCutWithWork_cost (lo width M i B : ℕ) (hM : 0 < M)
    (hl : Nat.size lo ≤ B) (hw : Nat.size width ≤ B)
    (hm : Nat.size M ≤ B) (hi : Nat.size i ≤ B) :
    (balancedCutWithWork lo width M i).2 ≤ 1000 * (B + 1) ^ 2 := by
  let product := binaryNaturalMulWithWork i width
  let quotient := binaryNaturalDivModWithWork (bitWordValue product.1) M
  have hp := binaryNaturalMulWithWork_cost i width
  have hpl := bitMulWithWork_length i.bits width.bits
  have hps : Nat.size (bitWordValue product.1) ≤ 3 * B + 1 := by
    have hv : Nat.size (bitWordValue product.1) ≤ product.1.length :=
      Nat.size_le.mpr (bitWordValue_lt_pow_length _)
    change product.1.length ≤ _ at hpl
    simp only [Nat.size_eq_bits_len] at hpl
    omega
  have hq := binaryNaturalDivModWithWork_cost (bitWordValue product.1) M
  have hqs : Nat.size (bitWordValue quotient.1) ≤ 3 * B + 1 := by
    rw [(binaryNaturalDivModWithWork_spec _ M hM).1]
    exact (Nat.size_le_size (Nat.div_le_self _ _)).trans hps
  have ha := binaryNaturalAddWithWork_cost lo (bitWordValue quotient.1)
  change product.2 + quotient.2.2 + (binaryNaturalAddWithWork lo (bitWordValue quotient.1)).2 + 2 ≤ _
  nlinarith only [hp, hq, ha, hps, hqs, hl, hw, hm, hi, Nat.zero_le B]

theorem sourceChildWithWork_cost {n M : ℕ} (parent : TargetInterval n) (i : Fin M)
    (B : ℕ) (hn : Nat.size n ≤ B) (hm : Nat.size M ≤ B) :
    (sourceChildWithWork parent i).2 ≤ 2200 * (B + 3) ^ 2 := by
  have hlo := (Nat.size_le_size (parent.ordered.trans parent.valid)).trans hn
  have hhi := (Nat.size_le_size parent.valid).trans hn
  have hi := (Nat.size_le_size i.isLt.le).trans hm
  let width := saturatingSubtractWithWork parent.hi parent.lo
  let next := binaryNaturalAddWithWork i.val 1
  have hwidth : Nat.size (bitWordValue width.1) ≤ B := by
    rw [saturatingSubtractWithWork_value]
    exact (Nat.size_le_size (Nat.sub_le _ _)).trans hhi
  have hnext : Nat.size (bitWordValue next.1) ≤ B + 2 := by
    rw [binaryNaturalAddWithWork_value]
    have h := binaryNaturalAdd_size_le i.val 1
    simp only [Nat.size_one] at h
    have hMpos : 1 ≤ Nat.size M := Nat.size_pos.mpr (Nat.zero_lt_of_lt i.isLt)
    omega
  have hleft := balancedCutWithWork_cost parent.lo (bitWordValue width.1) M i.val (B + 2)
    (Nat.zero_lt_of_lt i.isLt) (by omega) (by omega) (by omega) (by omega)
  have hright := balancedCutWithWork_cost parent.lo (bitWordValue width.1) M
    (bitWordValue next.1) (B + 2) (Nat.zero_lt_of_lt i.isLt)
    (by omega) (by omega) (by omega) hnext
  have hsub := saturatingSubtractWithWork_cost parent.hi parent.lo
  have hadd := binaryNaturalAddWithWork_cost i.val 1
  change width.2 + next.2 + _ + _ + 4 ≤ _
  change width.2 ≤ _ at hsub
  change next.2 ≤ _ at hadd
  simp only [Nat.size_one] at hadd
  nlinarith only [hleft, hright, hsub, hadd, hlo, hhi, hi, Nat.zero_le B]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryWideChildWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
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

theorem gridStateBoxBitBudget_mono_count (k l B : ℕ) (h : k ≤ l) :
    gridStateBoxBitBudget k B ≤ gridStateBoxBitBudget l B := by
  unfold gridStateBoxBitBudget gridPointsBitBudget
  gcongr

theorem wideChildGridWithWork_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P B : ℕ) (i : Fin M) (hPpos : 0 < P)
    (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (hM : Nat.size M ≤ B) (hb : Nat.size b ≤ B) (hP : Nat.size P ≤ B) :
    (wideChildGridWithWork parent r b P i).2 ≤ wideChildGridBitBudget P B := by
  let child := sourceChildWithWork parent i
  let spacing := seedGridSpacingWithWork b P
  let radius := binaryNaturalMulWithWork 10 b
  let leftOffset := saturatingSubtractWithWork child.1.lo parent.lo
  let rightOffset := saturatingSubtractWithWork child.1.hi parent.lo
  let left := binaryNaturalAddWithWork r.lo (bitWordValue leftOffset.1)
  let right := binaryNaturalAddWithWork r.lo (bitWordValue rightOffset.1)
  have hparent : Nat.size parent.lo ≤ B :=
    (Nat.size_le_size (parent.ordered.trans parent.valid)).trans hnx
  have hcl : Nat.size child.1.lo ≤ B :=
    (Nat.size_le_size (child.1.ordered.trans child.1.valid)).trans hnx
  have hch : Nat.size child.1.hi ≤ B := (Nat.size_le_size child.1.valid).trans hnx
  have hrlo : Nat.size r.lo ≤ B := (Nat.size_le_size (r.ordered.trans r.valid)).trans hny
  have hlo : Nat.size (bitWordValue leftOffset.1) ≤ B := by
    rw [saturatingSubtractWithWork_value]
    exact (Nat.size_le_size (Nat.sub_le _ _)).trans hcl
  have hro : Nat.size (bitWordValue rightOffset.1) ≤ B := by
    rw [saturatingSubtractWithWork_value]
    exact (Nat.size_le_size (Nat.sub_le _ _)).trans hch
  have hleft : Nat.size (bitWordValue left.1) ≤ B + 2 := by
    rw [binaryNaturalAddWithWork_value]
    exact (binaryNaturalAdd_size_le _ _).trans (by omega)
  have hright : Nat.size (bitWordValue right.1) ≤ B + 2 := by
    rw [binaryNaturalAddWithWork_value]
    exact (binaryNaturalAdd_size_le _ _).trans (by omega)
  have hspacing := seedGridSpacingWithWork_bounds b P B hb hP
  have hspacingCost : spacing.2 ≤ 100 * (B + 2) ^ 2 := hspacing.2
  have hgs : Nat.size (bitWordValue spacing.1) ≤ B + 1 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length spacing.1)).trans hspacing.1
  have hrl := bitMulWithWork_length (10 : ℕ).bits b.bits
  change radius.1.length ≤ _ at hrl
  simp only [Nat.size_eq_bits_len] at hrl
  have hten : Nat.size 10 = 4 := by decide
  rw [hten] at hrl
  have hrs : Nat.size (bitWordValue radius.1) ≤ B + 9 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length radius.1)).trans (by omega)
  have hg := seedGridSpacingWithWork_pos b P hPpos
  have hgrid := gridStateBoxWithWork_cost ny (bitWordValue spacing.1) (bitWordValue radius.1)
    (bitWordValue left.1) (bitWordValue right.1) (B + 12) hg
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have hcount : 2 * bitWordValue radius.1 / bitWordValue spacing.1 + 2 ≤ 40 * P + 2 := by
    rw [binaryNaturalMulWithWork_value, seedGridSpacingWithWork_value b P hPpos]
    simpa only [show 2 * (10 * b) = 20 * b by omega] using seedGridSpacing_radius_count b P hPpos
  have hgrid' := hgrid.trans (gridStateBoxBitBudget_mono_count _ _ (B + 12) hcount)
  have hc := sourceChildWithWork_cost parent i B hnx hM
  have hrad := binaryNaturalMulWithWork_cost 10 b
  have hol := saturatingSubtractWithWork_cost child.1.lo parent.lo
  have hor := saturatingSubtractWithWork_cost child.1.hi parent.lo
  have hal := binaryNaturalAddWithWork_cost r.lo (bitWordValue leftOffset.1)
  have har := binaryNaturalAddWithWork_cost r.lo (bitWordValue rightOffset.1)
  change child.2 ≤ _ at hc
  change radius.2 ≤ _ at hrad
  change leftOffset.2 ≤ _ at hol
  change rightOffset.2 ≤ _ at hor
  change left.2 ≤ _ at hal
  change right.2 ≤ _ at har
  rw [hten] at hrad
  change child.2 + spacing.2 + radius.2 + leftOffset.2 + rightOffset.2 + left.2 + right.2 + _ + 8 ≤ _
  unfold wideChildGridBitBudget
  nlinarith only [hc, hspacingCost, hrad, hol, hor, hal, har, hgrid', hcl, hch, hparent,
    hrlo, hlo, hro, hb, Nat.zero_le B]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalGuardWork
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_InitialInputBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local initial cone uses a bounded number of preceding-seed
queries on every clamped seed, independently of an accuracy event. -/

namespace EditApproximation

theorem localTargetStates_length_from_scale {n : ℕ} (P b radius C : ℕ)
    (q : TargetInterval n) (hP : 0 < P) (hradius : radius ≤ C * b) :
    (localTargetStates n (seedGridSpacing b P) radius q).length ≤ (4 * C * P + 2) ^ 2 := by
  have hg : 0 < seedGridSpacing b P := by unfold seedGridSpacing; omega
  have hcover : b ≤ 2 * P * seedGridSpacing b P := by
    have hquot : b / P ≤ seedGridSpacing b P := le_max_right _ _
    have hdiv := Nat.lt_mul_div_succ b hP
    nlinarith only [hquot, hdiv, hg]
  have hprod : 2 * radius ≤ 4 * C * P * seedGridSpacing b P := by
    nlinarith only [hradius, Nat.mul_le_mul_left (2 * C) hcover]
  have hcount : 2 * radius / seedGridSpacing b P ≤ 4 * C * P := by
    have hdivision := Nat.div_mul_le_self (2 * radius) (seedGridSpacing b P)
    nlinarith only [hdivision, hprod, hg]
  exact (localTargetStates_length_le hg q).trans
    (Nat.pow_le_pow_left (Nat.add_le_add_right hcount 2) 2)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalRepresentativeWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalUniformLaw_probability
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

private theorem query_grid_count (P b radius F : ℕ) (hP : 0 < P)
    (hr : radius ≤ 16 * F * b) :
    2 * radius / seedGridSpacing b P + 2 ≤ 64 * F * P + 2 := by
  have hg : 0 < seedGridSpacing b P := by unfold seedGridSpacing; omega
  have hq : b / P ≤ seedGridSpacing b P := le_max_right _ _
  have hdiv := Nat.lt_mul_div_succ b hP
  have hb : b ≤ 2 * P * seedGridSpacing b P := by nlinarith only [hq, hdiv, hg]
  have hnum : 2 * radius ≤ 64 * F * P * seedGridSpacing b P := by
    nlinarith only [hr, Nat.mul_le_mul_left (32 * F) hb]
  have hfloor := Nat.div_mul_le_self (2 * radius) (seedGridSpacing b P)
  nlinarith only [hfloor, hnum, hg]

theorem localRepresentativesWithWork_cost {n : ℕ} (N P F B : ℕ) (a : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction) (query : TargetInterval n)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hFpos : 1 ≤ F) (hPbits : Nat.size P ≤ B) (hP : 0 < P) (hn : Nat.size n ≤ B)
    (ha : a.width ≤ B) (hi : ∀ r, (initial r).width ≤ B) :
    (localRepresentativesWithWork N P F a initial query).2 ≤ localRepresentativesBitBudget P F B := by
  let scales := queryExponentsWithWork N F a (initial query)
  let radius := naturalCeilingWithWork (initial query)
  let C := B + 4
  let L := 64 * F * P + 2
  have hscales := queryExponentsWithWork_bounds N F B a (initial query) hB hN hF ha (hi query)
  have hradius : Nat.size (bitWordValue radius.1) ≤ B + 2 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length radius.1)).trans
      ((naturalCeilingWithWork_length (initial query)).trans (by have hh := hi query; omega))
  have hradiusCost := (naturalCeilingWithWork_cost (initial query)).trans
    (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (Nat.add_le_add_right (hi query) 1) 2))
  let callback := fun e =>
    let b := 2 ^ e
    let spacing := seedGridSpacingWithWork b P
    let points := gridStateBoxWithWork n (bitWordValue spacing.1) (bitWordValue radius.1) query.lo query.hi
    let selected := filterWithWork (fun r => centerEligibilityWithWork b F a (initial r)) points.1
    let labeled := arithmeticMapWithWork (fun r => ((b, r), 1)) selected.1
    (labeled.1, spacing.2 + points.2 + selected.2 + labeled.2 + e + 5)
  have hcallback (e : ℕ) (he : e ∈ scales.1) :
      (callback e).2 ≤ localRepresentativeScaleBitBudget P F B ∧ (callback e).1.length ≤ L ^ 2 := by
    have hmem := he
    change e ∈ (queryExponentsWithWork N F a (initial query)).1 at hmem
    simp only [queryExponentsWithWork, filterWithWork_value] at hmem
    obtain ⟨heRange, heGuard⟩ := List.mem_filter.mp hmem
    have heBound : e ≤ B := by
      have he' := List.mem_range.mp heRange
      rw [Nat.size_eq_bits_len] at he'
      omega
    have hb : Nat.size (2 ^ e) + 2 ≤ C := by rw [Nat.size_pow]; dsimp only [C]; omega
    have hspacing := seedGridSpacingWithWork_bounds (2 ^ e) P C (by omega) (by dsimp only [C]; omega)
    have hgs : 0 < bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1 := by
      rw [seedGridSpacingWithWork_value _ _ hP]
      unfold seedGridSpacing
      omega
    have hgsBits : Nat.size (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1) ≤ C := by
      rw [seedGridSpacingWithWork_value _ _ hP]
      have hdiv : Nat.size ((2 ^ e) / P) ≤ Nat.size (2 ^ e) := Nat.size_le_size (Nat.div_le_self _ _)
      rw [seedGridSpacing]
      rw [Nat.size_pow] at hdiv
      have hmax : max 1 ((2 ^ e) / P) = 1 ∨ max 1 ((2 ^ e) / P) = (2 ^ e) / P := max_choice _ _
      rcases hmax with hh | hh
      · rw [hh, Nat.size_one]
        dsimp only [C]
        omega
      · rw [hh]
        dsimp only [C]
        omega
    have hw := (refinementScaleGuardWithWork_value F (2 ^ e) a (initial query)).mp heGuard
    have hceil : bitWordValue radius.1 ≤ 16 * F * 2 ^ e := by
      rw [naturalCeilingWithWork_value]
      apply Nat.ceil_le.mpr
      have hden : (0 : ℚ) < 16 * F := by
        have hpositive : (0 : ℚ) < F := by exact_mod_cast (show 0 < F by omega)
        positivity
      have hh := (div_le_iff₀ hden).mp hw.1
      calc
        _ ≤ ((2 ^ e : ℕ) : ℚ) * (16 * (F : ℚ)) := hh
        _ = ((16 * F * 2 ^ e : ℕ) : ℚ) := by push_cast <;> ring
    have hcount : 2 * bitWordValue radius.1 /
        bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1 + 2 ≤ L := by
      rw [seedGridSpacingWithWork_value _ _ hP]
      exact query_grid_count P (2 ^ e) _ F hP hceil
    let points := gridStateBoxWithWork n (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
      (bitWordValue radius.1) query.lo query.hi
    have hpCost := (gridStateBoxWithWork_cost n _ _ query.lo query.hi C hgs
      (by dsimp only [C]; omega) hgsBits (by dsimp only [C]; omega)
      ((Nat.size_le_size (query.ordered.trans query.valid)).trans (by dsimp only [C]; omega))
      ((Nat.size_le_size query.valid).trans (by dsimp only [C]; omega))).trans
      (gridStateBoxBitBudget_mono_count _ _ C hcount)
    have hpLen : points.1.length ≤ L ^ 2 := by
      rw [gridStateBoxWithWork_value _ _ _ _ _ hgs]
      exact (localTargetStates_length_le hgs query).trans (Nat.pow_le_pow_left hcount 2)
    have hfilt := filterWithWork_cost
      (fun r => centerEligibilityWithWork (2 ^ e) F a (initial r)) points.1
      (localEligibilityBitBudget C) (fun r _ => centerEligibilityWithWork_cost (2 ^ e) F C a (initial r)
        (by dsimp only [C]; omega) hb (by dsimp only [C]; omega) (by dsimp only [C]; omega)
        ((hi r).trans (by dsimp only [C]; omega)))
    have hselected : (filterWithWork
        (fun r => centerEligibilityWithWork (2 ^ e) F a (initial r)) points.1).1.length ≤ L ^ 2 := by
      rw [filterWithWork_value]
      exact (List.length_filter_le _ _).trans hpLen
    have hlabel := arithmeticMapWithWork_cost (fun r : TargetInterval n => ((2 ^ e, r), 1))
      (filterWithWork (fun r => centerEligibilityWithWork (2 ^ e) F a (initial r)) points.1).1 1
      (fun _ _ => le_rfl)
    have hfilt' := hfilt.trans (Nat.mul_le_mul_right _ hpLen)
    have hlabel' := hlabel.trans (Nat.mul_le_mul_right _ hselected)
    constructor
    · change (seedGridSpacingWithWork (2 ^ e) P).2 + points.2 +
        (filterWithWork (fun r => centerEligibilityWithWork (2 ^ e) F a (initial r)) points.1).2 +
        (arithmeticMapWithWork (fun r => ((2 ^ e, r), 1))
          (filterWithWork (fun r => centerEligibilityWithWork (2 ^ e) F a (initial r)) points.1).1).2 + e + 5 ≤ _
      have hpc : points.2 ≤ gridStateBoxBitBudget L C := hpCost
      unfold localRepresentativeScaleBitBudget
      change _ ≤ 100 * (C + 2) ^ 2 + gridStateBoxBitBudget L C +
        L ^ 2 * (localEligibilityBitBudget C + 3) + L ^ 2 * 4 + B + 6
      omega
    · simpa only [callback, arithmeticMapWithWork_value, List.length_map] using hselected
  have hflat := arithmeticFlatMapWithWork_cost callback scales.1
    (localRepresentativeScaleBitBudget P F B) (L ^ 2)
    (fun e he => (hcallback e he).1) (fun e he => (hcallback e he).2)
  have hflat' := hflat.trans (Nat.mul_le_mul_right _ hscales.2)
  change scales.2 + radius.2 + (arithmeticFlatMapWithWork callback scales.1).2 + 3 ≤ _
  unfold localRepresentativesBitBudget
  have hsc : scales.2 ≤ queryExponentsBitBudget B := hscales.1
  change radius.2 ≤ _ at hradiusCost
  dsimp only [L] at hflat'
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedListBounds
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalUniformLaw_probability
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

theorem localRepresentativesWithWork_length_le {n : ℕ} (N P F B : ℕ) (hP : 0 < P)
    (hF : 1 ≤ F) (a : BinaryFraction) (initial : TargetInterval n → BinaryFraction)
    (query : TargetInterval n) (hN : Nat.size N ≤ B) :
    (localRepresentativesWithWork N P F a initial query).1.length ≤
      (B + 1) * (64 * F * P + 2) ^ 2 := by
  rw [localRepresentativesWithWork_value N P F hP]
  unfold localRefinementRepresentatives
  apply (list_flatMap_length_le _ _ _ ?_).trans
    (Nat.mul_le_mul_right _ ((List.length_filter_le _ _).trans (show
      (dyadicScales N).length ≤ B + 1 by rw [dyadicScales_length_bits, Nat.size_eq_bits_len]; omega)))
  intro b hb
  have hwindow := of_decide_eq_true (List.mem_filter.mp hb).2
  have hFp : (0 : ℚ) < 16 * F := by
    have : (0 : ℚ) < F := by exact_mod_cast (show 0 < F by omega)
    positivity
  have hr : ⌈(initial query).value⌉₊ ≤ (16 * F) * b := by
    apply Nat.ceil_le.mpr
    have hh := (div_le_iff₀ hFp).mp hwindow.1
    push_cast
    nlinarith only [hh]
  simp only [List.length_map]
  exact (List.length_filter_le _ _).trans (by
    simpa only [show 4 * (16 * F) * P = 64 * F * P by ring] using
      localTargetStates_length_from_scale P b ⌈(initial query).value⌉₊ (16 * F) query hP hr)

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRepresentativeReads
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalUniformLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Query-local representative construction reads its finite initial
table explicitly. Each center lookup is charged before testing it. -/

namespace EditApproximation
namespace BinaryFraction



theorem representativeScaleReadWithWork_eq_cost {n : ℕ} (P F : ℕ) (a : BinaryFraction)
    (read : TargetInterval n → BinaryFraction × ℕ) (radius : List Bool)
    (query : TargetInterval n) (e R : ℕ) (hR : ∀ r, (read r).2 ≤ R) :
    (representativeScaleReadWithWork P F a read radius query e).1 =
      (representativeScalePlainWithWork P F a (fun r => (read r).1) radius query e).1 ∧
    (representativeScaleReadWithWork P F a read radius query e).2 ≤
      (representativeScalePlainWithWork P F a (fun r => (read r).1) radius query e).2 * (R + 1) := by
  let spacing := seedGridSpacingWithWork (2 ^ e) P
  let points := gridStateBoxWithWork n (bitWordValue spacing.1) (bitWordValue radius) query.lo query.hi
  have h := filterWithWork_add_read (fun r => centerEligibilityWithWork (2 ^ e) F a (read r).1)
    (fun r => (read r).2) points.1 R (fun r _ => hR r)
  constructor
  · simp only [representativeScaleReadWithWork, representativeScalePlainWithWork, spacing, points, h.1]
  · unfold representativeScaleReadWithWork representativeScalePlainWithWork
    change spacing.2 + points.2 + _ + _ + e + 5 ≤ (spacing.2 + points.2 + _ + _ + e + 5) * _
    rw [h.1]
    nlinarith only [h.2]



theorem localRepresentativeReadWithWork_eq_cost {n : ℕ} (N P F : ℕ) (a : BinaryFraction)
    (read : TargetInterval n → BinaryFraction × ℕ) (query : TargetInterval n)
    (R : ℕ) (hR : ∀ r, (read r).2 ≤ R) :
    (localRepresentativeReadWithWork N P F a read query).1 =
      (localRepresentativesWithWork N P F a (fun r => (read r).1) query).1 ∧
    (localRepresentativeReadWithWork N P F a read query).2 ≤
      (localRepresentativesWithWork N P F a (fun r => (read r).1) query).2 * (R + 2) := by
  let scales := queryExponentsWithWork N F a (read query).1
  let radius := naturalCeilingWithWork (read query).1
  let plain := representativeScalePlainWithWork P F a (fun r => (read r).1) radius.1 query
  let withRead := representativeScaleReadWithWork P F a read radius.1 query
  have h := arithmeticFlatMapWithWork_factor withRead plain scales.1 (R + 1) (by omega)
    (fun e _ => (representativeScaleReadWithWork_eq_cost P F a read radius.1 query e R hR).1)
    (fun e _ => (representativeScaleReadWithWork_eq_cost P F a read radius.1 query e R hR).2)
  have hquery := hR query
  constructor
  · exact h.1
  · change (read query).2 + scales.2 + radius.2 +
      (arithmeticFlatMapWithWork withRead scales.1).2 + 3 ≤
      (scales.2 + radius.2 + (arithmeticFlatMapWithWork plain scales.1).2 + 3) * (R + 2)
    nlinarith only [h.2, hquery]

theorem localRepresentativeReadWithWork_cost {n : ℕ} (N P F B R : ℕ) (a : BinaryFraction)
    (read : TargetInterval n → BinaryFraction × ℕ) (query : TargetInterval n)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hFpos : 1 ≤ F) (hPbits : Nat.size P ≤ B) (hP : 0 < P) (hn : Nat.size n ≤ B)
    (ha : a.width ≤ B) (hi : ∀ r, (read r).1.width ≤ B) (hR : ∀ r, (read r).2 ≤ R) :
    (localRepresentativeReadWithWork N P F a read query).2 ≤
      localRepresentativesBitBudget P F B * (R + 2) :=
  (localRepresentativeReadWithWork_eq_cost N P F a read query R hR).2.trans
    (Nat.mul_le_mul_right _
      (localRepresentativesWithWork_cost N P F B a (fun r => (read r).1) query
        hB hN hF hFpos hPbits hP hn ha hi))

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryListWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! First-occurrence duplicate removal for the literal adaptive query lists.
The equality tests, accumulated list, and final reversal are charged. -/

namespace EditApproximation





theorem queryEraseLoopWithWork_cost {α : Type*} (equal : α → α → Bool × ℕ)
    (C : ℕ) (hC : ∀ a b, (equal a b).2 ≤ C) (xs seen : List α) :
    (queryEraseLoopWithWork equal xs seen).2 ≤
      (xs.length + 1) * (xs.length + seen.length + 1) * (C + 4) := by
  induction xs generalizing seen with
  | nil =>
    simp only [queryEraseLoopWithWork, List.length_nil, zero_add, one_mul]
    nlinarith
  | cons a xs ih =>
    have hm := memberByWithWork_cost equal C hC a seen
    have hs : (if (memberByWithWork equal a seen).1 then seen else a :: seen).length ≤
        seen.length + 1 := by
      split
      · omega
      · simp only [List.length_cons]; omega
    have hi := ih (if (memberByWithWork equal a seen).1 then seen else a :: seen)
    have hh : (queryEraseLoopWithWork equal xs
        (if (memberByWithWork equal a seen).1 then seen else a :: seen)).2 ≤
        (xs.length + 1) * (xs.length + (seen.length + 1) + 1) * (C + 4) :=
      hi.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))
    change (memberByWithWork equal a seen).2 + _ + 2 ≤ _
    simp only [List.length_cons]
    nlinarith only [hm, hh, Nat.zero_le xs.length, Nat.zero_le seen.length, Nat.zero_le C]

theorem queryEraseWithWork_cost {α : Type*} (equal : α → α → Bool × ℕ)
    (C : ℕ) (hC : ∀ a b, (equal a b).2 ≤ C) (xs : List α) :
    (queryEraseWithWork equal xs).2 ≤ (xs.length + 1) ^ 2 * (C + 4) := by
  simpa only [queryEraseWithWork, List.length_nil, Nat.add_zero, pow_two] using
    queryEraseLoopWithWork_cost equal C hC xs []



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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryOrderBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic work bounds for actual duplicate removal and encoded sorting.
The bound counts comparisons and list allocation, including duplicates. -/

namespace EditApproximation

theorem queryEraseLoopWithWork_length {α : Type*} (equal : α → α → Bool × ℕ)
    (xs seen : List α) :
    (queryEraseLoopWithWork equal xs seen).1.length ≤ xs.length + seen.length := by
  induction xs generalizing seen with
  | nil => simp only [queryEraseLoopWithWork, List.length_reverse, List.length_nil, Nat.zero_add, le_refl]
  | cons a xs ih =>
    change (queryEraseLoopWithWork equal xs
      (if (memberByWithWork equal a seen).1 then seen else a :: seen)).1.length ≤ _
    split_ifs
    · exact (ih seen).trans (by simp only [List.length_cons]; omega)
    · exact (ih (a :: seen)).trans (by simp only [List.length_cons]; omega)

theorem queryEraseWithWork_length {α : Type*} (equal : α → α → Bool × ℕ) (xs : List α) :
    (queryEraseWithWork equal xs).1.length ≤ xs.length := by
  simpa only [queryEraseWithWork, List.length_nil, Nat.add_zero] using
    queryEraseLoopWithWork_length equal xs []

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryScalarDispatch
attribute [-instance] _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The physical scalar sources locate a dyadic scale by a counted scan.
The scan computes the original first index and works also for absent scales. -/

namespace EditApproximation



theorem dyadicScales_size_bound (N b : ℕ) (hb : b ∈ dyadicScales N) :
    Nat.size b ≤ Nat.size N + 1 := by
  rw [← dyadicScalesWithWork_value N] at hb
  simp only [dyadicScalesWithWork, arithmeticMapWithWork_value, List.mem_map] at hb
  obtain ⟨e, he, rfl⟩ := hb
  rw [powerTwoWord_value, Nat.size_pow]
  have he' := List.mem_range.mp he
  rw [Nat.size_eq_bits_len] at he'
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryWideBounds
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band-buffer input construction has a polynomial counter in the
number of representatives, emitted child-grid cells and key width. -/

namespace EditApproximation.BinaryFraction

section Wide
variable {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx) (P : ℕ)
  (representatives : List (ℕ × TargetInterval ny)) (G C B : ℕ)
  (hM : Nat.size M ≤ B) (hny : Nat.size ny ≤ B)
  (hgrid : ∀ br ∈ representatives, ∀ i : Fin M,
    (wideChildGridWithWork parent br.2 br.1 P i).1.length ≤ G)
  (hwork : ∀ br ∈ representatives, ∀ i : Fin M,
    (wideChildGridWithWork parent br.2 br.1 P i).2 ≤ C)

include hM hny hgrid hwork in
theorem queryWideInputsWithWork_bounds :
    (queryWideInputsWithWork M parent P representatives).1.length ≤ representatives.length * (M * G) ∧
    (queryWideInputsWithWork M parent P representatives).2 ≤
      representatives.length * (M * (C + 4 * G + 1 + G + 3) + M * G + 3) +
      (representatives.length * (M * G) + 1) ^ 2 * (24 * B + 12) + M + 2 := by
  let childRun := fun (br : ℕ × TargetInterval ny) (i : Fin M) =>
    let states := wideChildGridWithWork parent br.2 br.1 P i
    let labeled := arithmeticMapWithWork (fun r => ((i, r), 1)) states.1
    (labeled.1, states.2 + labeled.2 + 1)
  let run := fun br : ℕ × TargetInterval ny => arithmeticFlatMapWithWork (childRun br) (List.finRange M)
  let raw := arithmeticFlatMapWithWork run representatives
  have child (br : ℕ × TargetInterval ny) (hbr : br ∈ representatives) (i : Fin M) :
      (childRun br i).1.length ≤ G ∧ (childRun br i).2 ≤ C + 4 * G + 1 := by
    have hl := hgrid br hbr i
    have hw := hwork br hbr i
    have hc := arithmeticMapWithWork_cost (fun r => ((i, r), 1))
      (wideChildGridWithWork parent br.2 br.1 P i).1 1 (fun _ _ => le_rfl)
    constructor
    · simpa only [childRun, arithmeticMapWithWork_value, List.length_map] using hl
    · change (wideChildGridWithWork parent br.2 br.1 P i).2 +
        (arithmeticMapWithWork (fun r => ((i, r), 1))
          (wideChildGridWithWork parent br.2 br.1 P i).1).2 + 1 ≤ _
      simp only [Nat.reduceAdd] at hc
      have hh := hc.trans (Nat.mul_le_mul_right 4 hl)
      omega
  have one (br : ℕ × TargetInterval ny) (hbr : br ∈ representatives) :
      (run br).1.length ≤ M * G ∧ (run br).2 ≤ M * (C + 4 * G + 1 + G + 3) := by
    have hl := arithmeticFlatMapWithWork_length (childRun br) (List.finRange M) G
      (fun i _ => (child br hbr i).1)
    have hw := arithmeticFlatMapWithWork_cost (childRun br) (List.finRange M) (C + 4 * G + 1) G
      (fun i _ => (child br hbr i).2) (fun i _ => (child br hbr i).1)
    simpa only [List.length_finRange] using And.intro hl hw
  have hl : raw.1.length ≤ representatives.length * (M * G) :=
    arithmeticFlatMapWithWork_length run representatives (M * G) (fun br hb => (one br hb).1)
  have hw : raw.2 ≤ representatives.length * (M * (C + 4 * G + 1 + G + 3) + M * G + 3) :=
    arithmeticFlatMapWithWork_cost run representatives (M * (C + 4 * G + 1 + G + 3)) (M * G)
      (fun br hb => (one br hb).2) (fun br hb => (one br hb).1)
  have he := queryEraseWithWork_cost coordinateEqualWithWork (24 * B + 8)
    (fun a b => coordinateEqualWithWork_cost a b B hM hny) raw.1
  have hsq : (raw.1.length + 1) ^ 2 ≤ (representatives.length * (M * G) + 1) ^ 2 := by gcongr
  have he' := he.trans (Nat.mul_le_mul_right (24 * B + 8 + 4) hsq)
  simp only [Nat.add_assoc, Nat.reduceAdd] at he'
  have hu := (queryEraseWithWork_length coordinateEqualWithWork raw.1).trans hl
  refine ⟨hu, ?_⟩
  change raw.2 + (queryEraseWithWork coordinateEqualWithWork raw.1).2 + M + 2 ≤ _
  omega

end Wide
end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryBandInputCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

theorem queryWideInputsWithWork_dyadic_bounds {nx ny : ℕ}
    (M N P count B : ℕ) (parent : TargetInterval nx) (hP : 0 < P)
    (representatives : List (ℕ × TargetInterval ny))
    (hl : representatives.length ≤ count)
    (hs : ∀ br ∈ representatives, br.1 ∈ dyadicScales N)
    (hN : Nat.size N ≤ B) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (hM : Nat.size M ≤ B) (hPb : Nat.size P ≤ B) :
    (queryWideInputsWithWork M parent P representatives).1.length ≤ count * (M * (40 * P + 2) ^ 2) ∧
    (queryWideInputsWithWork M parent P representatives).2 ≤ queryWideInputsBitBudget M P count B := by
  have hb := queryWideInputsWithWork_bounds M parent P representatives ((40 * P + 2) ^ 2)
    (wideChildGridBitBudget P (B + 1)) B hM hny
    (fun br _ i => by rw [wideChildGridWithWork_value _ _ _ _ _ hP]; exact wideChildStateList_length_le parent br.2 hP i)
    (fun br hbr i => wideChildGridWithWork_cost parent br.2 br.1 P (B + 1) i hP
      (by omega) (by omega) (by omega)
      ((dyadicScales_size_bound N br.1 (hs br hbr)).trans (by omega)) (by omega))
  constructor
  · exact hb.1.trans (Nat.mul_le_mul_right _ hl)
  · apply hb.2.trans
    unfold queryWideInputsBitBudget
    dsimp only
    gcongr

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryWarmupProgramCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

theorem queryWarmupInputsWithWork_bounds_oai {nx ny : ℕ} (M N P F B I : ℕ)
    (parent : TargetInterval nx) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (q : TargetInterval ny)
    (hB : 8 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hPb : Nat.size P ≤ B) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (hM : Nat.size M ≤ B) (ha : a.width ≤ B)
    (hi : ∀ r, (initial r).1.width ≤ B) (hI : ∀ r, (initial r).2 ≤ I) :
    (queryWarmupInputsWithWork M parent N P F a initial q).1.length ≤
      queryWarmupRepresentatives P F B * (M * (40 * P + 2) ^ 2) ∧
    (queryWarmupInputsWithWork M parent N P F a initial q).2 ≤
      queryWarmupInputsBitBudget M P F B I := by
  let reps := localRepresentativeReadWithWork N P F a initial q
  have heq := (localRepresentativeReadWithWork_eq_cost N P F a initial q I hI).1
  have hlen : reps.1.length ≤ queryWarmupRepresentatives P F B := by
    rw [show reps.1 = _ from heq]
    exact localRepresentativesWithWork_length_le N P F B hP hFpos a _ q hN
  have hscale : ∀ br ∈ reps.1, br.1 ∈ dyadicScales N := by
    intro br hb
    rw [show reps.1 = _ from heq, localRepresentativesWithWork_value N P F hP] at hb
    exact (representativeList_conditions a.value (fun r => (initial r).1.value)
      (localRefinementRepresentatives_subset N P F a.value (fun r => (initial r).1.value) q br hb)).1
  have hw := queryWideInputsWithWork_dyadic_bounds M N P (queryWarmupRepresentatives P F B) B
    parent hP reps.1 hlen hscale hN hnx hny hM hPb
  have hr := localRepresentativeReadWithWork_cost N P F B I a initial q (by omega)
    hN hF hFpos hPb hP hny ha hi hI
  exact ⟨hw.1, Nat.add_le_add_right (Nat.add_le_add hr hw.2) 1⟩

end EditApproximation.BinaryFraction

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.BinaryFraction.queryWarmupInputsWithWork_bounds_oai := @OAI.EditApproximation.BinaryFraction.queryWarmupInputsWithWork_bounds_oai
