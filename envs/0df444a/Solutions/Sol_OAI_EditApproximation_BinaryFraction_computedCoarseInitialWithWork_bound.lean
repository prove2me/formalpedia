-- Prove2me | solution 1 for OAI.EditApproximation.BinaryFraction.computedCoarseInitialWithWork_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:26:51.394145+00:00
-- url     : https://prove2.me/submissions/4d5dadf2-f880-475d-9691-8e98d47f1e06

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Nat
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea000
import Definitions.Def_OAIQ361V3Ea001
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_computedCoarseRoot_for_candidate

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

theorem natural_sum_bit_length (a b : ℕ) :
    Nat.size (a + b) ≤ Nat.size a + Nat.size b + 1 := by
  apply Nat.size_le.mpr
  have ha : a < 2 ^ (Nat.size a + Nat.size b) :=
    (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hb : b < 2 ^ (Nat.size a + Nat.size b) :=
    (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [pow_succ]
  omega

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

theorem add_den_bits (a b : UnreducedRational) :
    Nat.size (a.add b).den ≤ Nat.size a.den + Nat.size b.den :=
  natural_product_bit_length _ _

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











theorem addWithWork_cost (a b : SignedBinary) :
    (a.addWithWork b).2 ≤ 20 * (a.bits.length + b.bits.length + 1) := by
  have hadd := bitAddWithWork_cost a.bits b.bits false
  have hcompare := bitCompareWithWork_cost a.bits b.bits
  have hsub1 := bitSubtractWithWork_cost a.bits b.bits false
  have hsub2 := bitSubtractWithWork_cost b.bits a.bits false
  unfold addWithWork
  split_ifs
  · change (bitAddWithWork a.bits b.bits false).2 + 4 ≤ _
    omega
  · dsimp only
    cases (bitCompareWithWork a.bits b.bits).1 <;> simp only [] <;> omega

theorem mulWithWork_cost (a b : SignedBinary) :
    (a.mulWithWork b).2 ≤ 24 * (a.bits.length + b.bits.length + 1) ^ 2 := by
  have hmul := bitMulWithWork_cost a.bits b.bits
  change (bitMulWithWork a.bits b.bits).2 + 4 ≤ _
  nlinarith only [hmul]

theorem addWithWork_length (a b : SignedBinary) :
    (a.addWithWork b).1.bits.length ≤ max a.bits.length b.bits.length + 1 := by
  have hadd := bitAddWithWork_length a.bits b.bits false
  have hsub1 := bitSubtractWithWork_length a.bits b.bits false
  have hsub2 := bitSubtractWithWork_length b.bits a.bits false
  unfold addWithWork
  split_ifs
  · exact hadd
  · dsimp only
    cases (bitCompareWithWork a.bits b.bits).1 <;> simp only [List.length_nil] <;> omega

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





theorem addWithWork_cost (a b : BinaryFraction) (B : ℕ) (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (a.addWithWork b).2 ≤ 5000 * (B + 1) ^ 2 := by
  have han : a.numerator.bits.length ≤ B := (le_max_left _ _).trans ha
  have had : a.denominator.length ≤ B := (le_max_right _ _).trans ha
  have hbn : b.numerator.bits.length ≤ B := (le_max_left _ _).trans hb
  have hbd : b.denominator.length ≤ B := (le_max_right _ _).trans hb
  have hfirst := SignedBinary.mulWithWork_cost a.numerator b.denominatorInteger
  have hsecond := SignedBinary.mulWithWork_cost b.numerator a.denominatorInteger
  have hfl := SignedBinary.mulWithWork_length a.numerator b.denominatorInteger
  have hsl := SignedBinary.mulWithWork_length b.numerator a.denominatorInteger
  have hsum := SignedBinary.addWithWork_cost (a.numerator.mulWithWork b.denominatorInteger).1
    (b.numerator.mulWithWork a.denominatorInteger).1
  have hden := bitMulWithWork_cost a.denominator b.denominator
  simp only [denominatorInteger] at hfirst hsecond hfl hsl
  change (a.numerator.mulWithWork b.denominatorInteger).2 +
    (b.numerator.mulWithWork a.denominatorInteger).2 +
    ((a.numerator.mulWithWork b.denominatorInteger).1.addWithWork
      (b.numerator.mulWithWork a.denominatorInteger).1).2 +
    (bitMulWithWork a.denominator b.denominator).2 + 8 ≤ _
  simp only [denominatorInteger] at hsum ⊢
  nlinarith only [han, had, hbn, hbd, hfirst, hsecond, hfl, hsl, hsum, hden,
    Nat.mul_self_le_mul_self (show a.numerator.bits.length + b.denominator.length + 1 ≤ 2 * B + 1 by omega),
    Nat.mul_self_le_mul_self (show b.numerator.bits.length + a.denominator.length + 1 ≤ 2 * B + 1 by omega),
    Nat.mul_le_mul (show a.denominator.length + 1 ≤ B + 1 by omega)
      (show a.denominator.length + b.denominator.length + 1 ≤ 2 * B + 1 by omega)]

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





theorem rawAdd_width (a b : BinaryFraction) (B : ℕ) (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (a.addWithWork b).1.width ≤ 3 * B + 2 := by
  have han : a.numerator.bits.length ≤ B := (le_max_left _ _).trans ha
  have had : a.denominator.length ≤ B := (le_max_right _ _).trans ha
  have hbn : b.numerator.bits.length ≤ B := (le_max_left _ _).trans hb
  have hbd : b.denominator.length ≤ B := (le_max_right _ _).trans hb
  have hfirst := SignedBinary.mulWithWork_length a.numerator b.denominatorInteger
  have hsecond := SignedBinary.mulWithWork_length b.numerator a.denominatorInteger
  have hsum := SignedBinary.addWithWork_length (a.numerator.mulWithWork b.denominatorInteger).1
    (b.numerator.mulWithWork a.denominatorInteger).1
  have hden := bitMulWithWork_length a.denominator b.denominator
  simp only [denominatorInteger] at hfirst hsecond
  dsimp only [addWithWork, width, denominatorInteger]
  simp only [denominatorInteger] at hsum
  apply max_le <;> omega

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

theorem canonicalAddWithWork_cost (a b : BinaryFraction) (B : ℕ) (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (canonicalAddWithWork a b).2 ≤ 6000 * (B + 1) ^ 2 := by
  have hr := addWithWork_cost a b B ha hb
  have hw := rawAdd_width a b B ha hb
  have hc := canonicalizeWithWork_cost (a.addWithWork b).1
  change (a.addWithWork b).2 + (canonicalizeWithWork (a.addWithWork b).1).2 ≤ _
  nlinarith only [hr, hw, hc]

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

theorem canonicalAddWithWork_width_le_storageBits (a b : BinaryFraction) :
    (canonicalAddWithWork a b).1.width ≤
      (a.representation.add b.representation).storageBits := by
  have h := canonicalizeWithWork_width_le_storageBits (a.addWithWork b).1
  rw [addWithWork_representation] at h
  exact h

theorem canonicalMulWithWork_width_le_storageBits (a b : BinaryFraction) :
    (canonicalMulWithWork a b).1.width ≤
      (a.representation.mul b.representation).storageBits := by
  have h := canonicalizeWithWork_width_le_storageBits (a.mulWithWork b).1
  rw [mulWithWork_representation] at h
  exact h

theorem canonicalAddWithWork_self_width (a b : BinaryFraction) :
    (canonicalAddWithWork a b).1.width ≤ (canonicalAddWithWork a b).1.representation.storageBits := by
  rw [canonicalAddWithWork_representation]
  exact canonicalAddWithWork_width_le_storageBits a b

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

theorem storageBits_add (a b : UnreducedRational) :
    (a.add b).storageBits ≤ 2 * a.storageBits + 2 * b.storageBits + 2 := by
  have hnum := (Nat.size_le_size (Int.natAbs_add_le (a.num * b.den) (b.num * a.den))).trans
    (natural_sum_bit_length (a.num * b.den).natAbs (b.num * a.den).natAbs)
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hnum
  have hleft := natural_product_bit_length a.num.natAbs b.den
  have hright := natural_product_bit_length b.num.natAbs a.den
  have hden := add_den_bits a b
  dsimp only [add, storageBits] at *
  omega

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Integer-computed parameters

The logarithms and fourth roots in Section 2 are computed by natural bit
lengths and nested integer square roots. No real arithmetic oracle is
used to form the algorithm's parameters.
-/

namespace EditApproximation
















theorem inputHeight_covers_length (N : ℕ) : N + 2 ≤ 2 ^ inputHeight N := by
  have hlog := Nat.le_pow_clog (by decide : 1 < 2) (N + 2)
  have hheight := Nat.le_pow_clog (by decide : 1 < 2) (Nat.clog 2 (N + 2))
  exact hlog.trans (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hheight)

theorem inputSmallLog_bounds (N : ℕ) (hN : 0 < N) :
    heightExponent N ≤ inputSmallLog N ∧ inputSmallLog N < 2 * heightExponent N := by
  have hpos := heightExponent_pos N hN
  have hone : 1 ≤ heightExponent N := hpos
  have hrange := rejectionWord_range (heightExponent N) hpos
  simpa only [inputSmallLog, smallLogExponent, rejectionBitCount, max_eq_right hone] using hrange

theorem coarseExponent_fourth_power (ell : ℕ) :
    coarseExponent ell ^ 4 ≤ Nat.log 2 ell := by
  have ha := Nat.sqrt_le' (Nat.sqrt (Nat.log 2 ell))
  have hb := Nat.sqrt_le' (Nat.log 2 ell)
  have hsq := Nat.pow_le_pow_left ha 2
  rw [← pow_mul] at hsq
  exact hsq.trans hb

theorem coarseExponent_maximal (ell p : ℕ) (hp : p ^ 4 ≤ Nat.log 2 ell) :
    p ≤ coarseExponent ell := by
  apply Nat.le_sqrt'.2
  apply Nat.le_sqrt'.2
  simpa only [← pow_mul] using hp

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryFiniteLoops
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Executed finite filters and stored fraction reductions used by the
band tests. Callback costs and list construction are included. -/

namespace EditApproximation



namespace BinaryFraction



theorem minWithWork_width (a b : BinaryFraction) :
    (minWithWork a b).1.width ≤ max a.width b.width := by
  unfold minWithWork
  dsimp only
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem minWithWork_cost (a b : BinaryFraction) (B : ℕ) (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (minWithWork a b).2 ≤ 1000 * (B + 1) ^ 2 + 1 :=
  Nat.add_le_add_right (ltWithWork_cost a b B ha hb) 1



theorem minimumWithWork_width (fallback : BinaryFraction) (values : List BinaryFraction)
    (B : ℕ) (hf : fallback.width ≤ B) (hvalues : ∀ a ∈ values, a.width ≤ B) :
    (minimumWithWork fallback values).1.width ≤ B := by
  induction values with
  | nil => exact hf
  | cons head rest ih =>
    exact (minWithWork_width head (minimumWithWork fallback rest).1).trans
      (max_le (hvalues head List.mem_cons_self) (ih (fun a ha => hvalues a (List.mem_cons_of_mem _ ha))))

theorem minimumWithWork_cost (fallback : BinaryFraction) (values : List BinaryFraction)
    (B : ℕ) (hf : fallback.width ≤ B) (hvalues : ∀ a ∈ values, a.width ≤ B) :
    (minimumWithWork fallback values).2 ≤ 1 + values.length * (1000 * (B + 1) ^ 2 + 2) := by
  induction values with
  | nil => simp [minimumWithWork]
  | cons head rest ih =>
    have htail := ih (fun a ha => hvalues a (List.mem_cons_of_mem _ ha))
    have hw := minimumWithWork_width fallback rest B hf (fun a ha => hvalues a (List.mem_cons_of_mem _ ha))
    have hc := minWithWork_cost head (minimumWithWork fallback rest).1 B
      (hvalues head List.mem_cons_self) hw
    change (minimumWithWork fallback rest).2 + (minWithWork head (minimumWithWork fallback rest).1).2 + 1 ≤ _
    simp only [List.length_cons]
    rw [Nat.add_mul, Nat.one_mul]
    omega



end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryDistanceWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Absolute differences used in the literal prefix and band tests.
The sign update retains the magnitude words; subtraction uses signed
Boolean arithmetic. -/

namespace EditApproximation
namespace BinaryFraction



theorem canonicalAddWithWork_width (a b : BinaryFraction) (B : ℕ)
    (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (a.canonicalAddWithWork b).1.width ≤ 8 * B + 6 := by
  have hs := UnreducedRational.storageBits_add a.representation b.representation
  have ha' := representation_storageBits_le a
  have hb' := representation_storageBits_le b
  have hw := canonicalAddWithWork_self_width a b
  rw [canonicalAddWithWork_representation] at hw
  omega

end BinaryFraction
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseParameters
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Computed numerical premises of the initial seed

The literal dyadic estimator uses the input-computed branching factor,
threshold and precision. Its depth and distortion bounds follow from
those integer parameters.
-/

namespace EditApproximation





theorem computed_coarse_branching (N : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) :
    4 ≤ inputHeight N ∧ inputHeight N ≤ (integerParameters N).B := by
  have hlogs := inputSmallLog_bounds N hN
  have hexp : 2 ≤ heightExponent N := by omega
  have hH : 4 ≤ inputHeight N := by
    change 2 ^ 2 ≤ 2 ^ heightExponent N
    exact pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hexp
  have hlog : 1 ^ 4 ≤ Nat.log 2 (inputSmallLog N) := by
    apply Nat.le_log_of_pow_le (by decide : 1 < 2)
    norm_num
    omega
  have hp := coarseExponent_maximal (inputSmallLog N) 1 hlog
  have hB : inputHeight N ≤ inputHeight N ^ coarseExponent (inputSmallLog N) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by omega : 1 ≤ inputHeight N) hp
  exact ⟨hH, hB⟩

theorem computed_coarse_depth (N n : ℕ) (hN : 0 < N) (hn : n ≤ N)
    (hell : 200 ≤ inputSmallLog N) :
    n ≤ (integerParameters N).B ^ computedCoarseDepth N n ∧
      computedCoarseDepth N n ≤ inputHeight N := by
  have hB := computed_coarse_branching N hN hell
  have hBtwo : 2 ≤ (integerParameters N).B := by omega
  constructor
  · exact (le_max_right 1 n).trans (Nat.le_pow_clog hBtwo (max 1 n))
  · have hanti := Nat.clog_anti_left (by decide : 1 < 2) hBtwo (n := max 1 n)
    have hlength : max 1 n ≤ 2 ^ inputHeight N := by
      apply max_le Nat.one_le_two_pow
      exact hn.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N))
    exact hanti.trans ((Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 hlength)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_AccuracyCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A computable fixed-accuracy cutoff. The algorithm tests the small-log
conditions directly; it does not construct the double exponential bound. -/

namespace EditApproximation





theorem heightExponent_above_double_power (N exponent : ℕ) (h : 2 ^ (2 ^ exponent) ≤ N) :
    exponent ≤ heightExponent N := by
  have hfirst := Nat.clog_mono_right 2 (h.trans (Nat.le_add_right N 2))
  rw [Nat.clog_pow _ _ (by decide : 1 < (2 : ℕ))] at hfirst
  have hsecond := Nat.clog_mono_right 2 hfirst
  simpa only [Nat.clog_pow _ _ (by decide : 1 < (2 : ℕ)), heightExponent] using hsecond

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Growth of the computed parameters

These are scalar estimates for the literal integer parameters of Section 10.
They do not assert an evaluator cost: the recursive-input and charged local
work bounds must be connected to these estimates separately.
-/

namespace EditApproximation

open Filter
open scoped Topology

theorem heightExponent_tendsto : Tendsto heightExponent atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_ge_atTop (2 ^ (2 ^ b))] with N hN
  exact heightExponent_above_double_power N b hN

theorem inputSmallLog_tendsto : Tendsto inputSmallLog atTop atTop := by
  apply tendsto_atTop_mono' atTop _ heightExponent_tendsto
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (inputSmallLog_bounds N hN).1

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterLocalAsymptotics
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar bounds for the local enumeration exponent. -/

namespace EditApproximation

open Filter
open scoped Topology

/-- Every fixed polynomial in the computed small logarithm is negligible
relative to the computed height. -/
theorem smallLog_polynomial_div_height_tendsto (k : ℕ) :
    Tendsto (fun N => (inputSmallLog N : ℝ) ^ k / inputHeight N) atTop (𝓝 0) := by
  have hupper : Tendsto (fun N => (2 : ℝ) ^ k *
      ((heightExponent N : ℝ) ^ k / (2 : ℝ) ^ heightExponent N)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)).comp
        heightExponent_tendsto).const_mul ((2 : ℝ) ^ k)
  apply squeeze_zero' (Eventually.of_forall fun N =>
    div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)) _ hupper
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hbound : (inputSmallLog N : ℝ) ≤ 2 * (heightExponent N : ℝ) := by
    exact_mod_cast (inputSmallLog_bounds N hN).2.le
  have hpower := pow_le_pow_left₀ (Nat.cast_nonneg (inputSmallLog N)) hbound k
  simpa only [inputHeight, Nat.cast_pow, Nat.cast_ofNat, mul_pow, mul_div_assoc] using
    div_le_div_of_nonneg_right hpower (by positivity : (0 : ℝ) ≤ 2 ^ heightExponent N)

theorem coarseExponent_le_smallLog (N : ℕ) :
    coarseExponent (inputSmallLog N) ≤ inputSmallLog N := by
  have h := coarseExponent_fourth_power (inputSmallLog N)
  have hp : coarseExponent (inputSmallLog N) ≤ coarseExponent (inputSmallLog N) ^ 4 := by
    exact Nat.le_pow (by decide : 0 < 4)
  exact hp.trans (h.trans (Nat.log_le_self 2 _))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerPreprocessing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open Filter
open scoped Topology



/-- Scans, integer encoding, indexed occurrence preprocessing and the
exact equality guard are charged before the local evaluator starts. -/


 theorem input_length_bits_le (N : ℕ) : Nat.size (N + 2) ≤ inputHeight N + 1 := by
  apply Nat.size_le.mpr
  exact (inputHeight_covers_length N).trans_lt
    (Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self _))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarsePrecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Exact common precision of the coarse recurrence

Minima and threshold maxima select existing rationals. All computed arrays
therefore share one denominator whose bit length grows linearly with depth.
-/

namespace EditApproximation

open Finset

universe u

/-- The common-denominator representation needs only linearly many
factor bit lengths per coarse depth. -/
theorem coarseCommonDenominator_bits (allowanceDen q L B D : ℕ) :
    Nat.size (coarseCommonDenominator allowanceDen q L B D) ≤
      Nat.size allowanceDen + Nat.size q + D * (Nat.size L + Nat.size B + Nat.size q) + 1 := by
  have hfirst := natural_product_bit_length allowanceDen q
  have hbase := natural_product_bit_length L B
  have hbaseSecond := natural_product_bit_length (L * B) q
  have hpower := natural_power_bit_length (L * B * q) D
  have htotal := natural_product_bit_length (allowanceDen * q) ((L * B * q) ^ D)
  unfold coarseCommonDenominator
  nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseGlobalSeed
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Simultaneous seed failure with the computed parameters

The count includes every dyadic guess, complete coarse-tree node and shift.
Independent finite entry streams realize the actual full table law.
Symbolic recursion indices carry exact equalities to the computed parameters.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

theorem twice_square_le_two_pow (r : ℕ) (hr : 8 ≤ r) : 2 * r ^ 2 ≤ 2 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
    rw [pow_succ 2 r]
    nlinarith

theorem computed_coarse_B_upper (N : ℕ) (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) :
    (integerParameters N).B ≤ 2 ^ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hr : 8 ≤ heightExponent N := by omega
  have hp : coarseExponent (inputSmallLog N) ≤ 2 * heightExponent N := by
    have hsqrt := (Nat.sqrt_le_self (Nat.sqrt (Nat.log 2 (inputSmallLog N)))).trans
      (Nat.sqrt_le_self (Nat.log 2 (inputSmallLog N)))
    exact hsqrt.trans ((Nat.log_le_self _ _).trans (by omega))
  have hpoly := twice_square_le_two_pow (heightExponent N) hr
  have hexponent : heightExponent N * coarseExponent (inputSmallLog N) ≤ inputHeight N := by
    have hmul := Nat.mul_le_mul_left (heightExponent N) hp
    change _ ≤ 2 ^ heightExponent N
    nlinarith
  change (2 ^ heightExponent N) ^ coarseExponent (inputSmallLog N) ≤ 2 ^ inputHeight N
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hexponent

theorem computed_coarse_height_large (N : ℕ) (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) :
    256 ≤ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hr : 8 ≤ heightExponent N := by omega
  change 2 ^ 8 ≤ 2 ^ heightExponent N
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hr

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseLevelMagnitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

 theorem coarseLevelMagnitude_ge (N k B d : ℕ) : k ≤ coarseLevelMagnitude N k B d := by
  have hp : 1 ≤ (2 * B + 2) ^ (d + 1) := by
    have hz : 0 < (2 * B + 2) ^ (d + 1) := by positivity
    omega
  unfold coarseLevelMagnitude
  nlinarith

 theorem coarseLevelMagnitude_bits (N k B d : ℕ) :
    Nat.size (coarseLevelMagnitude N k B d) ≤
      Nat.size (N + k + 1) + (d + 1) * Nat.size (2 * B + 2) + 1 := by
  have hm := natural_product_bit_length (N + k + 1) ((2 * B + 2) ^ (d + 1))
  have hp := natural_power_bit_length (2 * B + 2) (d + 1)
  unfold coarseLevelMagnitude
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseBitParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

 theorem coarseBitParameters_grid (H N k B q L d : ℕ)
    (hH : 100 ≤ H) (hd : d ≤ H)
    (hN : Nat.size N ≤ 2 * H) (hk : Nat.size k ≤ 2 * H)
    (hB : Nat.size B ≤ 2 * H) (hq : Nat.size q ≤ 2 * H) (hL : Nat.size L ≤ 2 * H) :
    Nat.size (coarseCommonDenominator 1 q L B d) ≤ 10 * H ^ 2 ∧
    Nat.size (coarseLevelMagnitude N k B d + 2) + 2 * (10 * H ^ 2) + 1 ≤ H ^ 3 := by
  have hsum : Nat.size L + Nat.size B + Nat.size q ≤ 6 * H := by omega
  have hcoeff := Nat.mul_le_mul hd hsum
  have hden := coarseCommonDenominator_bits 1 q L B d
  rw [Nat.size_one] at hden
  have hbaseprod := natural_product_bit_length 2 B
  have hbasesum := natural_sum_bit_length (2 * B) 2
  rw [show Nat.size 2 = 2 by decide] at hbaseprod hbasesum
  have hbase : Nat.size (2 * B + 2) ≤ 2 * H + 5 := by omega
  have hsumNk := natural_sum_bit_length N k
  have hsumone := natural_sum_bit_length (N + k) 1
  rw [Nat.size_one] at hsumone
  have hnk : Nat.size (N + k + 1) ≤ 4 * H + 3 := by omega
  have hmag := coarseLevelMagnitude_bits N k B d
  have hmag2 := natural_sum_bit_length (coarseLevelMagnitude N k B d) 2
  rw [show Nat.size 2 = 2 by decide] at hmag2
  have hprod := Nat.mul_le_mul (show d + 1 ≤ H + 1 by omega) hbase
  have hsq : H ≤ H ^ 2 := Nat.le_pow (by decide)
  have hcube : 100 * H ^ 2 ≤ H ^ 3 := by
    have hh := Nat.mul_le_mul_right (H ^ 2) hH
    nlinarith only [hh]
  constructor
  · nlinarith only [hden, hq, hcoeff, hH, hsq]
  · nlinarith only [hmag, hmag2, hnk, hprod, hsq, hcube, hH]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseInitialExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
namespace BinaryFraction



 theorem naturalListEqualWithWork_value (x y : List ℕ) :
    (naturalListEqualWithWork x y).1 = true ↔ x = y := by
  induction x generalizing y with
  | nil => cases y <;> simp [naturalListEqualWithWork]
  | cons a left ih =>
    cases y with
    | nil => simp [naturalListEqualWithWork]
    | cons b right =>
      simp only [naturalListEqualWithWork]
      by_cases hab : a = b
      · rw [ite_eq_left ((naturalEqualWithWork_value a b).mpr hab), ih]
        simp only [List.cons.injEq, hab, true_and]
      · have ht : ¬ (naturalEqualWithWork a b).1 = true :=
          fun h => hab ((naturalEqualWithWork_value a b).mp h)
        simp only [ite_eq_right ht, Bool.false_eq_true, List.cons.injEq, hab, false_and]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseInitialWorkBounds
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

 theorem arithmeticMapWithWork_total {α β : Type*} (f : α → β × ℕ) (values : List α) :
    (arithmeticMapWithWork f values).2 = (values.map (fun a => (f a).2)).sum + 3 * values.length := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
    simp only [arithmeticMapWithWork, List.map_cons, List.sum_cons, List.length_cons, ih]
    omega

namespace BinaryFraction

 theorem coarseMinimumWithWork_bounds (values : List BinaryFraction) (A : ℕ)
    (hA : 2 ≤ A) (hv : ∀ a ∈ values, a.width ≤ A) :
    (coarseMinimumWithWork values).1.width ≤ A ∧
      (coarseMinimumWithWork values).2 ≤ 1 + values.length * (1000 * (A + 1) ^ 2 + 2) := by
  cases values with
  | nil =>
    constructor
    · exact (nat_width_le 0).trans (by simpa using hA)
    · simp only [coarseMinimumWithWork, List.length_nil, zero_mul, add_zero, le_refl]
  | cons a rest =>
    have ha := hv a List.mem_cons_self
    have hr := fun b hb => hv b (List.mem_cons_of_mem _ hb)
    exact ⟨minimumWithWork_width a rest A ha hr,
      (minimumWithWork_cost a rest A ha hr).trans (by simp only [List.length_cons] <;> nlinarith)⟩

 theorem naturalListEqualWithWork_cost (x y : List ℕ) (S : ℕ)
    (hs : ∀ a ∈ x ++ y, Nat.size a ≤ S) :
    (naturalListEqualWithWork x y).2 ≤ (x.length + y.length + 1) * (8 * S + 4) := by
  induction x generalizing y with
  | nil => cases y <;> simp only [naturalListEqualWithWork] <;> nlinarith [Nat.zero_le S]
  | cons a left ih =>
    cases y with
    | nil => simp only [naturalListEqualWithWork] <;> nlinarith [Nat.zero_le S]
    | cons b right =>
      have ha : Nat.size a ≤ S := hs a (by simp)
      have hb : Nat.size b ≤ S := hs b (by simp)
      have ht := naturalEqualWithWork_cost a b S ha hb
      have hr := ih right (by
        intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact hs z (List.mem_append.mpr (Or.inl (List.mem_cons_of_mem _ hz)))
        · exact hs z (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hz))))
      simp only [naturalListEqualWithWork]
      split_ifs <;> dsimp only
      · simp only [List.length_cons] at *
        nlinarith only [ht, hr, Nat.zero_le S]
      · simp only [List.length_cons]
        nlinarith only [ht, Nat.zero_le S, Nat.zero_le left.length, Nat.zero_le right.length]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseInitialCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- The dyadic wrapper adds only comparisons, a scan, ceiling, and clamp
beyond the sum of the actually executed candidate counters. -/
theorem coarseInitialWithWork_cost {B d : ℕ} (q L N A S : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d)
    (hA : 2 ≤ A) (hN : Nat.size N ≤ A)
    (hx : Nat.size x.length ≤ A) (hy : Nat.size y.length ≤ A)
    (hs : ∀ a ∈ x ++ y, Nat.size a ≤ S)
    (hc : ∀ i, (coarseCandidateWithWork q L hB hq hL x y i (draws i)).1.width ≤ A) :
    (coarseInitialWithWork q L N hB hq hL x y draws).2 ≤
      ((List.finRange (Nat.clog 2 (coarseEntryWidth x y) + 1)).map
        (fun i => (coarseCandidateWithWork q L hB hq hL x y i (draws i)).2)).sum +
      (x.length + y.length + 1) * (8 * S + 4) +
      10000 * (Nat.clog 2 (coarseEntryWidth x y) + 2) * (A + 2) ^ 2 := by
  let f := fun i => coarseCandidateWithWork q L hB hq hL x y i (draws i)
  let indices := List.finRange (Nat.clog 2 (coarseEntryWidth x y) + 1)
  let roots := arithmeticMapWithWork f indices
  have hl := binaryNaturalCompareWithWork_cost (2 * x.length) y.length
  have hxl := natural_product_bit_length 2 x.length
  rw [show Nat.size 2 = 2 by decide] at hxl
  have hlong : (binaryNaturalCompareWithWork (2 * x.length) y.length).2 ≤ 8 * A + 9 := by omega
  have hequal := naturalListEqualWithWork_cost x y S hs
  have hw : ∀ a ∈ roots.1, a.width ≤ A := by
    intro a ha
    rw [arithmeticMapWithWork_value] at ha
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    exact hc i
  have hm := coarseMinimumWithWork_bounds roots.1 A hA hw
  have hlen : roots.1.length = Nat.clog 2 (coarseEntryWidth x y) + 1 := by
    simp only [roots, arithmeticMapWithWork_value, List.length_map, indices, List.length_finRange]
  rw [hlen] at hm
  have hr := naturalCeilingWithWork_cost (coarseMinimumWithWork roots.1).1
  have hrw := naturalCeilingWithWork_length (coarseMinimumWithWork roots.1).1
  have hr' : (naturalCeilingWithWork (coarseMinimumWithWork roots.1).1).2 ≤ 500 * (A + 1) ^ 2 :=
    hr.trans (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (by omega) 2))
  have hcmp := wordLEWithWork_cost N.bits (naturalCeilingWithWork (coarseMinimumWithWork roots.1).1).1
  rw [Nat.size_eq_bits_len] at hcmp
  have hclamp : (wordMinWithWork N.bits (naturalCeilingWithWork (coarseMinimumWithWork roots.1).1).1).2 ≤
      8 * A + 11 := by
    change (wordLEWithWork _ _).2 + 1 ≤ _
    omega
  have hmap := arithmeticMapWithWork_total f indices
  change roots.2 = _ at hmap
  have hmap' : roots.2 = (indices.map (fun i => (f i).2)).sum +
      3 * (Nat.clog 2 (coarseEntryWidth x y) + 1) := by
    simpa only [indices, List.length_finRange] using hmap
  change _ ≤ (indices.map (fun i => (f i).2)).sum + _ + _
  unfold coarseInitialWithWork
  dsimp only
  split_ifs
  · dsimp only
    nlinarith only [hlong, hA, hN, hy,
      Nat.zero_le ((indices.map (fun i => (f i).2)).sum),
      Nat.zero_le ((x.length + y.length + 1) * (8 * S + 4)),
      Nat.zero_le (Nat.clog 2 (coarseEntryWidth x y))]
  · dsimp only
    nlinarith only [hlong, hequal, hA,
      Nat.zero_le ((indices.map (fun i => (f i).2)).sum),
      Nat.zero_le (Nat.clog 2 (coarseEntryWidth x y))]
  · change _ + _ + roots.2 + (coarseMinimumWithWork roots.1).2 +
      (naturalCeilingWithWork (coarseMinimumWithWork roots.1).1).2 +
      (wordMinWithWork N.bits (naturalCeilingWithWork (coarseMinimumWithWork roots.1).1).1).2 +
      Nat.size N + 6 ≤ _
    rw [hmap']
    nlinarith only [hlong, hequal, hm.2, hr', hclamp, hA, hN,
      Nat.zero_le (Nat.clog 2 (coarseEntryWidth x y))]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseInitialScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Scalar envelope used only after summing the executed dyadic roots. -/
theorem coarseInitial_aggregate_scalar (H x a g roots work : ℕ) (hH : 100 ≤ H)
    (hg : g ≤ H + 1)
    (hr : roots ≤ H ^ 32 * (a + g))
    (hw : work ≤ roots + (3 * x + 1) * (8 * H ^ 3 + 4) +
      10000 * (g + 1) * (H ^ 4 + 2) ^ 2) :
    work ≤ H ^ 36 * (a + x + 1) := by
  have hpos : 0 < H := by omega
  have hpow (i j : ℕ) (hij : i ≤ j) : H ^ i ≤ H ^ j := Nat.pow_le_pow_right hpos hij
  have hone : 1 ≤ H := by omega
  have hthree : 3 ≤ H := by omega
  have hhundred : 10000 ≤ H ^ 2 := by nlinarith
  have hgp : g + 1 ≤ H ^ 2 := by nlinarith
  have hp3 : 1 ≤ H ^ 3 := one_le_pow₀ hone
  have hp4 : H ^ 4 + 2 ≤ H ^ 5 := by
    have hh := Nat.mul_le_mul_right (H ^ 4) (show 2 ≤ H by omega)
    have h4 : 2 ≤ H ^ 4 := (show 2 ≤ H by omega).trans (by simpa only [pow_one] using hpow 1 4 (by decide))
    nlinarith only [hh, h4]
  have hwrap : 10000 * (g + 1) * (H ^ 4 + 2) ^ 2 ≤ H ^ 14 := by
    calc
      _ ≤ H ^ 2 * H ^ 2 * (H ^ 5) ^ 2 := by gcongr
      _ = _ := by ring
  have hscale : 3 * (8 * H ^ 3 + 4) ≤ H ^ 5 := by
    have hh := Nat.mul_le_mul_right (H ^ 3) (show 36 ≤ H ^ 2 by nlinarith)
    nlinarith only [hh, hp3]
  have hscan : (3 * x + 1) * (8 * H ^ 3 + 4) ≤ (x + 1) * H ^ 5 := by
    calc
      _ ≤ (x + 1) * (3 * (8 * H ^ 3 + 4)) := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_left _ hscale
  have hroot : roots ≤ H ^ 34 * (a + 1) := by
    have hga : a + g ≤ H ^ 2 * (a + 1) := by
      have ha := Nat.mul_le_mul_right a (show 1 ≤ H ^ 2 from one_le_pow₀ hone)
      nlinarith only [ha, hgp]
    calc
      roots ≤ H ^ 32 * (a + g) := hr
      _ ≤ H ^ 32 * (H ^ 2 * (a + 1)) := Nat.mul_le_mul_left _ hga
      _ = _ := by ring
  have hscan' := hscan.trans (Nat.mul_le_mul_left (x + 1) (hpow 5 34 (by decide)))
  have hwrap' := hwrap.trans (hpow 14 34 (by decide))
  have hfinal : 3 * H ^ 34 ≤ H ^ 36 := by
    have hh := Nat.mul_le_mul_left (H ^ 34) (show 3 ≤ H ^ 2 by nlinarith)
    nlinarith only [hh]
  have hfinal' := Nat.mul_le_mul_right (a + x + 1) hfinal
  nlinarith only [hw, hroot, hscan', hwrap', hfinal', Nat.zero_le a, Nat.zero_le x]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedSourceAddressBits
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual uniform source-range address fits in one logarithmic input
word eventually. The coefficient can be any fixed natural number. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem computed_sourceAddressBits_div_height_tendsto (C : ℕ) :
    Tendsto (fun N =>
      ((C * (coarseExponent (inputSmallLog N) + 1) * Nat.size (inputHeight N) + 1 : ℕ) : ℝ) /
        inputHeight N) atTop (𝓝 0) := by
  have hupper := (smallLog_polynomial_div_height_tendsto 2).const_mul (4 * (C : ℝ) + 1)
  simp only [mul_zero] at hupper
  apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _ hupper
  filter_upwards [eventually_ge_atTop 1] with N hN
  have he := (inputSmallLog_bounds N hN).1
  have hp := coarseExponent_le_smallLog N
  have hell : 1 ≤ inputSmallLog N := Nat.one_le_two_pow
  have hs : Nat.size (inputHeight N) = heightExponent N + 1 := by
    simp only [inputHeight, Nat.size_pow]
  have hsmall : (1 : ℝ) ≤ inputSmallLog N := by exact_mod_cast hell
  have hpR : (coarseExponent (inputSmallLog N) : ℝ) + 1 ≤ 2 * inputSmallLog N := by
    exact_mod_cast (show coarseExponent (inputSmallLog N) + 1 ≤ 2 * inputSmallLog N by omega)
  have hsR : (Nat.size (inputHeight N) : ℝ) ≤ 2 * inputSmallLog N := by
    exact_mod_cast (show Nat.size (inputHeight N) ≤ 2 * inputSmallLog N by omega)
  have hproduct := mul_le_mul hpR hsR (Nat.cast_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * inputSmallLog N)
  have hscaled := mul_le_mul_of_nonneg_left hproduct (Nat.cast_nonneg C : (0 : ℝ) ≤ C)
  have hnum : ((C * (coarseExponent (inputSmallLog N) + 1) * Nat.size (inputHeight N) + 1 : ℕ) : ℝ) ≤
      (4 * (C : ℝ) + 1) * (inputSmallLog N : ℝ) ^ 2 := by
    push_cast
    nlinarith only [hscaled, hsmall, sq_nonneg ((inputSmallLog N : ℝ) - 1)]
  have h := div_le_div_of_nonneg_right hnum (Nat.cast_nonneg (inputHeight N) : (0 : ℝ) ≤ inputHeight N)
  simpa only [mul_div_assoc] using h

theorem computed_sourceAddressBits_le_height (C : ℕ) :
    ∀ᶠ N in atTop,
      C * (coarseExponent (inputSmallLog N) + 1) * Nat.size (inputHeight N) + 1 ≤ inputHeight N := by
  filter_upwards [(computed_sourceAddressBits_div_height_tendsto C).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with N h
  have hH : (0 : ℝ) < inputHeight N := by
    exact_mod_cast Nat.two_pow_pos (heightExponent N)
  have hlt := (div_lt_one hH).mp h
  exact_mod_cast hlt.le

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedParameterRegisters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter

/-- A single logarithmic word accommodates every power exponent needed
by the global integer and online-mass constructors. -/
 theorem computedParameterPower_word :
    ∀ᶠ N in atTop, ∀ k : ℕ,
      k ≤ 8000 * (coarseExponent (inputSmallLog N) + 1) →
      Nat.size (inputHeight N ^ k) ≤ inputHeight N := by
  filter_upwards [computed_sourceAddressBits_le_height 8000] with N hN
  intro k hk
  exact (natural_power_bit_length _ _).trans
    ((Nat.add_le_add_right (Nat.mul_le_mul_right _ hk) 1).trans hN)

 theorem inputLength_register_word (N : ℕ) : Nat.size (N + 2) ≤ inputHeight N + 1 :=
  input_length_bits_le N

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCoarseBitParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter
namespace BinaryFraction

 theorem computedCoarse_bitParameters :
    ∀ᶠ N : ℕ in atTop, ∀ B d n k : ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N n → n ≤ N → k ≤ 2 * (N + 2) →
      Nat.size (coarseCommonDenominator 1 (inputHeight N ^ 4) (64 * inputHeight N) B d) ≤
        10 * inputHeight N ^ 2 ∧
      Nat.size (coarseLevelMagnitude N k B d + 2) + 2 * (10 * inputHeight N ^ 2) + 1 ≤ inputHeight N ^ 3 ∧
      Nat.size B + 2 ≤ inputHeight N ^ 3 ∧
      Nat.size (inputHeight N ^ 4) + 2 ≤ inputHeight N ^ 3 ∧
      Nat.size (64 * inputHeight N) + 2 ≤ inputHeight N ^ 3 ∧
      Nat.size N + 2 ≤ inputHeight N ^ 3 ∧
      10 * inputHeight N ^ 2 ≤ inputHeight N ^ 3 := by
  filter_upwards [computedParameterPower_word, eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)] with N hpower hN hell
  intro B d n k hBdef hddef hn hk
  have hH := computed_coarse_height_large N (by omega) hell
  have hD : d ≤ inputHeight N := hddef.symm ▸ (computed_coarse_depth N n (by omega) hn hell).2
  have hb : Nat.size B ≤ 2 * inputHeight N := by
    have hb' := Nat.size_le_size (computed_coarse_B_upper N (by omega) hell)
    simp only [Nat.size_pow] at hb'
    rw [hBdef]
    omega
  have hq : Nat.size (inputHeight N ^ 4) ≤ 2 * inputHeight N := by
    have h := hpower 4 (by omega)
    omega
  have hHsize : Nat.size (inputHeight N) ≤ inputHeight N :=
    Nat.size_le.mpr (Nat.lt_pow_self (by decide : 1 < (2 : ℕ)))
  have hL : Nat.size (64 * inputHeight N) ≤ 2 * inputHeight N := by
    have h := natural_product_bit_length 64 (inputHeight N)
    rw [show Nat.size 64 = 7 by decide] at h
    omega
  have hnsize : Nat.size N ≤ 2 * inputHeight N := by
    have h := (Nat.size_le_size (Nat.le_add_right N 2)).trans (inputLength_register_word N)
    omega
  have hksize : Nat.size k ≤ 2 * inputHeight N := by
    have h := (Nat.size_le_size hk).trans (natural_product_bit_length 2 (N + 2))
    have hn' := inputLength_register_word N
    rw [show Nat.size 2 = 2 by decide] at h
    omega
  have hgrid := coarseBitParameters_grid (inputHeight N) N k B (inputHeight N ^ 4)
    (64 * inputHeight N) d (by omega) hD hnsize hksize hb hq hL
  have hcube : 100 * inputHeight N ^ 2 ≤ inputHeight N ^ 3 := by
    have h := Nat.mul_le_mul_right (inputHeight N ^ 2) (show 100 ≤ inputHeight N by omega)
    nlinarith only [h]
  have hsquare : inputHeight N ≤ inputHeight N ^ 2 := Nat.le_pow (by decide)
  exact ⟨hgrid.1, hgrid.2, by nlinarith only [hb, hcube, hsquare, hH],
    by nlinarith only [hq, hcube, hsquare, hH], by nlinarith only [hL, hcube, hsquare, hH],
    by nlinarith only [hnsize, hcube, hsquare, hH], by nlinarith only [hcube]⟩

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCoarseCandidateWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter
namespace BinaryFraction

theorem coarseGuess_le (n : ℕ) (i : CoarseGuessIndex n) : coarseGuess n i ≤ 2 * (n + 1) := by
  have hi : i.val ≤ Nat.clog 2 n := by omega
  have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hi
  by_cases hn : n = 0
  · subst n
    simp only [Nat.clog_zero_right, pow_zero] at hp
    exact hp.trans (by decide)
  · have hr := (rejectionWord_range n (by omega)).2
    unfold rejectionBitCount at hr
    exact hp.trans (by omega)

private theorem coarseCandidate_scalar (H a root add mul size : ℕ) (hH : 100 ≤ H)
    (hr : root ≤ H ^ 30 * (2 * a + 1))
    (ha : add ≤ 6000 * (H ^ 3 + 1) ^ 2)
    (hm : mul ≤ 2000 * (8 * H ^ 3 + 7) ^ 2) (hs : size ≤ H ^ 3) :
    root + add + mul + size + 3 ≤ H ^ 32 * (a + 1) := by
  have ht : 1 ≤ H ^ 3 := one_le_pow₀ (by omega)
  have hb : add + mul + size + 3 ≤ 1000000 * H ^ 6 := by
    nlinarith only [ha, hm, hs, ht]
  have hc : 1000000 ≤ H ^ 4 := by
    have h := Nat.pow_le_pow_left hH 4
    norm_num at h
    omega
  have hbig : 1000000 * H ^ 6 ≤ H ^ 10 := by
    calc
      _ ≤ H ^ 4 * H ^ 6 := Nat.mul_le_mul_right _ hc
      _ = _ := by rw [← pow_add]
  have hexp : H ^ 10 ≤ H ^ 30 := Nat.pow_le_pow_right (by omega) (by omega)
  have htwo : 2 * H ^ 30 ≤ H ^ 32 := by
    have hh : 2 ≤ H ^ 2 := by nlinarith
    have hz := Nat.mul_le_mul_left (H ^ 30) hh
    simpa only [← pow_add, Nat.mul_comm] using hz
  nlinarith only [hr, hb, hbig, hexp, Nat.mul_le_mul_right (a + 1) htwo]

private theorem coarseCandidate_k_bits (N k B d : ℕ)
    (hb : Nat.size (coarseLevelMagnitude N k B d + 2) +
      2 * (10 * inputHeight N ^ 2) + 1 ≤ inputHeight N ^ 3) :
    Nat.size k + 2 ≤ inputHeight N ^ 3 := by
  have h := Nat.size_le_size (coarseLevelMagnitude_ge N k B d)
  have h' := Nat.size_le_size (show coarseLevelMagnitude N k B d ≤
    coarseLevelMagnitude N k B d + 2 by omega)
  have hh : 0 < inputHeight N := Nat.two_pow_pos _
  have hdpos : 0 < 10 * inputHeight N ^ 2 := by positivity
  omega

/-- Every executed dyadic candidate has a short binary value and its complete
arithmetic cost is bounded by a fixed height power times its active-array work. -/
theorem computedCoarseCandidate_bounds :
    ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N → ∀ (hB : 0 < B) (hq : 0 < inputHeight N ^ 4)
      (hL : 0 < 64 * inputHeight N)
      (i : CoarseGuessIndex (coarseEntryWidth x y)) (draws : CoarseThresholdDraws B d),
      (coarseCandidateWithWork (inputHeight N ^ 4) (64 * inputHeight N) hB hq hL x y i draws).1.width ≤
        inputHeight N ^ 4 ∧
      (coarseCandidateWithWork (inputHeight N ^ 4) (64 * inputHeight N) hB hq hL x y i draws).2 ≤
        inputHeight N ^ 32 * (coarseActiveArrayWork (coarseGuess (coarseEntryWidth x y) i)
          (initialThresholdQ N) (initialLambda N) (coarseEntryTree B d x y) draws
          (coarseGuess (coarseEntryWidth x y) i) + 1) := by
  filter_upwards [computedCoarseRoot_for_candidate, computedCoarse_bitParameters,
    eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)] with N hroot hbits hN hell
  intro B d x y hBdef hddef hsize hB hq hL i draws
  let H := inputHeight N
  let k := coarseGuess (coarseEntryWidth x y) i
  let root := coarseRootWithWork k (H ^ 4) (64 * H) hB hq hL
    (coarseTargetFrame k (coarsePadTo (coarseEntryWidth x y) y))
    (coarseEntryTree B d x y) draws 0 (coarseRootShift k)
  have hH : 100 ≤ H := (by decide : 100 ≤ 256).trans
    (computed_coarse_height_large N (by omega) hell)
  obtain ⟨hrw, hrc'⟩ := hroot B d x y hBdef hddef hsize hB hq hL i draws
  change root.1.width ≤ H ^ 3 at hrw
  change root.2 ≤ H ^ 30 * (2 * coarseActiveArrayWork k
    (initialThresholdQ N) (initialLambda N) (coarseEntryTree B d x y) draws k + 1) at hrc'
  have hk : k ≤ 2 * (N + 2) := (coarseGuess_le _ i).trans (by omega)
  have hbound := (hbits B d (coarseEntryWidth x y) k hBdef hddef hsize hk).2.1
  have hkw : Nat.size k + 2 ≤ H ^ 3 := coarseCandidate_k_bits N k B d hbound
  have hnw : (nat k).width ≤ H ^ 3 := (nat_width_le k).trans hkw
  have hsw := canonicalAddWithWork_width root.1 (nat k) (H ^ 3) hrw hnw
  have hsc := canonicalAddWithWork_cost root.1 (nat k) (H ^ 3) hrw hnw
  have htw : (nat 2).width ≤ 8 * H ^ 3 + 6 := (nat_width_le 2).trans (by rw [show Nat.size 2 = 2 by decide]; omega)
  have hmw := canonicalMulWithWork_width (nat 2) (canonicalAddWithWork root.1 (nat k)).1
    (8 * H ^ 3 + 6) htw hsw
  have hmc := canonicalMulWithWork_cost (nat 2) (canonicalAddWithWork root.1 (nat k)).1
    (8 * H ^ 3 + 6) htw hsw
  constructor
  · change (canonicalMulWithWork (nat 2) (canonicalAddWithWork root.1 (nat k)).1).1.width ≤ H ^ 4
    have hh := Nat.mul_le_mul_right (H ^ 3) hH
    have ht : 1 ≤ H ^ 3 := one_le_pow₀ (by omega)
    nlinarith only [hmw, hh, ht]
  · change root.2 + (canonicalAddWithWork root.1 (nat k)).2 +
      (canonicalMulWithWork (nat 2) (canonicalAddWithWork root.1 (nat k)).1).2 + Nat.size k + 3 ≤ _
    exact coarseCandidate_scalar H _ _ _ _ _ hH hrc' hsc hmc (by omega)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCoarseInitialWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter
namespace BinaryFraction

/-- All actual initial-estimator branches have the same source-width charging
form. In the long-target branch no target scan or root is executed. -/
theorem computedCoarseInitialWithWork_bound_oai :
    ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N →
      (∀ a ∈ x ++ y, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ (hB : 0 < B) (hq : 0 < inputHeight N ^ 4) (hL : 0 < 64 * inputHeight N)
      (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d),
      (coarseInitialWithWork (inputHeight N ^ 4) (64 * inputHeight N) N hB hq hL x y draws).2 ≤
        inputHeight N ^ 36 * (coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N)
          x y draws + x.length + 1) := by
  filter_upwards [computedCoarseCandidate_bounds, eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)] with N hcandidate hN hell
  intro B d x y hBdef hddef hsize hsymbols hB hq hL draws
  let H := inputHeight N
  change (coarseInitialWithWork (H ^ 4) (64 * H) N hB hq hL x y draws).2 ≤
    H ^ 36 * (coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N) x y draws + x.length + 1)
  have hH : 100 ≤ H := (by decide : 100 ≤ 256).trans
    (computed_coarse_height_large N (by omega) hell)
  have hlength : Nat.size N ≤ H + 1 :=
    (Nat.size_le_size (Nat.le_add_right N 2)).trans (inputLength_register_word N)
  have hxlen : x.length ≤ N := (le_max_left _ _).trans hsize
  have hylen : y.length ≤ N := (le_max_right _ _).trans hsize
  have hx : Nat.size x.length ≤ H + 1 := (Nat.size_le_size hxlen).trans hlength
  have hy : Nat.size y.length ≤ H + 1 := (Nat.size_le_size hylen).trans hlength
  have hlongcost : (binaryNaturalCompareWithWork (2 * x.length) y.length).2 ≤ 8 * H + 17 := by
    have hc := binaryNaturalCompareWithWork_cost (2 * x.length) y.length
    have hp := natural_product_bit_length 2 x.length
    rw [show Nat.size 2 = 2 by decide] at hp
    omega
  have hpow36 : 100 * H ^ 3 ≤ H ^ 36 := by
    have hh := Nat.mul_le_mul_right (H ^ 3) hH
    have hp := Nat.pow_le_pow_right (by omega : 0 < H) (by decide : 4 ≤ 36)
    nlinarith only [hh, hp]
  have hH3 : H ≤ H ^ 3 := Nat.le_pow (by decide)
  have hmul := Nat.mul_le_mul_left (H ^ 36)
    (show 1 ≤ coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N) x y draws +
      x.length + 1 by omega)
  by_cases hlong : 2 * x.length < y.length
  · have hb := (binaryNaturalCompareWithWork_lt (2 * x.length) y.length).mpr hlong
    change (coarseInitialWithWork _ _ _ _ _ _ _ _ _).2 ≤ _
    simp only [coarseInitialWithWork, hb, ite_true, if_true]
    nlinarith only [hlongcost, hlength, hy, hH, hpow36, hmul, hH3]
  have hb : ¬ (binaryNaturalCompareWithWork (2 * x.length) y.length).1 = Ordering.lt :=
    fun h => hlong ((binaryNaturalCompareWithWork_lt _ _).mp h)
  by_cases he : x = y
  · have heq := (naturalListEqualWithWork_value x y).mpr he
    have hc := naturalListEqualWithWork_cost x y (H ^ 3) hsymbols
    have hsource : y.length = x.length := congrArg List.length he.symm
    have hf : (2 * x.length + 1) * (8 * H ^ 3 + 4) + (8 * H + 17) + 3 ≤
        H ^ 36 * (x.length + 1) := by
      have ha := Nat.mul_le_mul_right (x.length + 1) hpow36
      have h3 : 1 ≤ H ^ 3 := one_le_pow₀ (by omega)
      nlinarith only [ha, hH, h3, hH3]
    simp only [coarseInitialWithWork, ite_eq_right hb, heq, ite_true, if_true]
    rw [hsource] at hc
    have hz : coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N) x y draws = 0 := by
      simp only [coarseInitialArrayWork, ite_eq_right hlong, ite_eq_left he]
    rw [hz, zero_add]
    nlinarith only [hc, hf, hlongcost]
  have hclog : Nat.clog 2 (coarseEntryWidth x y) ≤ H :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).mpr
      (hsize.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N)))
  have hN4 : Nat.size N ≤ H ^ 4 := by
    have hp2 : H + 1 ≤ H ^ 2 := by nlinarith
    have hp : H + 1 ≤ H ^ 4 := hp2.trans
      (Nat.pow_le_pow_right (by omega : 0 < H) (by decide : 2 ≤ 4))
    exact hlength.trans hp
  have hw := coarseInitialWithWork_cost (inputHeight N ^ 4) (64 * inputHeight N) N
    (H ^ 4) (H ^ 3) hB hq hL x y draws (by
      have hp : H ≤ H ^ 4 := Nat.le_pow (by decide)
      omega) hN4
    ((Nat.size_le_size hxlen).trans hN4) ((Nat.size_le_size hylen).trans hN4) hsymbols
    (fun i => (hcandidate B d x y hBdef hddef hsize hB hq hL i (draws i)).1)
  let f := fun i : CoarseGuessIndex (coarseEntryWidth x y) =>
    (coarseCandidateWithWork (H ^ 4) (64 * H) hB hq hL x y i (draws i)).2
  have hsum : ((List.finRange (Nat.clog 2 (coarseEntryWidth x y) + 1)).map f).sum =
      ∑ i, f i := by
    rw [← List.ofFn_eq_map, List.sum_ofFn]
  have hr : ((List.finRange (Nat.clog 2 (coarseEntryWidth x y) + 1)).map f).sum ≤
      H ^ 32 * (coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N) x y draws +
        (Nat.clog 2 (coarseEntryWidth x y) + 1)) := by
    rw [hsum]
    calc
      _ ≤ ∑ i : CoarseGuessIndex (coarseEntryWidth x y), H ^ 32 *
          (coarseActiveArrayWork (coarseGuess (coarseEntryWidth x y) i)
            (initialThresholdQ N) (initialLambda N) (coarseEntryTree B d x y) (draws i)
            (coarseGuess (coarseEntryWidth x y) i) + 1) :=
        Finset.sum_le_sum (fun i _ => (hcandidate B d x y hBdef hddef hsize hB hq hL i (draws i)).2)
      _ = _ := by
        simp only [coarseInitialArrayWork, ite_eq_right hlong, ite_eq_right he,
          ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul, mul_one]
  have hscan : x.length + y.length + 1 ≤ 3 * x.length + 1 := by omega
  apply coarseInitial_aggregate_scalar H x.length _ (Nat.clog 2 (coarseEntryWidth x y) + 1)
    _ _ hH (by omega) hr
  exact hw.trans (Nat.add_le_add_right (Nat.add_le_add_left
    (Nat.mul_le_mul_right (8 * H ^ 3 + 4) hscan) _) _)

end BinaryFraction
end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.BinaryFraction.computedCoarseInitialWithWork_bound_oai := @OAI.EditApproximation.BinaryFraction.computedCoarseInitialWithWork_bound_oai
