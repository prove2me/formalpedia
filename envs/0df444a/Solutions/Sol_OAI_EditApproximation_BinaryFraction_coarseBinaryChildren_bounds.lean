-- Prove2me | solution 1 for OAI.EditApproximation.BinaryFraction.coarseBinaryChildren_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:25:19.396753+00:00
-- url     : https://prove2.me/submissions/0a439db3-4d91-45b1-a787-444cb63765cd

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_OAIQ361V3Ea000
import Definitions.Def_OAIQ361V3Ea001

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

theorem mul_den_bits (a b : UnreducedRational) :
    Nat.size (a.mul b).den ≤ Nat.size a.den + Nat.size b.den :=
  natural_product_bit_length _ _

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal Boolean construction of the child envelope of a finite band.
It scans the actual child values, compares with `b/M`, and runs the exact
bounded dyadic scan. Table reads are accounted for by the query program. -/

namespace EditApproximation
namespace BinaryFraction



theorem maxWithWork_cost (a b : BinaryFraction) (B : ℕ) (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (maxWithWork a b).2 ≤ 1000 * (B + 1) ^ 2 + 1 :=
  Nat.add_le_add_right (ltWithWork_cost a b B ha hb) 1



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



namespace BinaryFraction



theorem leWithWork_cost (a b : BinaryFraction) (B : ℕ) (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (a.leWithWork b).2 ≤ 1000 * (B + 1) ^ 2 + 1 :=
  Nat.add_le_add_right (ltWithWork_cost b a B hb ha) 1




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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryFixedDenominator
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

theorem fixedDenominatorWithWork_cost (a : BinaryFraction) (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) (A B : ℕ)
    (ha : a.width ≤ A) (hB : denominator.length ≤ B) :
    (fixedDenominatorWithWork a denominator hden).2 ≤ 5000 * (A + B + 2) ^ 2 := by
  let product := bitMulWithWork a.numerator.bits denominator
  let quotient := bitDivModWithWork a.denominator product.1
  let raw : BinaryFraction := ⟨⟨a.numerator.negative, quotient.1⟩, denominator, hden⟩
  have hn : a.numerator.bits.length ≤ A := (le_max_left _ _).trans ha
  have hd : a.denominator.length ≤ A := (le_max_right _ _).trans ha
  have hp := bitMulWithWork_cost a.numerator.bits denominator
  have hpl := bitMulWithWork_length a.numerator.bits denominator
  have hq := bitDivModWithWork_cost a.denominator product.1
  have hql := (bitDivModWithWork_lengths a.denominator product.1).1
  change product.1.length ≤ 2 * a.numerator.bits.length + denominator.length + 1 at hpl
  change quotient.1.length = product.1.length at hql
  have hraw : raw.width ≤ 2 * A + B + 1 := by
    change max quotient.1.length denominator.length ≤ _
    exact max_le (by omega) (by omega)
  have hc := canonicalizeWithWork_cost raw
  change product.2 + quotient.2.2 + (canonicalizeWithWork raw).2 + 4 ≤ _
  have hprod : product.2 ≤ 20 * (A + B + 2) ^ 2 := by
    apply hp.trans
    have h1 : a.numerator.bits.length + 1 ≤ A + B + 2 := by omega
    have h2 : a.numerator.bits.length + denominator.length + 1 ≤ A + B + 2 := by omega
    nlinarith only [Nat.mul_le_mul h1 h2]
  have hquot : quotient.2.2 ≤ 30 * (3 * (A + B + 2)) * (4 * (A + B + 2)) := by
    apply hq.trans
    have h1 : product.1.length + 1 ≤ 3 * (A + B + 2) := by omega
    have h2 : product.1.length + a.denominator.length + 1 ≤ 4 * (A + B + 2) := by omega
    nlinarith only [Nat.mul_le_mul h1 h2]
  nlinarith only [hprod, hquot, hc, hraw, Nat.zero_le A, Nat.zero_le B]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseGridArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Exact arithmetic on a shared coarse-array denominator. Addition touches
only the signed numerators and keeps the denominator, preventing denominator
growth across the child-array sums. All counters run Boolean primitives. -/

namespace EditApproximation
namespace BinaryFraction

/-- Store an integer on the common denominator by a literal bit product. -/


 theorem coarseGridNatWithWork_value (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) (n : ℕ) :
    (coarseGridNatWithWork denominator hden n).1.value = n := by
  unfold coarseGridNatWithWork
  dsimp only
  rw [← representation_value, canonicalizeWithWork_representation, representation_value]
  simp only [value, SignedBinary.value, signedMagnitude, Bool.false_eq_true, ↓reduceIte,
    bitMulWithWork_value, bitWordValue_bits]
  push_cast
  exact mul_div_cancel_right₀ _ (by exact_mod_cast hden.ne')

 theorem coarseGridNatWithWork_den (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) (n : ℕ) :
    (coarseGridNatWithWork denominator hden n).1.representation.den =
      bitWordValue denominator := by
  unfold coarseGridNatWithWork
  dsimp only
  rw [canonicalizeWithWork_representation]
  rfl

 theorem coarseGridNatWithWork_cost (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) (n B : ℕ)
    (hn : Nat.size n ≤ B) (hd : denominator.length ≤ B) :
    (coarseGridNatWithWork denominator hden n).2 ≤ 100 * (B + 1) ^ 2 := by
  have hc := bitMulWithWork_cost n.bits denominator
  have hl := bitMulWithWork_length n.bits denominator
  have hnb : n.bits.length ≤ B := by simpa only [← Nat.size_eq_bits_len] using hn
  have hw : (⟨⟨false, (bitMulWithWork n.bits denominator).1⟩, denominator,
      hden⟩ : BinaryFraction).width ≤ 3 * B + 1 := by
    change max (bitMulWithWork n.bits denominator).1.length denominator.length ≤ _
    apply max_le <;> omega
  have ht := canonicalizeWithWork_cost
    (⟨⟨false, (bitMulWithWork n.bits denominator).1⟩, denominator, hden⟩ : BinaryFraction)
  have hp : (bitMulWithWork n.bits denominator).2 ≤ 40 * (B + 1) ^ 2 := by
    apply hc.trans
    have hm := Nat.mul_le_mul (show n.bits.length + 1 ≤ B + 1 by omega)
      (show n.bits.length + denominator.length + 1 ≤ 2 * (B + 1) by omega)
    nlinarith only [hm]
  change (bitMulWithWork n.bits denominator).2 + _ + 3 ≤ _
  nlinarith only [hp, ht, hw, Nat.zero_le B]

/-- Add two stored cells after their denominators have been made identical. -/


 theorem coarseGridAddWithWork_value (a b : BinaryFraction)
    (hden : bitWordValue a.denominator = bitWordValue b.denominator) :
    (coarseGridAddWithWork a b).1.value = a.value + b.value := by
  unfold coarseGridAddWithWork
  dsimp only
  rw [← representation_value, canonicalizeWithWork_representation, representation_value]
  simp only [value, SignedBinary.addWithWork_value, Int.cast_add, ← hden]
  ring

 theorem coarseGridAddWithWork_den (a b : BinaryFraction) :
    (coarseGridAddWithWork a b).1.representation.den = a.representation.den := by
  unfold coarseGridAddWithWork
  dsimp only
  rw [canonicalizeWithWork_representation]
  rfl

 theorem coarseGridAddWithWork_cost (a b : BinaryFraction) (B : ℕ)
    (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (coarseGridAddWithWork a b).2 ≤ 100 * (B + 1) := by
  have han : a.numerator.bits.length ≤ B := (le_max_left _ _).trans ha
  have hbn : b.numerator.bits.length ≤ B := (le_max_left _ _).trans hb
  have had : a.denominator.length ≤ B := (le_max_right _ _).trans ha
  have hc := SignedBinary.addWithWork_cost a.numerator b.numerator
  have hl := SignedBinary.addWithWork_length a.numerator b.numerator
  have hw : (⟨(a.numerator.addWithWork b.numerator).1, a.denominator,
      a.denominator_pos⟩ : BinaryFraction).width ≤ B + 1 := by
    change max (a.numerator.addWithWork b.numerator).1.bits.length a.denominator.length ≤ _
    apply max_le <;> omega
  have ht := canonicalizeWithWork_cost
    (⟨(a.numerator.addWithWork b.numerator).1, a.denominator, a.denominator_pos⟩ : BinaryFraction)
  change (a.numerator.addWithWork b.numerator).2 + _ + 3 ≤ _
  omega

 theorem coarseGridAddWithWork_width (a b : BinaryFraction) (V B : ℕ)
    (hden : bitWordValue a.denominator = bitWordValue b.denominator)
    (hvalue : |a.value + b.value| ≤ V) (hbits : a.denominator.length ≤ B) :
    (coarseGridAddWithWork a b).1.width ≤ Nat.size V + 2 * B + 1 := by
  let answer := (coarseGridAddWithWork a b).1
  have hv : |answer.representation.value| ≤ V := by
    rw [representation_value]
    exact (coarseGridAddWithWork_value a b hden) ▸ hvalue
  have hd : Nat.size answer.representation.den ≤ B := by
    rw [coarseGridAddWithWork_den]
    exact (Nat.size_le.mpr (bitWordValue_lt_pow_length a.denominator)).trans hbits
  have hs := UnreducedRational.storageBits_le answer.representation V B hv hd
  have hw : answer.width ≤ answer.representation.storageBits := by
    unfold answer coarseGridAddWithWork
    dsimp only
    rw [canonicalizeWithWork_representation]
    exact canonicalizeWithWork_width_le_storageBits _
  exact hw.trans hs

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseThresholdArithmetic
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Boolean threshold arithmetic on the fixed denominator of one coarse
execution. Quotients use actual long division when compressed to that grid. -/

namespace EditApproximation
namespace BinaryFraction



 theorem coarseDivideWithWork_cost (a divisor : BinaryFraction) (B : ℕ)
    (ha : a.width ≤ B) (hd : divisor.width ≤ B) :
    (coarseDivideWithWork a divisor).2 ≤ 1000000 * (B + 1) ^ 2 := by
  have hq := divWithWork_cost a divisor B ha hd
  have hqw := divWithWork_width_uniform a divisor B ha hd
  have had : a.denominator.length ≤ B := (le_max_right _ _).trans ha
  have hc := fixedDenominatorWithWork_cost (divWithWork a divisor).1 a.denominator
    a.denominator_pos (4 * B + 4) B hqw had
  change (divWithWork a divisor).2 + _ + 2 ≤ _
  nlinarith only [hq, hc, Nat.zero_le B]

 theorem coarseContributionWithWork_cost (threshold scale a : BinaryFraction) (B : ℕ)
    (ht : threshold.width ≤ B) (hs : scale.width ≤ B) (ha : a.width ≤ B) :
    (coarseContributionWithWork threshold scale a).2 ≤ 2200 * (B + 1) ^ 2 := by
  have htest := leWithWork_cost threshold a B ht ha
  have hmax := maxWithWork_cost a scale B ha hs
  have hzero := coarseGridNatWithWork_cost a.denominator a.denominator_pos 0 B
    (by simp) ((le_max_right _ _).trans ha)
  unfold coarseContributionWithWork
  dsimp only
  split_ifs <;> nlinarith only [htest, hmax, hzero, Nat.zero_le B]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseTransforms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Linear sweeps for the coarse penalty transform

The finite minima define the semantic arrays. These sweeps compute them
with one rational addition and one comparison per scan transition.
-/

namespace EditApproximation

open Finset

theorem coarseLeftSweep_length (source : List ℚ) :
    (coarseLeftSweep source).length = source.length := by
  cases source <;> simp only [coarseLeftSweep, List.length_nil, List.length_cons, List.length_scanl]

theorem coarsePenaltyTransform_length (source : List ℚ) :
    (coarsePenaltyTransform source).length = source.length := by
  simp only [coarsePenaltyTransform, List.length_zipWith, List.length_reverse,
    coarseLeftSweep_length, min_self]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseArrayArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The coarse penalty sweep executed on shared-denominator Boolean cells.
Each transition performs a numerator addition and a rational comparison. -/

namespace EditApproximation
namespace BinaryFraction

private theorem coarseMin_den (a b : BinaryFraction)
    (hden : a.representation.den = b.representation.den) :
    (minWithWork a b).1.representation.den = a.representation.den := by
  unfold minWithWork
  dsimp only
  split_ifs
  · rfl
  · exact hden.symm

private theorem coarseMin_den_length (a b : BinaryFraction) (D : ℕ)
    (ha : a.denominator.length ≤ D) (hb : b.denominator.length ≤ D) :
    (minWithWork a b).1.denominator.length ≤ D := by
  unfold minWithWork
  dsimp only
  split_ifs <;> assumption

private theorem coarseGridAdd_den_length (a b : BinaryFraction) :
    (coarseGridAddWithWork a b).1.denominator.length ≤ a.denominator.length := by
  change (trimBitWordWithWork a.denominator).1.length ≤ a.denominator.length
  rw [trimBitWordWithWork_length]
  exact Nat.size_le.mpr (bitWordValue_lt_pow_length _)

/-- The complete left sweep, including writes and traversal. -/


 theorem coarseGridScanWithWork_value (two previous : BinaryFraction)
    (source : List BinaryFraction) (htwo : two.value = 2)
    (hp : previous.representation.den = two.representation.den)
    (hs : ∀ a ∈ source, a.representation.den = two.representation.den) :
    (coarseGridScanWithWork two previous source).1.map value =
      (source.map value).scanl (fun old a => min a (old + 2)) previous.value := by
  induction source generalizing previous with
  | nil => rfl
  | cons head rest ih =>
    have hh := hs head List.mem_cons_self
    have ha : (coarseGridAddWithWork previous two).1.representation.den = two.representation.den :=
      (coarseGridAddWithWork_den previous two).trans hp
    have hn : (minWithWork head (coarseGridAddWithWork previous two).1).1.representation.den =
        two.representation.den :=
      (coarseMin_den head _ (hh.trans ha.symm)).trans hh
    have hv := coarseGridAddWithWork_value previous two hp
    simp only [coarseGridScanWithWork, List.map_cons, List.scanl_cons]
    rw [ih _ hn (fun a ha => hs a (List.mem_cons_of_mem _ ha)), minWithWork_value, hv, htwo]

 theorem coarseGridScanWithWork_bounds (two previous : BinaryFraction)
    (source : List BinaryFraction) (V D B : ℕ) (htwo : two.value = 2)
    (htw : two.width ≤ B) (hbound : Nat.size (V + 2) + 2 * D + 1 ≤ B)
    (hp : CoarseGridCell two previous V D B)
    (hs : ∀ a ∈ source, CoarseGridCell two a V D B) :
    (∀ a ∈ (coarseGridScanWithWork two previous source).1, CoarseGridCell two a V D B) ∧
      (coarseGridScanWithWork two previous source).2 ≤
        source.length * (1200 * (B + 1) ^ 2 + 3) := by
  induction source generalizing previous with
  | nil =>
    constructor
    · simpa only [coarseGridScanWithWork, List.mem_singleton] using
        (fun a (ha : a = previous) => ha ▸ hp)
    · simp only [coarseGridScanWithWork, List.length_nil, Nat.zero_mul, le_refl]
  | cons head rest ih =>
    have hh := hs head List.mem_cons_self
    have hav : |previous.value + two.value| ≤ (V + 2 : ℕ) := by
      rw [htwo, abs_of_nonneg (by linarith only [hp.2.2.1])]
      push_cast
      linarith only [hp.2.2.2.1]
    have haw := (coarseGridAddWithWork_width previous two (V + 2) D hp.1 hav hp.2.1).trans hbound
    have had := (coarseGridAddWithWork_den previous two).trans hp.1
    have hv := coarseGridAddWithWork_value previous two hp.1
    have hn : CoarseGridCell two (minWithWork head (coarseGridAddWithWork previous two).1).1 V D B := by
      refine ⟨(coarseMin_den head _ (hh.1.trans had.symm)).trans hh.1,
        coarseMin_den_length head _ D hh.2.1
          ((coarseGridAdd_den_length previous two).trans hp.2.1), ?_, ?_, ?_⟩
      · rw [minWithWork_value, hv, htwo]
        exact le_min hh.2.2.1 (by linarith only [hp.2.2.1])
      · rw [minWithWork_value]
        exact (min_le_left _ _).trans hh.2.2.2.1
      · exact (minWithWork_width head _).trans (max_le hh.2.2.2.2 haw)
    have ht := ih _ hn (fun a ha => hs a (List.mem_cons_of_mem _ ha))
    constructor
    · intro a ha
      change a ∈ previous :: _ at ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hp
      · exact ht.1 a ha
    · have hc := coarseGridAddWithWork_cost previous two B hp.2.2.2.2 htw
      have hm := minWithWork_cost head _ B hh.2.2.2.2 haw
      change (coarseGridAddWithWork previous two).2 +
        (minWithWork head (coarseGridAddWithWork previous two).1).2 +
        (coarseGridScanWithWork two (minWithWork head (coarseGridAddWithWork previous two).1).1 rest).2 + 3 ≤ _
      rw [List.length_cons, Nat.add_mul, Nat.one_mul]
      nlinarith only [hc, hm, ht.2, Nat.zero_le B]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarsePenaltyArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
namespace BinaryFraction



 theorem coarseGridLeftWithWork_value (two : BinaryFraction) (source : List BinaryFraction)
    (htwo : two.value = 2)
    (hs : ∀ a ∈ source, a.representation.den = two.representation.den) :
    (coarseGridLeftWithWork two source).1.map value = coarseLeftSweep (source.map value) := by
  cases source with
  | nil => rfl
  | cons head rest =>
    exact coarseGridScanWithWork_value two head rest htwo (hs head List.mem_cons_self)
      (fun a ha => hs a (List.mem_cons_of_mem _ ha))

 theorem coarseGridLeftWithWork_bounds (two : BinaryFraction)
    (source : List BinaryFraction) (V D B : ℕ) (htwo : two.value = 2)
    (htw : two.width ≤ B) (hbound : Nat.size (V + 2) + 2 * D + 1 ≤ B)
    (hs : ∀ a ∈ source, CoarseGridCell two a V D B) :
    (∀ a ∈ (coarseGridLeftWithWork two source).1, CoarseGridCell two a V D B) ∧
      (coarseGridLeftWithWork two source).2 ≤ source.length * (1200 * (B + 1) ^ 2 + 3) := by
  cases source with
  | nil => simp only [coarseGridLeftWithWork, List.not_mem_nil, false_implies,
      implies_true, List.length_nil, Nat.zero_mul, le_refl, and_self]
  | cons head rest =>
    have h := coarseGridScanWithWork_bounds two head rest V D B htwo htw hbound
      (hs head List.mem_cons_self) (fun a ha => hs a (List.mem_cons_of_mem _ ha))
    refine ⟨h.1, h.2.trans ?_⟩
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega



 theorem coarseGridZipMinimumWithWork_value (left right : List BinaryFraction) :
    (coarseGridZipMinimumWithWork left right).1.map value =
      List.zipWith min (left.map value) (right.map value) := by
  induction left generalizing right with
  | nil => rfl
  | cons a left ih =>
    cases right with
    | nil => rfl
    | cons b right =>
      simp only [coarseGridZipMinimumWithWork, List.map_cons, List.zipWith_cons_cons,
        minWithWork_value, ih]

 theorem coarseGridZipMinimumWithWork_cost (left right : List BinaryFraction)
    (B : ℕ) (hl : ∀ a ∈ left, a.width ≤ B) (hr : ∀ a ∈ right, a.width ≤ B) :
    (coarseGridZipMinimumWithWork left right).2 ≤
      min left.length right.length * (1000 * (B + 1) ^ 2 + 4) := by
  induction left generalizing right with
  | nil => simp only [coarseGridZipMinimumWithWork, List.length_nil, Nat.zero_min, Nat.zero_mul, le_refl]
  | cons a left ih =>
    cases right with
    | nil => simp only [coarseGridZipMinimumWithWork, List.length_nil, Nat.min_zero, Nat.zero_mul, le_refl]
    | cons b right =>
      have hh := minWithWork_cost a b B (hl a List.mem_cons_self) (hr b List.mem_cons_self)
      have ht := ih right (fun a ha => hl a (List.mem_cons_of_mem _ ha))
        (fun b hb => hr b (List.mem_cons_of_mem _ hb))
      change (minWithWork a b).2 + (coarseGridZipMinimumWithWork left right).2 + 3 ≤ _
      simp only [List.length_cons]
      rw [show min (left.length + 1) (right.length + 1) = min left.length right.length + 1 by omega,
        Nat.add_mul, Nat.one_mul]
      omega

/-- The two sweeps and final comparison, with every list pass charged. -/


 theorem coarseGridPenaltyWithWork_value (two : BinaryFraction) (source : List BinaryFraction)
    (htwo : two.value = 2)
    (hs : ∀ a ∈ source, a.representation.den = two.representation.den) :
    (coarseGridPenaltyWithWork two source).1.map value = coarsePenaltyTransform (source.map value) := by
  have hl := coarseGridLeftWithWork_value two source htwo hs
  have hr := coarseGridLeftWithWork_value two source.reverse htwo
    (fun a ha => hs a (List.mem_reverse.mp ha))
  simp only [List.map_reverse] at hr
  simp only [coarseGridPenaltyWithWork, coarseGridZipMinimumWithWork_value,
    coarsePenaltyTransform, List.map_reverse, hl, hr]

 theorem coarseGridPenaltyWithWork_cost (two : BinaryFraction) (source : List BinaryFraction)
    (V D B : ℕ) (htwo : two.value = 2) (htw : two.width ≤ B)
    (hbound : Nat.size (V + 2) + 2 * D + 1 ≤ B)
    (hs : ∀ a ∈ source, CoarseGridCell two a V D B) :
    (coarseGridPenaltyWithWork two source).2 ≤ source.length * (3500 * (B + 1) ^ 2 + 20) := by
  have hl := coarseGridLeftWithWork_bounds two source V D B htwo htw hbound hs
  have hr := coarseGridLeftWithWork_bounds two source.reverse V D B htwo htw hbound
    (fun a ha => hs a (List.mem_reverse.mp ha))
  have hv := congrArg List.length (coarseGridLeftWithWork_value two source htwo
    (fun a ha => (hs a ha).1))
  simp only [List.length_map, coarseLeftSweep_length] at hv
  have hz := coarseGridZipMinimumWithWork_cost (coarseGridLeftWithWork two source).1
    (coarseGridLeftWithWork two source.reverse).1.reverse B
    (fun a ha => (hl.1 a ha).2.2.2.2)
    (fun a ha => (hr.1 a (List.mem_reverse.mp ha)).2.2.2.2)
  have hm : min (coarseGridLeftWithWork two source).1.length
      (coarseGridLeftWithWork two source.reverse).1.reverse.length ≤ source.length := by
    exact (min_le_left _ _).trans_eq hv
  have hz' := hz.trans (Nat.mul_le_mul_right _ hm)
  simp only [List.length_reverse] at hr
  change (coarseGridLeftWithWork two source).2 + (coarseGridLeftWithWork two source.reverse).2 +
    (coarseGridZipMinimumWithWork (coarseGridLeftWithWork two source).1
      (coarseGridLeftWithWork two source.reverse).1.reverse).2 + 3 * source.length ≤ _
  nlinarith only [hl.2, hr.2, hz', Nat.zero_le (source.length * (B + 1) ^ 2),
    Nat.zero_le source.length]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseArrayRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Binary storage operations used by the shared coarse-array recursion.
A missing array is the same zero marker as in the rational specification. -/

namespace EditApproximation
namespace BinaryFraction



 theorem coarseGridZipAddWithWork_cost (left right : List BinaryFraction)
    (B : ℕ) (hl : ∀ a ∈ left, a.width ≤ B) (hr : ∀ a ∈ right, a.width ≤ B) :
    (coarseGridZipAddWithWork left right).2 ≤
      min left.length right.length * (100 * (B + 1) + 3) := by
  induction left generalizing right with
  | nil => simp only [coarseGridZipAddWithWork, List.length_nil, Nat.zero_min, Nat.zero_mul, le_refl]
  | cons a left ih =>
    cases right with
    | nil => simp only [coarseGridZipAddWithWork, List.length_nil, Nat.min_zero, Nat.zero_mul, le_refl]
    | cons b right =>
      have hh := coarseGridAddWithWork_cost a b B (hl a List.mem_cons_self) (hr b List.mem_cons_self)
      have ht := ih right (fun a ha => hl a (List.mem_cons_of_mem _ ha))
        (fun b hb => hr b (List.mem_cons_of_mem _ hb))
      change (coarseGridAddWithWork a b).2 + (coarseGridZipAddWithWork left right).2 + 3 ≤ _
      simp only [List.length_cons]
      rw [show min (left.length + 1) (right.length + 1) = min left.length right.length + 1 by omega,
        Nat.add_mul, Nat.one_mul]
      omega





end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseCompactCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

 theorem coarseCompact_canonical (a : BinaryFraction) :
    CoarseCompact (canonicalizeWithWork a).1 := by
  change (canonicalizeWithWork a).1.width ≤ _
  rw [canonicalizeWithWork_representation]
  exact canonicalizeWithWork_width_le_storageBits a

 theorem coarseCompact_gridNat (den : List Bool) (hden : 0 < bitWordValue den) (n : ℕ) :
    CoarseCompact (coarseGridNatWithWork den hden n).1 := by
  unfold coarseGridNatWithWork
  exact coarseCompact_canonical _

 theorem coarseCompact_width (a : BinaryFraction) (V D : ℕ)
    (ha : CoarseCompact a) (hv : |a.value| ≤ V)
    (hd : Nat.size a.representation.den ≤ D) :
    a.width ≤ Nat.size V + 2 * D + 1 := by
  apply ha.trans
  exact UnreducedRational.storageBits_le a.representation V D
    (by simpa only [representation_value] using hv) hd

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseCellBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

 theorem coarseGridNatWithWork_bounds (two : BinaryFraction) (den : List Bool)
    (hden : 0 < bitWordValue den) (n V D A : ℕ)
    (hd : bitWordValue den = two.representation.den) (hdl : den.length ≤ D)
    (hn : n ≤ V) (hb : Nat.size V + 2 * D + 1 ≤ A) :
    CoarseGridCell two (coarseGridNatWithWork den hden n).1 V D A := by
  have hv := coarseGridNatWithWork_value den hden n
  have hrd := (coarseGridNatWithWork_den den hden n).trans hd
  have hdl' : (coarseGridNatWithWork den hden n).1.denominator.length ≤ D := by
    change (trimBitWordWithWork den).1.length ≤ D
    rw [trimBitWordWithWork_length]
    exact (Nat.size_le.mpr (bitWordValue_lt_pow_length den)).trans hdl
  refine ⟨hrd, hdl', ?_, ?_, ?_⟩
  · rw [hv]; positivity
  · rw [hv]; exact_mod_cast hn
  · apply (coarseCompact_width _ V D (coarseCompact_gridNat den hden n) ?_ ?_).trans hb
    · rw [hv, abs_of_nonneg (by positivity : (0 : ℚ) ≤ n)]; exact_mod_cast hn
    · rw [coarseGridNatWithWork_den]
      exact (Nat.size_le.mpr (bitWordValue_lt_pow_length den)).trans hdl

 theorem coarseGridAddWithWork_bounds (two a b : BinaryFraction) (V W D A : ℕ)
    (ha : CoarseGridCell two a V D A) (hb : CoarseGridCell two b W D A)
    (hbound : Nat.size (V + W) + 2 * D + 1 ≤ A) :
    CoarseGridCell two (coarseGridAddWithWork a b).1 (V + W) D A := by
  have hd : a.representation.den = b.representation.den := ha.1.trans hb.1.symm
  have hv := coarseGridAddWithWork_value a b hd
  have hnonneg : 0 ≤ a.value + b.value := add_nonneg ha.2.2.1 hb.2.2.1
  have hvalue : a.value + b.value ≤ ((V + W : ℕ) : ℚ) := by
    push_cast; exact add_le_add ha.2.2.2.1 hb.2.2.2.1
  refine ⟨(coarseGridAddWithWork_den a b).trans ha.1, ?_, ?_, ?_, ?_⟩
  · change (trimBitWordWithWork a.denominator).1.length ≤ D
    rw [trimBitWordWithWork_length]
    exact (Nat.size_le.mpr (bitWordValue_lt_pow_length a.denominator)).trans ha.2.1
  · rw [hv]; exact hnonneg
  · rw [hv]; exact hvalue
  · exact (coarseGridAddWithWork_width a b (V + W) D hd
      (by rw [abs_of_nonneg hnonneg]; exact hvalue) ha.2.1).trans hbound

 theorem coarseGridCell_mono (two a : BinaryFraction) (V W D A : ℕ)
    (h : CoarseGridCell two a V D A) (hle : V ≤ W) : CoarseGridCell two a W D A := by
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1.trans (by exact_mod_cast hle), h.2.2.2.2⟩

 theorem coarseGridZipMinimum_property (P : BinaryFraction → Prop)
    (left right : List BinaryFraction) (hl : ∀ a ∈ left, P a) (hr : ∀ a ∈ right, P a) :
    ∀ a ∈ (coarseGridZipMinimumWithWork left right).1, P a := by
  induction left generalizing right with
  | nil => simp only [coarseGridZipMinimumWithWork, List.not_mem_nil, false_implies, implies_true]
  | cons a left ih =>
    cases right with
    | nil => simp only [coarseGridZipMinimumWithWork, List.not_mem_nil, false_implies, implies_true]
    | cons b right =>
      intro z hz
      change z ∈ (minWithWork a b).1 :: _ at hz
      rcases List.mem_cons.mp hz with rfl | hz
      · unfold minWithWork
        dsimp only
        split_ifs
        · exact hl a List.mem_cons_self
        · exact hr b List.mem_cons_self
      · exact ih right (fun a ha => hl a (List.mem_cons_of_mem _ ha))
          (fun b hb => hr b (List.mem_cons_of_mem _ hb)) z hz

 theorem coarseGridPenaltyWithWork_bounds (two : BinaryFraction) (source : List BinaryFraction)
    (V D A : ℕ) (htwo : two.value = 2) (htw : two.width ≤ A)
    (hbound : Nat.size (V + 2) + 2 * D + 1 ≤ A)
    (hs : ∀ a ∈ source, CoarseGridCell two a V D A) :
    ∀ a ∈ (coarseGridPenaltyWithWork two source).1, CoarseGridCell two a V D A := by
  have hl := (coarseGridLeftWithWork_bounds two source V D A htwo htw hbound hs).1
  have hr := (coarseGridLeftWithWork_bounds two source.reverse V D A htwo htw hbound
    (fun a ha => hs a (List.mem_reverse.mp ha))).1
  exact coarseGridZipMinimum_property _ _ _ hl
    (fun a ha => hr a (List.mem_reverse.mp ha))

 theorem coarseContributionWithWork_bounds (two threshold scale a : BinaryFraction) (V W D A : ℕ)
    (ha : CoarseGridCell two a V D A) (hs : CoarseGridCell two scale W D A)
    (hbound : Nat.size (V + W) + 2 * D + 1 ≤ A) :
    CoarseGridCell two (coarseContributionWithWork threshold scale a).1 (V + W) D A := by
  unfold coarseContributionWithWork
  dsimp only
  split_ifs
  · unfold maxWithWork
    dsimp only
    split_ifs
    · exact coarseGridCell_mono two scale W (V + W) D A hs (by omega)
    · exact coarseGridCell_mono two a V (V + W) D A ha (by omega)
  · exact coarseGridNatWithWork_bounds two a.denominator a.denominator_pos 0 (V + W) D A
      ha.1 ha.2.1 (by omega) hbound

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseBinaryBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

 theorem coarseBinaryBox_none (two : BinaryFraction) (n V D A : ℕ) :
    CoarseBinaryBox two n V D A none := by
  intro cells h; cases h

 theorem coarseBinaryBox_mono (two : BinaryFraction) (n V W D A : ℕ)
    (array : CoarseBinaryArray) (h : CoarseBinaryBox two n V D A array) (hle : V ≤ W) :
    CoarseBinaryBox two n W D A array := by
  intro cells hc
  exact ⟨(h cells hc).1, fun a ha => coarseGridCell_mono two a V W D A ((h cells hc).2 a ha) hle⟩

 theorem coarseGridZipAddWithWork_bounds (two : BinaryFraction) (left right : List BinaryFraction)
    (V W D A : ℕ) (hl : ∀ a ∈ left, CoarseGridCell two a V D A)
    (hr : ∀ a ∈ right, CoarseGridCell two a W D A)
    (hbound : Nat.size (V + W) + 2 * D + 1 ≤ A) :
    ∀ a ∈ (coarseGridZipAddWithWork left right).1, CoarseGridCell two a (V + W) D A := by
  induction left generalizing right with
  | nil => simp only [coarseGridZipAddWithWork, List.not_mem_nil, false_implies, implies_true]
  | cons a left ih =>
    cases right with
    | nil => simp only [coarseGridZipAddWithWork, List.not_mem_nil, false_implies, implies_true]
    | cons b right =>
      intro z hz
      change z ∈ (coarseGridAddWithWork a b).1 :: _ at hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact coarseGridAddWithWork_bounds two a b V W D A (hl a List.mem_cons_self)
          (hr b List.mem_cons_self) hbound
      · exact ih right (fun a ha => hl a (List.mem_cons_of_mem _ ha))
          (fun b hb => hr b (List.mem_cons_of_mem _ hb)) z hz

 theorem coarseGridZipAddWithWork_length (left right : List BinaryFraction) :
    (coarseGridZipAddWithWork left right).1.length = min left.length right.length := by
  induction left generalizing right with
  | nil => simp only [coarseGridZipAddWithWork, List.length_nil, Nat.zero_min]
  | cons a left ih =>
    cases right with
    | nil => simp only [coarseGridZipAddWithWork, List.length_nil, Nat.min_zero]
    | cons b right =>
      change _ + 1 = min _ _
      rw [ih]
      simp only [List.length_cons]
      omega

 theorem coarseBinaryAddWithWork_box (two : BinaryFraction) (n V W D A : ℕ)
    (left right : CoarseBinaryArray) (hl : CoarseBinaryBox two n V D A left)
    (hr : CoarseBinaryBox two n W D A right)
    (hbound : Nat.size (V + W) + 2 * D + 1 ≤ A) :
    CoarseBinaryBox two n (V + W) D A (coarseBinaryAddWithWork left right).1 := by
  cases left with
  | none => exact coarseBinaryBox_mono two n W (V + W) D A right hr (by omega)
  | some left =>
    cases right with
    | none => exact coarseBinaryBox_mono two n V (V + W) D A (some left) hl (by omega)
    | some right =>
      intro cells hc
      have heq : (coarseGridZipAddWithWork left right).1 = cells := Option.some.inj hc
      rw [← heq]
      refine ⟨?_, coarseGridZipAddWithWork_bounds two left right V W D A
        (hl left rfl).2 (hr right rfl).2 hbound⟩
      rw [coarseGridZipAddWithWork_length, (hl left rfl).1, (hr right rfl).1, min_self]

 theorem coarseBinaryAddWithWork_cost (two : BinaryFraction) (n V W D A : ℕ)
    (left right : CoarseBinaryArray) (hl : CoarseBinaryBox two n V D A left)
    (hr : CoarseBinaryBox two n W D A right) :
    (coarseBinaryAddWithWork left right).2 ≤ n * (100 * (A + 1) + 3) := by
  cases left with
  | none => change 0 ≤ _; omega
  | some left =>
    cases right with
    | none => change 0 ≤ _; omega
    | some right =>
      have h := coarseGridZipAddWithWork_cost left right A
        (fun a ha => ((hl left rfl).2 a ha).2.2.2.2)
        (fun b hb => ((hr right rfl).2 b hb).2.2.2.2)
      simpa only [coarseBinaryAddWithWork, (hl left rfl).1, (hr right rfl).1, min_self] using h

 theorem coarseBinaryPenaltyWithWork_box (two : BinaryFraction) (n V D A : ℕ)
    (array : CoarseBinaryArray) (h : CoarseBinaryBox two n V D A array)
    (htwo : two.value = 2) (htw : two.width ≤ A)
    (hbound : Nat.size (V + 2) + 2 * D + 1 ≤ A) :
    CoarseBinaryBox two n V D A (coarseBinaryPenaltyWithWork two array).1 := by
  cases array with
  | none => exact coarseBinaryBox_none two n V D A
  | some source =>
    intro cells hc
    have heq : (coarseGridPenaltyWithWork two source).1 = cells := Option.some.inj hc
    rw [← heq]
    refine ⟨?_, coarseGridPenaltyWithWork_bounds two source V D A htwo htw hbound (h source rfl).2⟩
    have hv := congrArg List.length (coarseGridPenaltyWithWork_value two source htwo
      (fun a ha => ((h source rfl).2 a ha).1))
    simpa only [List.length_map, coarsePenaltyTransform_length, (h source rfl).1] using hv

 theorem coarseBinaryPenaltyWithWork_cost (two : BinaryFraction) (n V D A : ℕ)
    (array : CoarseBinaryArray) (h : CoarseBinaryBox two n V D A array)
    (htwo : two.value = 2) (htw : two.width ≤ A)
    (hbound : Nat.size (V + 2) + 2 * D + 1 ≤ A) :
    (coarseBinaryPenaltyWithWork two array).2 ≤ n * (3500 * (A + 1) ^ 2 + 20) := by
  cases array with
  | none => change 0 ≤ _; omega
  | some source =>
    have hc := coarseGridPenaltyWithWork_cost two source V D A htwo htw hbound (h source rfl).2
    simpa only [coarseBinaryPenaltyWithWork, (h source rfl).1] using hc

 theorem coarseBinaryMapWithWork_box (two : BinaryFraction) (n V W D A : ℕ)
    (f : BinaryFraction → BinaryFraction × ℕ) (array : CoarseBinaryArray)
    (h : CoarseBinaryBox two n V D A array)
    (hf : ∀ a, CoarseGridCell two a V D A → CoarseGridCell two (f a).1 W D A) :
    CoarseBinaryBox two n W D A (coarseBinaryMapWithWork f array).1 := by
  cases array with
  | none => exact coarseBinaryBox_none two n W D A
  | some source =>
    intro cells hc
    have heq : (arithmeticMapWithWork f source).1 = cells := Option.some.inj hc
    rw [← heq, arithmeticMapWithWork_value]
    refine ⟨?_, ?_⟩
    · simpa only [List.length_map] using (h source rfl).1
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact hf b ((h source rfl).2 b hb)

 theorem coarseBinaryMapWithWork_cost (two : BinaryFraction) (n V D A C : ℕ)
    (f : BinaryFraction → BinaryFraction × ℕ) (array : CoarseBinaryArray)
    (h : CoarseBinaryBox two n V D A array)
    (hf : ∀ a, CoarseGridCell two a V D A → (f a).2 ≤ C) :
    (coarseBinaryMapWithWork f array).2 ≤ n * (C + 3) := by
  cases array with
  | none => change 0 ≤ _; omega
  | some source =>
    have hc := arithmeticMapWithWork_cost f source C (fun a ha => hf a ((h source rfl).2 a ha))
    simpa only [coarseBinaryMapWithWork, (h source rfl).1] using hc

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseThresholdStepWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

 theorem coarseChildThresholdWithWork_cost (B q A : ℕ) (allowance : BinaryFraction)
    (draw : Fin B) (ha : allowance.width ≤ A)
    (hB : Nat.size B + 2 ≤ A) (hq : Nat.size q + 2 ≤ A) :
    (coarseChildThresholdWithWork B q allowance draw).2 ≤
      30000000 * (A + 1) ^ 2 := by
  have hdraw : Nat.size (draw.val + 1) + 2 ≤ A :=
    (Nat.add_le_add_right (Nat.size_le_size (show draw.val + 1 ≤ B by omega)) 2).trans hB
  have hn := (nat_width_le (draw.val + 1)).trans hdraw
  have hb := (nat_width_le B).trans hB
  have hq' := (nat_width_le q).trans hq
  have hnc := canonicalMulWithWork_cost allowance (nat (draw.val + 1)) A ha hn
  have hdc := canonicalMulWithWork_cost (nat B) (nat q) A hb hq'
  have hnw := canonicalMulWithWork_width allowance (nat (draw.val + 1)) A ha hn
  have hdw := canonicalMulWithWork_width (nat B) (nat q) A hb hq'
  have hc := coarseDivideWithWork_cost
    (canonicalMulWithWork allowance (nat (draw.val + 1))).1
    (canonicalMulWithWork (nat B) (nat q)).1 (4 * A + 2) hnw hdw
  change (canonicalMulWithWork allowance (nat (draw.val + 1))).2 +
    (canonicalMulWithWork (nat B) (nat q)).2 +
    (coarseDivideWithWork (canonicalMulWithWork allowance (nat (draw.val + 1))).1
      (canonicalMulWithWork (nat B) (nat q)).1).2 +
    Nat.size (draw.val + 1) + Nat.size B + Nat.size q + 4 ≤ _
  nlinarith only [hnc, hdc, hc, hdraw, hB, hq, Nat.zero_le A]

 theorem coarseChildAllowanceWithWork_cost (L A : ℕ) (threshold : BinaryFraction)
    (ha : threshold.width ≤ A) (hL : Nat.size L + 2 ≤ A) :
    (coarseChildAllowanceWithWork L threshold).2 ≤ 1000002 * (A + 1) ^ 2 := by
  have hc := coarseDivideWithWork_cost threshold (nat L) A ha ((nat_width_le L).trans hL)
  change (coarseDivideWithWork threshold (nat L)).2 + Nat.size L + 1 ≤ _
  nlinarith only [hc, hL, Nat.zero_le A]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseChildrenBitWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

 theorem coarseBinaryChildren_bounds_oai {B d : ℕ} {α : Type*} (k q L N V D A : ℕ)
    (two allowance : BinaryFraction)
    (evaluate : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ →
      CoarseBinaryArray × ℕ)
    (weight : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ)
    (children : List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d))
    (hB : 0 < B) (hlen : children.length ≤ B) (htwo : two.value = 2) (htw : two.width ≤ A)
    (ha : allowance.width ≤ A) (hBbits : Nat.size B + 2 ≤ A)
    (hqbits : Nat.size q + 2 ≤ A) (hLbits : Nat.size L + 2 ≤ A)
    (hNbits : Nat.size N ≤ A)
    (ht : ∀ draw : Fin B, (coarseChildThresholdWithWork B q allowance draw).1.width ≤ A)
    (hs : CoarseGridCell two (coarseChildAllowanceWithWork q allowance).1 k D A)
    (hbound : Nat.size (B * (V + k) + 2) + 2 * D + 1 ≤ A)
    (he : ∀ child draw below, (child, draw, below) ∈ children → ∀ s,
      s + child.word.length ≤ N →
      CoarseBinaryBox two (2 * k + 1) V D A
        (evaluate child below (coarseChildAllowanceWithWork L
          (coarseChildThresholdWithWork B q allowance draw).1).1 s).1 ∧
      (evaluate child below (coarseChildAllowanceWithWork L
          (coarseChildThresholdWithWork B q allowance draw).1).1 s).2 ≤
        (100000000 * (A + 1) ^ 2) * weight child below
          (coarseChildAllowanceWithWork L (coarseChildThresholdWithWork B q allowance draw).1).1)
    (start : ℕ) (hstart : start + coarseChildrenSpan children ≤ N) :
    CoarseBinaryBox two (2 * k + 1) (children.length * (V + k)) D A
      (coarseBinaryChildren k q L two evaluate allowance children start).1 ∧
    (coarseBinaryChildren k q L two evaluate allowance children start).2 + children.length ≤
      (100000000 * (A + 1) ^ 2) *
        (coarseBinaryChildrenWeight q L weight allowance children + (2 * k + 1) * children.length) := by
  have hvsmall : V + 2 ≤ B * (V + k) + 2 := by nlinarith
  have hvbound : Nat.size (V + 2) + 2 * D + 1 ≤ A :=
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.size_le_size hvsmall) _) _).trans hbound
  have hmapbound : Nat.size (V + k) + 2 * D + 1 ≤ A :=
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.size_le_size (by nlinarith : V + k ≤ B * (V + k) + 2)) _) _).trans hbound
  induction children generalizing start with
  | nil =>
    constructor
    · exact coarseBinaryBox_none _ _ _ _ _
    · simp only [coarseBinaryChildren, coarseBinaryChildrenWeight, List.length_nil, mul_zero, add_zero, le_refl]
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    have hspan : start + (child.word.length + coarseChildrenSpan rest) ≤ N := hstart
    have hchild := he child draw below List.mem_cons_self start (by omega)
    have hrest := ih (by simp only [List.length_cons] at hlen; omega)
      (fun child draw below hmem => he child draw below (List.mem_cons_of_mem _ hmem))
      (start + child.word.length) (by omega)
    let threshold := coarseChildThresholdWithWork B q allowance draw
    let childAllowance := coarseChildAllowanceWithWork L threshold.1
    let evaluated := evaluate child below childAllowance.1 start
    let penalty := coarseBinaryPenaltyWithWork two evaluated.1
    let scale := coarseChildAllowanceWithWork q allowance
    let contribution := coarseBinaryMapWithWork (coarseContributionWithWork threshold.1 scale.1) penalty.1
    let remainder := coarseBinaryChildren k q L two evaluate allowance rest (start + child.word.length)
    have hpen : CoarseBinaryBox two (2 * k + 1) V D A penalty.1 :=
      coarseBinaryPenaltyWithWork_box two _ V D A evaluated.1 hchild.1 htwo htw hvbound
    have hcon : CoarseBinaryBox two (2 * k + 1) (V + k) D A contribution.1 :=
      coarseBinaryMapWithWork_box two _ V (V + k) D A _ penalty.1 hpen
        (fun a ha => coarseContributionWithWork_bounds two threshold.1 scale.1 a V k D A ha hs hmapbound)
    have habound : Nat.size ((V + k) + rest.length * (V + k)) + 2 * D + 1 ≤ A := by
      apply le_trans _ hbound
      apply Nat.add_le_add_right
      apply Nat.add_le_add_right
      apply Nat.size_le_size
      simp only [List.length_cons] at hlen
      nlinarith
    constructor
    · have hh := coarseBinaryAddWithWork_box two (2 * k + 1) (V + k) (rest.length * (V + k)) D A
        contribution.1 remainder.1 hcon hrest.1 habound
      change CoarseBinaryBox two (2 * k + 1) ((rest.length + 1) * (V + k)) D A
        (coarseBinaryAddWithWork contribution.1 remainder.1).1
      simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using hh
    · have htc := coarseChildThresholdWithWork_cost B q A allowance draw ha hBbits hqbits
      have hlc := coarseChildAllowanceWithWork_cost L A threshold.1 (ht draw) hLbits
      have hsc := coarseChildAllowanceWithWork_cost q A allowance ha hqbits
      have hpc := coarseBinaryPenaltyWithWork_cost two (2 * k + 1) V D A evaluated.1 hchild.1 htwo htw hvbound
      have hmc := coarseBinaryMapWithWork_cost two (2 * k + 1) V D A (2200 * (A + 1) ^ 2)
        (coarseContributionWithWork threshold.1 scale.1) penalty.1 hpen
        (fun a ha => coarseContributionWithWork_cost threshold.1 scale.1 a A
          (ht draw) hs.2.2.2.2 ha.2.2.2.2)
      have hac := coarseBinaryAddWithWork_cost two (2 * k + 1) (V + k) (rest.length * (V + k)) D A
        contribution.1 remainder.1 hcon hrest.1
      have haddr : Nat.size start ≤ A := (Nat.size_le_size (by omega)).trans hNbits
      have hchildlen : Nat.size child.word.length ≤ A := (Nat.size_le_size (by omega)).trans hNbits
      have hstep : threshold.2 + childAllowance.2 + penalty.2 + scale.2 + contribution.2 +
          (coarseBinaryAddWithWork contribution.1 remainder.1).2 +
          Nat.size start + Nat.size child.word.length + 10 ≤
          100000000 * (A + 1) ^ 2 * (2 * k + 1) := by
        nlinarith only [htc, hlc, hsc, hpc, hmc, hac, haddr, hchildlen,
          Nat.zero_le A, Nat.zero_le k]
      change threshold.2 + childAllowance.2 + evaluated.2 + penalty.2 + scale.2 + contribution.2 +
        remainder.2 + (coarseBinaryAddWithWork contribution.1 remainder.1).2 +
        Nat.size start + Nat.size child.word.length + 9 + (rest.length + 1) ≤ _
      have heval := hchild.2
      change evaluated.2 ≤ _ at heval
      have hrec := hrest.2
      change remainder.2 + rest.length ≤ _ at hrec
      simp only [coarseBinaryChildrenWeight, List.length_cons]
      nlinarith only [hstep, heval, hrec]

end BinaryFraction
end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.BinaryFraction.coarseBinaryChildren_bounds_oai.{u_1} := @OAI.EditApproximation.BinaryFraction.coarseBinaryChildren_bounds_oai.{u_1}
