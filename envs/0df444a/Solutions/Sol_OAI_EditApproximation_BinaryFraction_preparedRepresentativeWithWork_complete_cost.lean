-- Prove2me | solution 1 for OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_complete_cost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:30:39.381664+00:00
-- url     : https://prove2.me/submissions/f550c5a2-a39a-4513-85df-1bd1fa07f022

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

theorem add_den_bits (a b : UnreducedRational) :
    Nat.size (a.add b).den ≤ Nat.size a.den + Nat.size b.den :=
  natural_product_bit_length _ _

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

theorem zero_width_le_storageBits : zero.width ≤ zero.representation.storageBits := by decide

theorem dotListWithWork_width_le_storageBits {d : ℕ} (left right : Vector BinaryFraction d)
    (indices : List (Fin d)) :
    (dotListWithWork left right indices).1.width ≤
      (dotListWithWork left right indices).1.representation.storageBits := by
  cases indices with
  | nil => exact zero_width_le_storageBits
  | cons i rest =>
    dsimp only [dotListWithWork]
    exact canonicalAddWithWork_self_width _ _

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_UnreducedStorage
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.nat_representation _root_.OAI.EditApproximation.BinaryFraction.representation_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
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

theorem dotList_den_bits {d : ℕ} (left right : Vector UnreducedRational d)
    (indices : List (Fin d)) (L R : ℕ)
    (hl : ∀ i ∈ indices, Nat.size (left.get i).den ≤ L)
    (hr : ∀ i ∈ indices, Nat.size (right.get i).den ≤ R) :
    Nat.size (dotList left right indices).den ≤ 1 + indices.length * (L + R) := by
  induction indices with
  | nil => simp [dotList, zero]
  | cons i rest ih =>
    have ht := ih (fun i hi => hl i (List.mem_cons_of_mem _ hi))
      (fun i hi => hr i (List.mem_cons_of_mem _ hi))
    have hi := mul_den_bits (left.get i) (right.get i)
    have hs := add_den_bits ((left.get i).mul (right.get i)) (dotList left right rest)
    have hil := hl i List.mem_cons_self
    have hir := hr i List.mem_cons_self
    change Nat.size (((left.get i).mul (right.get i)).add (dotList left right rest)).den ≤ _
    simp only [List.length_cons]
    nlinarith only [ht, hi, hs, hil, hir]

theorem dotList_abs_le {d : ℕ} (left right : Vector UnreducedRational d)
    (indices : List (Fin d)) (L R : ℕ)
    (hl : ∀ i ∈ indices, |(left.get i).value| ≤ L)
    (hr : ∀ i ∈ indices, |(right.get i).value| ≤ R) :
    |(dotList left right indices).value| ≤ indices.length * L * R := by
  induction indices with
  | nil => simp [dotList]
  | cons i rest ih =>
    have ht := ih (fun i hi => hl i (List.mem_cons_of_mem _ hi))
      (fun i hi => hr i (List.mem_cons_of_mem _ hi))
    have hi := mul_le_mul (hl i List.mem_cons_self) (hr i List.mem_cons_self)
      (abs_nonneg _) (Nat.cast_nonneg L)
    simp only [dotList, value_add, value_mul]
    calc
      _ ≤ |(left.get i).value * (right.get i).value| + |(dotList left right rest).value| := abs_add_le _ _
      _ ≤ (L : ℚ) * R + rest.length * L * R := by rw [abs_mul]; exact add_le_add hi ht
      _ = (i :: rest).length * L * R := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one] <;> ring

theorem dotList_storageBits {d : ℕ} (left right : Vector UnreducedRational d)
    (indices : List (Fin d)) (BL BR VL VR : ℕ)
    (hlbits : ∀ i ∈ indices, Nat.size (left.get i).den ≤ BL)
    (hrbits : ∀ i ∈ indices, Nat.size (right.get i).den ≤ BR)
    (hlvalue : ∀ i ∈ indices, |(left.get i).value| ≤ VL)
    (hrvalue : ∀ i ∈ indices, |(right.get i).value| ≤ VR) :
    (dotList left right indices).storageBits ≤ Nat.size (indices.length * VL * VR) +
      2 * (1 + indices.length * (BL + BR)) + 1 := by
  apply storageBits_le
  · simpa only [Nat.cast_mul] using dotList_abs_le left right indices VL VR hlvalue hrvalue
  · exact dotList_den_bits left right indices BL BR hlbits hrbits

end UnreducedRational
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRawStorage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Boolean word lengths in the materialized numerical implementation.
These bounds use the stored unreduced values, without a gcd reduction. -/

namespace EditApproximation
namespace BinaryFraction

theorem dotListWithWork_width {d : ℕ} (left right : Vector BinaryFraction d)
    (indices : List (Fin d)) (BL BR VL VR : ℕ)
    (hlbits : ∀ i ∈ indices, Nat.size (left.get i).representation.den ≤ BL)
    (hrbits : ∀ i ∈ indices, Nat.size (right.get i).representation.den ≤ BR)
    (hlvalue : ∀ i ∈ indices, |(left.get i).value| ≤ VL)
    (hrvalue : ∀ i ∈ indices, |(right.get i).value| ≤ VR) :
    (dotListWithWork left right indices).1.width ≤ Nat.size (indices.length * VL * VR) +
      2 * (1 + indices.length * (BL + BR)) + 1 := by
  have hwidth := dotListWithWork_width_le_storageBits left right indices
  rw [dotListWithWork_representation] at hwidth
  apply hwidth.trans
  apply UnreducedRational.dotList_storageBits _ _ _ BL BR VL VR
  · simpa only [vector_map_get] using hlbits
  · simpa only [vector_map_get] using hrbits
  · simpa only [vector_map_get, representation_value] using hlvalue
  · simpa only [vector_map_get, representation_value] using hrvalue

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRawCost
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
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

theorem neg_width (a : BinaryFraction) : a.neg.width = a.width := rfl

theorem invWithWork_width (a : BinaryFraction) : (a.invWithWork).1.width ≤ a.width + 1 := by
  unfold invWithWork
  dsimp only
  split_ifs
  · change 1 ≤ a.width + 1
    omega
  · change max a.denominator.length a.numerator.bits.length ≤ a.width + 1
    rw [max_comm]
    exact Nat.le_add_right _ _

theorem subWithWork_cost (a b : BinaryFraction) (B : ℕ) (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (a.subWithWork b).2 ≤ 6000 * (B + 1) ^ 2 + 1 := by
  have h := canonicalAddWithWork_cost a b.neg B ha (by simpa only [neg_width] using hb)
  exact Nat.add_le_add_right h 1

theorem divWithWork_cost (a b : BinaryFraction) (B : ℕ) (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (a.divWithWork b).2 ≤ 2100 * (B + 2) ^ 2 := by
  have hi := invWithWork_cost b
  have hw := invWithWork_width b
  have hm := canonicalMulWithWork_cost a (b.invWithWork).1 (B + 1)
    (by omega) (by omega)
  change (b.invWithWork).2 + (canonicalMulWithWork a (b.invWithWork).1).2 + 1 ≤ _
  nlinarith only [hi, hw, hm, hb]

theorem representation_den_bits_le_width (a : BinaryFraction) :
    Nat.size a.representation.den ≤ a.width := by
  have hd : Nat.size (bitWordValue a.denominator) ≤ a.denominator.length :=
    Nat.size_le.mpr (bitWordValue_lt_pow_length _)
  exact hd.trans (le_max_right _ _)

theorem dotListWithWork_width_in {d : ℕ} (left right : Vector BinaryFraction d)
    (indices : List (Fin d)) (n B V : ℕ) (hlen : indices.length ≤ n)
    (hlwidth : ∀ i ∈ indices, (left.get i).width ≤ B)
    (hrwidth : ∀ i ∈ indices, (right.get i).width ≤ B)
    (hlvalue : ∀ i ∈ indices, |(left.get i).value| ≤ V)
    (hrvalue : ∀ i ∈ indices, |(right.get i).value| ≤ V) :
    (dotListWithWork left right indices).1.width ≤ dotWordBudget n B V := by
  have hw := dotListWithWork_width left right indices B B V V
    (fun i hi => (representation_den_bits_le_width _).trans (hlwidth i hi))
    (fun i hi => (representation_den_bits_le_width _).trans (hrwidth i hi)) hlvalue hrvalue
  have hs := Nat.size_le_size (Nat.mul_le_mul_right V (Nat.mul_le_mul_right V hlen))
  have hm := Nat.mul_le_mul_right (B + B) hlen
  unfold dotWordBudget
  omega

theorem dotListWithWork_cost_in {d : ℕ} (left right : Vector BinaryFraction d)
    (indices : List (Fin d)) (n B V : ℕ) (hlen : indices.length ≤ n)
    (hlwidth : ∀ i ∈ indices, (left.get i).width ≤ B)
    (hrwidth : ∀ i ∈ indices, (right.get i).width ≤ B)
    (hlvalue : ∀ i ∈ indices, |(left.get i).value| ≤ V)
    (hrvalue : ∀ i ∈ indices, |(right.get i).value| ≤ V) :
    (dotListWithWork left right indices).2 ≤
      1 + indices.length * (100000 * (dotWordBudget n B V + 1) ^ 2) := by
  induction indices with
  | nil => simp [dotListWithWork]
  | cons i rest ih =>
    let W := dotWordBudget n B V
    have hBW : B ≤ W := by dsimp only [W, dotWordBudget]; omega
    have hl := hlwidth i List.mem_cons_self
    have hr := hrwidth i List.mem_cons_self
    have ht := ih (by simp only [List.length_cons] at hlen; omega)
      (fun i hi => hlwidth i (List.mem_cons_of_mem _ hi))
      (fun i hi => hrwidth i (List.mem_cons_of_mem _ hi))
      (fun i hi => hlvalue i (List.mem_cons_of_mem _ hi))
      (fun i hi => hrvalue i (List.mem_cons_of_mem _ hi))
    have htail : (dotListWithWork left right rest).1.width ≤ W :=
      dotListWithWork_width_in left right rest n B V (by simp only [List.length_cons] at hlen; omega)
        (fun i hi => hlwidth i (List.mem_cons_of_mem _ hi))
        (fun i hi => hrwidth i (List.mem_cons_of_mem _ hi))
        (fun i hi => hlvalue i (List.mem_cons_of_mem _ hi))
        (fun i hi => hrvalue i (List.mem_cons_of_mem _ hi))
    have hp := canonicalMulWithWork_cost (left.get i) (right.get i) W (hl.trans hBW) (hr.trans hBW)
    have hproduct : (canonicalMulWithWork (left.get i) (right.get i)).1.width ≤ 4 * W + 2 := by
      have hc := canonicalMulWithWork_width_le_storageBits (left.get i) (right.get i)
      have hm := UnreducedRational.storageBits_mul (left.get i).representation (right.get i).representation
      have hls := (representation_storageBits_le (left.get i)).trans
        (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hl.trans hBW)) 1)
      have hrs := (representation_storageBits_le (right.get i)).trans
        (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hr.trans hBW)) 1)
      omega
    have ha := canonicalAddWithWork_cost (canonicalMulWithWork (left.get i) (right.get i)).1
      (dotListWithWork left right rest).1 (4 * W + 2) hproduct (by omega)
    have hstep : (canonicalMulWithWork (left.get i) (right.get i)).2 +
        (canonicalAddWithWork (canonicalMulWithWork (left.get i) (right.get i)).1
          (dotListWithWork left right rest).1).2 + 5 ≤ 100000 * (W + 1) ^ 2 := by
      nlinarith only [hp, ha, Nat.zero_le W]
    change (dotListWithWork left right rest).2 +
      (canonicalMulWithWork (left.get i) (right.get i)).2 +
      (canonicalAddWithWork (canonicalMulWithWork (left.get i) (right.get i)).1
        (dotListWithWork left right rest).1).2 + 5 ≤ _
    simp only [List.length_cons]
    change _ ≤ 1 + (rest.length + 1) * (100000 * (W + 1) ^ 2)
    change (dotListWithWork left right rest).2 ≤ 1 + rest.length * (100000 * (W + 1) ^ 2) at ht
    nlinarith only [ht, hstep]

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGradientWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bit-operation bound for each actually materialized gradient coordinate. -/

namespace EditApproximation
namespace BinaryFraction

theorem vectorMapWithWork_cost_le {α : Type*} (d : ℕ) (f : Fin d → α × ℕ)
    (C : ℕ) (hC : ∀ i, (f i).2 ≤ C) :
    (vectorMapWithWork d f).2 ≤ d * (C + 6) := by
  simp only [vectorMapWithWork, Vector.toList_map, Vector.toList_ofFn,
    List.map_ofFn, Function.comp_def, List.sum_ofFn]
  have hs : (∑ i : Fin d, (f i).2) ≤ d * C := by
    calc
      _ ≤ ∑ _ : Fin d, C := Finset.sum_le_sum (fun i _ => hC i)
      _ = d * C := by simp
  nlinarith only [hs]

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandInputs
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Actual Boolean construction of the normalized band vertices.
The input masses are stored fractions; their sum and divisions use the
counted routines and no reduced-rational conversion is performed. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

theorem bandMassTotalWithWork_storage {M : ℕ} (mass : Vector BinaryFraction M)
    (B : ℕ) (hmass : ∀ i, (mass.get i).width ≤ B) :
    (bandMassTotalWithWork mass).1.representation.storageBits ≤ bandMassTotalStorageBudget M B := by
  have hvalue (i : Fin M) : |(mass.get i).value| ≤ ((2 ^ B : ℕ) : ℚ) := by
    have h := (value_abs_le_pow_width (mass.get i)).trans
      (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (hmass i))
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h
  have h := UnreducedRational.dotList_storageBits
    (mass.map representation) ((Vector.replicate M one).map representation)
    (List.finRange M) B 1 (2 ^ B) 1
    (by intro i _; simpa only [vector_map_get] using (representation_den_bits_le_width (mass.get i)).trans (hmass i))
    (by intro i _; simp [one_representation, UnreducedRational.one, UnreducedRational.ofRat])
    (by intro i _; simpa only [vector_map_get, representation_value] using hvalue i)
    (by intro i _; simp [one_representation])
  simp only [List.length_finRange, Nat.mul_one] at h
  have hsize := (natural_product_bit_length M (2 ^ B)).trans
    (Nat.add_le_add_left (by rw [Nat.size_pow] : Nat.size (2 ^ B) ≤ B + 1) M.size)
  rw [bandMassTotalWithWork, dotWithWork_representation]
  change (UnreducedRational.dotList (mass.map representation)
    ((Vector.replicate M one).map representation) (List.finRange M)).storageBits ≤ _
  unfold bandMassTotalStorageBudget
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandInputWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bit-operation costs for preparing the actual stored band vertices.  The
large numerical values in the generic dot-product bound occur only inside
`Nat.size`; the resulting bound is polynomial in the stored word width. -/

namespace EditApproximation
namespace BinaryFraction

theorem bandMassTotalWithWork_cost {M : ℕ} (mass : Vector BinaryFraction M)
    (B : ℕ) (hmass : ∀ i, (mass.get i).width ≤ B) :
    (bandMassTotalWithWork mass).2 ≤ storedSumBitBudget M B := by
  have hvalue (i : Fin M) : |(mass.get i).value| ≤ ((2 ^ (B + 1) : ℕ) : ℚ) := by
    have h := (value_abs_le_pow_width (mass.get i)).trans
      (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2)
        (show (mass.get i).width ≤ B + 1 by have := hmass i; omega))
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h
  have honew : one.width ≤ B + 1 := by
    change 1 ≤ B + 1
    omega
  have hone : |one.value| ≤ ((2 ^ (B + 1) : ℕ) : ℚ) := by
    have hp : 1 ≤ 2 ^ (B + 1) := Nat.one_le_pow _ _ (by decide)
    rw [← representation_value one, one_representation, UnreducedRational.value_one, abs_one]
    exact_mod_cast hp
  have h := dotListWithWork_cost_in mass (Vector.replicate M one)
    (List.finRange M) M (B + 1) (2 ^ (B + 1)) (by simp)
    (by intro i _; have := hmass i; omega)
    (by intro i _; simpa using honew)
    (by intro i _; exact hvalue i)
    (by intro i _; simpa using hone)
  have hs1 := natural_product_bit_length (M * 2 ^ (B + 1)) (2 ^ (B + 1))
  have hs2 := natural_product_bit_length M (2 ^ (B + 1))
  have hp : Nat.size (2 ^ (B + 1)) = B + 2 := by rw [Nat.size_pow]
  have hword : dotWordBudget M (B + 1) (2 ^ (B + 1)) ≤ storedSumWordBudget M B := by
    unfold dotWordBudget storedSumWordBudget
    omega
  change (dotListWithWork mass (Vector.replicate M one) (List.finRange M)).2 ≤ _
  simp only [List.length_finRange] at h
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left M
    (Nat.mul_le_mul_left 100000 (Nat.pow_le_pow_left (by omega) 2))) 1)

end BinaryFraction
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

theorem allWithWork_cost {α : Type*} (test : α → Bool × ℕ) (values : List α)
    (C : ℕ) (hC : ∀ a ∈ values, (test a).2 ≤ C) :
    (allWithWork test values).2 ≤ values.length * (C + 3) := by
  induction values with
  | nil => simp [allWithWork]
  | cons a rest ih =>
    have ha := hC a List.mem_cons_self
    have ht := ih (fun b hb => hC b (List.mem_cons_of_mem _ hb))
    change (test a).2 + (allWithWork test rest).2 + 3 ≤ _
    simp only [List.length_cons]
    rw [Nat.add_mul, Nat.one_mul]
    omega

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



theorem sumListWithWork_width (values : List BinaryFraction) (B : ℕ)
    (hB : ∀ a ∈ values, a.width ≤ B) :
    (sumListWithWork values).1.width ≤ bandMassTotalStorageBudget values.length B := by
  exact (dotListWithWork_width_le_storageBits (Vector.ofFn values.get)
      (Vector.replicate values.length one) (List.finRange values.length)).trans
    (bandMassTotalWithWork_storage (Vector.ofFn values.get) B (by
      intro i
      rw [vector_get_ofFn]
      exact hB _ (List.get_mem _ _)))

theorem sumListWithWork_cost (values : List BinaryFraction) (B : ℕ)
    (hB : ∀ a ∈ values, a.width ≤ B) :
    (sumListWithWork values).2 ≤ storedSumBitBudget values.length B + 6 * values.length := by
  exact Nat.add_le_add_right (bandMassTotalWithWork_cost (Vector.ofFn values.get) B (by
    intro i
    rw [vector_get_ofFn]
    exact hB _ (List.get_mem _ _))) _

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

theorem materializedAssignmentsWithWork_cost {α : Type*} (M K : ℕ)
    (choices : Fin M → List α) (hchoices : ∀ i, (choices i).length ≤ K) :
    (materializedAssignmentsWithWork M choices).2 ≤
      (M + 1) * (6 * M + 10) * (K + 1) ^ (M + 1) := by
  induction M with
  | zero =>
    simp only [materializedAssignmentsWithWork, Nat.zero_add, Nat.mul_zero, pow_one, Nat.one_mul]
    omega
  | succ M ih =>
    let previous := materializedAssignmentsWithWork M (fun i => choices i.succ)
    have hprevious := ih (fun i => choices i.succ) (fun i => hchoices i.succ)
    have hlength : previous.1.length ≤ K ^ M := by
      have heq := congrArg List.length
        (materializedAssignmentsWithWork_value M (fun i => choices i.succ))
      simp only [List.length_map] at heq
      exact heq.trans_le (finiteAssignments_length_le M K _ (fun i => hchoices i.succ))
    have hmap (head : α) :
        (arithmeticMapWithWork (fun tail : Vector α M =>
          (Vector.ofFn (Fin.cons head tail.get), 3 * (M + 1))) previous.1).2 ≤
            previous.1.length * (3 * (M + 1) + 3) :=
      arithmeticMapWithWork_cost _ _ _ (fun _ _ => le_rfl)
    have hmaplength (head : α) :
        (arithmeticMapWithWork (fun tail : Vector α M =>
          (Vector.ofFn (Fin.cons head tail.get), 3 * (M + 1))) previous.1).1.length ≤
            previous.1.length := by
      rw [arithmeticMapWithWork_value, List.length_map]
    have hflat := arithmeticFlatMapWithWork_cost (fun head =>
      arithmeticMapWithWork (fun tail : Vector α M =>
        (Vector.ofFn (Fin.cons head tail.get), 3 * (M + 1))) previous.1) (choices 0)
      (previous.1.length * (3 * (M + 1) + 3)) previous.1.length
      (fun head _ => hmap head) (fun head _ => hmaplength head)
    have hchoice := hchoices 0
    have hL : previous.1.length ≤ (K + 1) ^ M :=
      hlength.trans (Nat.pow_le_pow_left (by omega) M)
    have hscale : K * (K + 1) ^ M ≤ (K + 1) ^ (M + 1) := by
      rw [pow_succ]
      nlinarith
    have hZ : K + 1 ≤ (K + 1) ^ (M + 1) := Nat.le_pow (by omega)
    have hexp : (K + 1) ^ (M + 1) ≤ (K + 1) ^ (M + 2) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hexpanded :
        (arithmeticFlatMapWithWork (fun head =>
          arithmeticMapWithWork (fun tail : Vector α M =>
            (Vector.ofFn (Fin.cons head tail.get), 3 * (M + 1))) previous.1) (choices 0)).2 ≤
          (3 * M + 11) * (K + 1) ^ (M + 1) := by
      apply hflat.trans
      calc
        _ ≤ K * ((K + 1) ^ M * (3 * (M + 1) + 3) + (K + 1) ^ M + 3) :=
          Nat.mul_le_mul hchoice (by nlinarith only [hL])
        _ = (3 * M + 7) * (K * (K + 1) ^ M) + 3 * K := by ring
        _ ≤ (3 * M + 7) * (K + 1) ^ (M + 1) + 3 * K :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ hscale) _
        _ ≤ _ := by nlinarith only [hZ]
    change previous.2 + _ + 1 ≤ _
    have hcoefficient :
        (M + 1) * (6 * M + 10) + (3 * M + 11) + 1 ≤ (M + 2) * (6 * (M + 1) + 10) := by
      nlinarith
    have hone : 1 ≤ (K + 1) ^ (M + 1) := Nat.one_le_pow _ _ (by omega)
    calc
      _ ≤ ((M + 1) * (6 * M + 10) + (3 * M + 11) + 1) * (K + 1) ^ (M + 1) := by
        dsimp only [previous] at *
        nlinarith only [hprevious, hexpanded, hone]
      _ ≤ (M + 2) * (6 * (M + 1) + 10) * (K + 1) ^ (M + 2) :=
        Nat.mul_le_mul hcoefficient hexp
      _ = _ := by rfl

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

theorem subWithWork_width (a b : BinaryFraction) (B : ℕ)
    (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (a.subWithWork b).1.width ≤ 8 * B + 6 := by
  exact canonicalAddWithWork_width a b.neg B ha (by simpa only [neg_width] using hb)



theorem distanceWithWork_width (a b : BinaryFraction) (B : ℕ)
    (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (distanceWithWork a b).1.width ≤ 8 * B + 6 :=
  subWithWork_width a b B ha hb

theorem distanceWithWork_cost (a b : BinaryFraction) (B : ℕ)
    (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (distanceWithWork a b).2 ≤ 6000 * (B + 1) ^ 2 + 2 := by
  exact Nat.add_le_add_right (subWithWork_cost a b B ha hb) 1

theorem connectionTermsWithWork_width {n : ℕ} (start finish : BinaryFraction)
    (states : List (TargetInterval n)) (B : ℕ)
    (hs : start.width ≤ B) (hf : finish.width ≤ B)
    (he : ∀ state ∈ states, Nat.size state.lo + 2 ≤ B ∧ Nat.size state.hi + 2 ≤ B) :
    ∀ a ∈ (connectionTermsWithWork start states finish).1, a.width ≤ 8 * B + 6 := by
  induction states generalizing start with
  | nil =>
    intro a ha
    simp only [connectionTermsWithWork, List.mem_singleton] at ha
    subst a
    exact distanceWithWork_width start finish B hs hf
  | cons state rest ih =>
    have hstate := he state List.mem_cons_self
    intro a ha
    simp only [connectionTermsWithWork, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact distanceWithWork_width start (nat state.lo) B hs
        ((nat_width_le state.lo).trans hstate.1)
    · exact ih (nat state.hi) ((nat_width_le state.hi).trans hstate.2)
        (fun s h => he s (List.mem_cons_of_mem _ h)) a ha

theorem connectionTermsWithWork_cost {n : ℕ} (start finish : BinaryFraction)
    (states : List (TargetInterval n)) (B : ℕ)
    (hs : start.width ≤ B) (hf : finish.width ≤ B)
    (he : ∀ state ∈ states, Nat.size state.lo + 2 ≤ B ∧ Nat.size state.hi + 2 ≤ B) :
    (connectionTermsWithWork start states finish).2 ≤ connectionTermsBitBudget states.length B := by
  induction states generalizing start with
  | nil =>
    have hc := distanceWithWork_cost start finish B hs hf
    change (distanceWithWork start finish).2 + 2 ≤ _
    simpa only [connectionTermsBitBudget, List.length_nil, zero_add, one_mul, zero_mul,
      add_zero] using Nat.add_le_add_right hc 2
  | cons state rest ih =>
    have hstate := he state List.mem_cons_self
    have hc := distanceWithWork_cost start (nat state.lo) B hs
      ((nat_width_le state.lo).trans hstate.1)
    have ht := ih (nat state.hi) ((nat_width_le state.hi).trans hstate.2)
      (fun s h => he s (List.mem_cons_of_mem _ h))
    change (distanceWithWork start (nat state.lo)).2 +
      (connectionTermsWithWork (nat state.hi) rest finish).2 + Nat.size state.lo +
        Nat.size state.hi + 6 ≤ _
    simp only [connectionTermsBitBudget, List.length_cons] at ht ⊢
    simp only [Nat.add_mul, Nat.one_mul] at ht ⊢
    omega



theorem connectionWithWork_width {n : ℕ} (start finish : BinaryFraction)
    (states : List (TargetInterval n)) (B : ℕ)
    (hs : start.width ≤ B) (hf : finish.width ≤ B)
    (he : ∀ state ∈ states, Nat.size state.lo + 2 ≤ B ∧ Nat.size state.hi + 2 ≤ B) :
    (connectionWithWork start finish states).1.width ≤ connectionWordBudget states.length B := by
  have h := sumListWithWork_width (connectionTermsWithWork start states finish).1
    (8 * B + 6) (connectionTermsWithWork_width start finish states B hs hf he)
  simpa only [connectionWithWork, connectionTermsWithWork_length, connectionWordBudget] using h

theorem connectionWithWork_cost {n : ℕ} (start finish : BinaryFraction)
    (states : List (TargetInterval n)) (B : ℕ)
    (hs : start.width ≤ B) (hf : finish.width ≤ B)
    (he : ∀ state ∈ states, Nat.size state.lo + 2 ≤ B ∧ Nat.size state.hi + 2 ≤ B) :
    (connectionWithWork start finish states).2 ≤ connectionBitBudget states.length B := by
  have ht := connectionTermsWithWork_cost start finish states B hs hf he
  have hs' := sumListWithWork_cost (connectionTermsWithWork start states finish).1
    (8 * B + 6) (connectionTermsWithWork_width start finish states B hs hf he)
  simp only [connectionTermsWithWork_length] at hs'
  change _ + _ + 1 ≤ _
  unfold connectionBitBudget
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



theorem affineErrorWithWork_cost (position offset velocity prediction tolerance : BinaryFraction)
    (B : ℕ) (hp : position.width ≤ B) (ho : offset.width ≤ B)
    (hv : velocity.width ≤ B) (hpred : prediction.width ≤ B) (ht : tolerance.width ≤ B) :
    (affineErrorWithWork position offset velocity prediction tolerance).2 ≤ affineGuardBitBudget B := by
  have hdw := subWithWork_width position offset B hp ho
  have hmw := canonicalMulWithWork_width velocity prediction B hv hpred
  have hd := subWithWork_cost position offset B hp ho
  have hm := canonicalMulWithWork_cost velocity prediction B hv hpred
  have hew := subWithWork_width (position.subWithWork offset).1
    (velocity.canonicalMulWithWork prediction).1 (12 * B + 8) (by omega) (by omega)
  have he := subWithWork_cost (position.subWithWork offset).1
    (velocity.canonicalMulWithWork prediction).1 (12 * B + 8) (by omega) (by omega)
  have hc := leWithWork_cost ((position.subWithWork offset).1.subWithWork
    (velocity.canonicalMulWithWork prediction).1).1.absolute tolerance (96 * B + 70)
    (by simpa only [absolute_width] using (hew.trans (by omega : 8 * (12 * B + 8) + 6 ≤ 96 * B + 70))) (by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd] at he hc
  change _ + _ + _ + _ + 4 ≤ _
  unfold affineGuardBitBudget
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

theorem bandToleranceWithWork_bounds (tau theta : BinaryFraction) (b M B : ℕ)
    (htau : tau.width ≤ B) (htheta : theta.width ≤ B)
    (hb : Nat.size b + 2 ≤ B) (hM : Nat.size M + 2 ≤ B) :
    (bandToleranceWithWork tau theta b M).1.width ≤ 64 * B + 44 ∧
    (bandToleranceWithWork tau theta b M).2 ≤ bandToleranceBitBudget B := by
  have hpw := canonicalMulWithWork_width tau theta B htau htheta
  have hp := canonicalMulWithWork_cost tau theta B htau htheta
  have hsw := canonicalMulWithWork_width (canonicalMulWithWork tau theta).1 (nat b)
    (4 * B + 2) hpw ((nat_width_le b).trans (by omega))
  have hs := canonicalMulWithWork_cost (canonicalMulWithWork tau theta).1 (nat b)
    (4 * B + 2) hpw ((nat_width_le b).trans (by omega))
  have htw := divWithWork_width_uniform (canonicalMulWithWork
    (canonicalMulWithWork tau theta).1 (nat b)).1 (nat M) (16 * B + 10)
    (by omega) ((nat_width_le M).trans (by omega))
  have ht := divWithWork_cost (canonicalMulWithWork
    (canonicalMulWithWork tau theta).1 (nat b)).1 (nat M) (16 * B + 10)
    (by omega) ((nat_width_le M).trans (by omega))
  refine ⟨by dsimp only [bandToleranceWithWork]; omega, ?_⟩
  simp only [Nat.add_assoc, Nat.reduceAdd] at hs ht
  change _ + _ + _ + Nat.size b + Nat.size M + 3 ≤ _
  unfold bandToleranceBitBudget
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPrefixWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal stored-fraction evaluation of the finite prefix predictor.
Every prefix minimum scans the finite action array and uses exact
Boolean comparisons. No rational operation is assigned unit cost. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

private theorem prefix_parts {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (states : Fin M → TargetInterval ny)
    (child : Fin M → TargetInterval ny → BinaryFraction) (j : ℕ) (p : BinaryFraction)
    (B : ℕ) (hp : p.width ≤ B) (hr : Nat.size r.lo + 2 ≤ B)
    (hcut : Nat.size (balancedCut parent.lo (parent.hi - parent.lo) M j) + 2 ≤ B)
    (hstate : ∀ i, Nat.size (states i).lo + 2 ≤ B ∧ Nat.size (states i).hi + 2 ≤ B)
    (hchild : ∀ i, (child i (states i)).width ≤ B) :
    let finish := canonicalAddWithWork (nat (balancedCut parent.lo (parent.hi - parent.lo) M j)) p
    let connection := connectionWithWork (nat r.lo) finish.1 ((List.ofFn states).take j)
    let total := sumListWithWork (List.ofFn fun i : Fin M =>
      if i.val < j then child i (states i) else zero)
    connection.1.width ≤ prefixConnectionWord M j B ∧
    total.1.width ≤ bandMassTotalStorageBudget M B ∧
    connection.2 ≤ connectionBitBudget (min j M) (8 * B + 6) ∧
    total.2 ≤ storedSumBitBudget M B + 6 * M := by
  dsimp only
  have hfinish := canonicalAddWithWork_width
    (nat (balancedCut parent.lo (parent.hi - parent.lo) M j)) p B
    ((nat_width_le _).trans hcut) hp
  have hstart : (nat r.lo).width ≤ 8 * B + 6 := by
    have := (nat_width_le r.lo).trans hr
    omega
  have hend : ∀ state ∈ (List.ofFn states).take j,
      Nat.size state.lo + 2 ≤ 8 * B + 6 ∧ Nat.size state.hi + 2 ≤ 8 * B + 6 := by
    intro state hs
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hs)
    have hi := hstate i
    omega
  have hlist : ∀ a ∈ (List.ofFn fun i : Fin M =>
      if i.val < j then child i (states i) else zero), a.width ≤ B := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    split_ifs
    · exact hchild i
    · have : zero.width = 1 := rfl
      have := hcut
      omega
  have hw := connectionWithWork_width (nat r.lo) _ ((List.ofFn states).take j)
    (8 * B + 6) hstart hfinish hend
  have hc := connectionWithWork_cost (nat r.lo) _ ((List.ofFn states).take j)
    (8 * B + 6) hstart hfinish hend
  have htw := sumListWithWork_width _ B hlist
  have htc := sumListWithWork_cost _ B hlist
  simp only [List.length_take, List.length_ofFn] at hw hc htw htc
  exact ⟨hw, htw, hc, htc⟩

theorem prefixWithWork_width {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (states : Fin M → TargetInterval ny)
    (child : Fin M → TargetInterval ny → BinaryFraction) (j : ℕ) (p : BinaryFraction)
    (B : ℕ) (hp : p.width ≤ B) (hr : Nat.size r.lo + 2 ≤ B)
    (hcut : Nat.size (balancedCut parent.lo (parent.hi - parent.lo) M j) + 2 ≤ B)
    (hstate : ∀ i, Nat.size (states i).lo + 2 ≤ B ∧ Nat.size (states i).hi + 2 ≤ B)
    (hchild : ∀ i, (child i (states i)).width ≤ B) :
    (prefixWithWork parent r states child j p).1.width ≤ prefixWordBudget M j B := by
  obtain ⟨hw, htw, _, _⟩ := prefix_parts parent r states child j p B hp hr hcut hstate hchild
  exact canonicalAddWithWork_width _ _ _
    (hw.trans (Nat.le_add_right _ _)) (htw.trans (Nat.le_add_left _ _))

theorem prefixWithWork_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (states : Fin M → TargetInterval ny)
    (child : Fin M → TargetInterval ny → BinaryFraction) (j : ℕ) (p : BinaryFraction)
    (B : ℕ) (hp : p.width ≤ B) (hr : Nat.size r.lo + 2 ≤ B)
    (hcut : Nat.size (balancedCut parent.lo (parent.hi - parent.lo) M j) + 2 ≤ B)
    (hstate : ∀ i, Nat.size (states i).lo + 2 ≤ B ∧ Nat.size (states i).hi + 2 ≤ B)
    (hchild : ∀ i, (child i (states i)).width ≤ B) :
    (prefixWithWork parent r states child j p).2 ≤ prefixBitBudget M j B := by
  obtain ⟨hw, htw, hc, htc⟩ := prefix_parts parent r states child j p B hp hr hcut hstate hchild
  have hf := canonicalAddWithWork_cost
    (nat (balancedCut parent.lo (parent.hi - parent.lo) M j)) p B
    ((nat_width_le _).trans hcut) hp
  have ha := canonicalAddWithWork_cost _ _
    (prefixConnectionWord M j B + bandMassTotalStorageBudget M B)
    (hw.trans (Nat.le_add_right _ _)) (htw.trans (Nat.le_add_left _ _))
  change _ + _ + _ + _ + _ + _ + 6 * M + 5 ≤ _
  unfold prefixBitBudget
  omega

theorem prefixMinimumWithWork_bounds {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (child : Fin M → TargetInterval ny → BinaryFraction) (j : ℕ) (p : BinaryFraction)
    (B : ℕ) (hp : p.width ≤ B) (hr : Nat.size r.lo + 2 ≤ B)
    (hcut : Nat.size (balancedCut parent.lo (parent.hi - parent.lo) M j) + 2 ≤ B)
    (hstate : ∀ action ∈ actions, ∀ i,
      Nat.size (action i).lo + 2 ≤ B ∧ Nat.size (action i).hi + 2 ≤ B)
    (hchild : ∀ action ∈ actions, ∀ i, (child i (action i)).width ≤ B) :
    (prefixMinimumWithWork parent r actions hne child j p).1.width ≤ prefixWordBudget M j B ∧
    (prefixMinimumWithWork parent r actions hne child j p).2 ≤
      prefixMinimumBitBudget M j actions.length B := by
  have hw (action) (ha : action ∈ actions) :=
    prefixWithWork_width parent r action child j p B hp hr hcut (hstate action ha) (hchild action ha)
  have hc (action) (ha : action ∈ actions) :=
    prefixWithWork_cost parent r action child j p B hp hr hcut (hstate action ha) (hchild action ha)
  have hf := List.head_mem hne
  have hmap : ∀ a ∈ (arithmeticMapWithWork
      (fun action => prefixWithWork parent r action child j p) actions).1,
      a.width ≤ prefixWordBudget M j B := by
    intro a ha
    rw [arithmeticMapWithWork_value] at ha
    obtain ⟨action, hmem, heq⟩ := List.mem_map.mp ha
    subst a
    exact hw action hmem
  have hmw := minimumWithWork_width _ _ _ (hw _ hf) hmap
  have hmc := minimumWithWork_cost _ _ _ (hw _ hf) hmap
  have hsc := arithmeticMapWithWork_cost
    (fun action => prefixWithWork parent r action child j p) actions (prefixBitBudget M j B) hc
  have hlen : (arithmeticMapWithWork
      (fun action => prefixWithWork parent r action child j p) actions).1.length = actions.length := by
    rw [arithmeticMapWithWork_value, List.length_map]
  rw [hlen] at hmc
  refine ⟨hmw, ?_⟩
  have hfc := hc _ hf
  change _ + _ + _ + 1 ≤ _
  unfold prefixMinimumBitBudget
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandGuardWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Exact finite band predicates evaluated on stored Boolean fractions.
The cut tests use the actual finite prefix minimum; the other tests are
Boolean comparisons of the actual interval endpoints. -/

namespace EditApproximation

open Finset



theorem zeroConnectionWithWork_cost {n : ℕ} (start finish : ℕ)
    (states : List (TargetInterval n)) (B : ℕ)
    (hs : Nat.size start ≤ B) (hf : Nat.size finish ≤ B)
    (he : ∀ s ∈ states, Nat.size s.lo ≤ B ∧ Nat.size s.hi ≤ B) :
    (zeroConnectionWithWork start states finish).2 ≤ (states.length + 1) * (8 * B + 3) := by
  induction states generalizing start with
  | nil =>
    have h := naturalEqualWithWork_cost start finish B hs hf
    simpa only [zeroConnectionWithWork, List.length_nil, zero_add, one_mul] using
      h.trans (by omega : 8 * B + 2 ≤ 8 * B + 3)
  | cons state rest ih =>
    have hstate := he state List.mem_cons_self
    have hc := naturalEqualWithWork_cost start state.lo B hs hstate.1
    have ht := ih state.hi hstate.2 (fun s h => he s (List.mem_cons_of_mem _ h))
    change _ + _ + 1 ≤ _
    simp only [List.length_cons]
    rw [show rest.length + 1 + 1 = (rest.length + 1) + 1 by omega, Nat.add_mul, Nat.one_mul]
    omega

theorem translatedEndpointWithWork_cost (reference root endpoint B : ℕ)
    (h : root ≤ endpoint) (hr : Nat.size reference ≤ B)
    (hroot : Nat.size root ≤ B) (he : Nat.size endpoint ≤ B) :
    (translatedEndpointWithWork reference root endpoint).2 ≤ 36 * B + 4 := by
  have hd := binaryNaturalSubtractWithWork_cost endpoint root
  have ha := binaryNaturalAddWithWork_cost reference
    (bitWordValue (binaryNaturalSubtractWithWork endpoint root).1)
  have hw : Nat.size (bitWordValue (binaryNaturalSubtractWithWork endpoint root).1) ≤ B := by
    rw [binaryNaturalSubtractWithWork_value endpoint root h]
    exact (Nat.size_le_size (Nat.sub_le endpoint root)).trans he
  change _ + _ + 2 ≤ _
  omega

namespace BinaryFraction

theorem naturalDistanceLeWithWork_cost (a b radius B : ℕ)
    (ha : Nat.size a + 2 ≤ B) (hb : Nat.size b + 2 ≤ B)
    (hr : Nat.size radius + 2 ≤ B) :
    (naturalDistanceLeWithWork a b radius).2 ≤ naturalDistanceBitBudget B := by
  have hdw := distanceWithWork_width (nat a) (nat b) B
    ((nat_width_le a).trans ha) ((nat_width_le b).trans hb)
  have hd := distanceWithWork_cost (nat a) (nat b) B
    ((nat_width_le a).trans ha) ((nat_width_le b).trans hb)
  have hc := leWithWork_cost (distanceWithWork (nat a) (nat b)).1 (nat radius)
    (8 * B + 6) hdw ((nat_width_le radius).trans (by omega))
  simp only [Nat.add_assoc, Nat.reduceAdd] at hc
  change _ + _ + Nat.size a + Nat.size b + Nat.size radius + 3 ≤ _
  unfold naturalDistanceBitBudget
  omega

theorem cutGuardWithWork_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (child : Fin M → TargetInterval ny → BinaryFraction) (states : Fin M → TargetInterval ny)
    (velocity tolerance : BinaryFraction) (j : Fin M) (B : ℕ)
    (hvel : velocity.width ≤ B) (htol : tolerance.width ≤ 64 * B + 44)
    (hr : Nat.size r.lo + 2 ≤ B) (hp : Nat.size parent.lo + 2 ≤ B)
    (hs : Nat.size (states j).lo + 2 ≤ B)
    (hc : Nat.size (sourceChild parent j).lo + 2 ≤ B)
    (hcut : Nat.size (balancedCut parent.lo (parent.hi - parent.lo) M j.val) + 2 ≤ B)
    (hstates : ∀ action ∈ actions, ∀ i,
      Nat.size (action i).lo + 2 ≤ B ∧ Nat.size (action i).hi + 2 ≤ B)
    (hchild : ∀ action ∈ actions, ∀ i, (child i (action i)).width ≤ B) :
    (cutGuardWithWork parent r actions hne child states velocity tolerance j).2 ≤
      cutGuardBitBudget M j.val actions.length B := by
  by_cases hj : j.val = 0
  · simp only [cutGuardWithWork, hj, ↓reduceIte]
    unfold cutGuardBitBudget
    omega
  · have hshift := subWithWork_width (nat (states j).lo) (nat (sourceChild parent j).lo) B
      ((nat_width_le _).trans hs) ((nat_width_le _).trans hc)
    have hoffset := subWithWork_width (nat r.lo) (nat parent.lo) B
      ((nat_width_le _).trans hr) ((nat_width_le _).trans hp)
    have hshiftCost := subWithWork_cost (nat (states j).lo) (nat (sourceChild parent j).lo) B
      ((nat_width_le _).trans hs) ((nat_width_le _).trans hc)
    have hoffsetCost := subWithWork_cost (nat r.lo) (nat parent.lo) B
      ((nat_width_le _).trans hr) ((nat_width_le _).trans hp)
    have hlarge : B ≤ 8 * B + 6 := by omega
    obtain ⟨hpred, hpredCost⟩ := prefixMinimumWithWork_bounds parent r actions hne child j.val
      (subWithWork (nat (states j).lo) (nat (sourceChild parent j).lo)).1 (8 * B + 6)
      hshift (hr.trans hlarge) (hcut.trans hlarge)
      (fun action ha i => ⟨(hstates action ha i).1.trans hlarge,
        (hstates action ha i).2.trans hlarge⟩)
      (fun action ha i => (hchild action ha i).trans hlarge)
    have herr := affineErrorWithWork_cost
      (subWithWork (nat (states j).lo) (nat (sourceChild parent j).lo)).1
      (subWithWork (nat r.lo) (nat parent.lo)).1 velocity
      (prefixMinimumWithWork parent r actions hne child j.val
        (subWithWork (nat (states j).lo) (nat (sourceChild parent j).lo)).1).1
      tolerance (cutGuardWordBudget M j.val B)
      (by unfold cutGuardWordBudget; omega) (by unfold cutGuardWordBudget; omega)
      (by unfold cutGuardWordBudget; omega) (by unfold cutGuardWordBudget; omega)
      (by unfold cutGuardWordBudget; omega)
    simp only [cutGuardWithWork, hj, ↓reduceIte]
    unfold cutGuardBitBudget
    omega

theorem bandPredicateWithWork_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b : ℕ) (tau theta velocity : BinaryFraction)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (child : Fin M → TargetInterval ny → BinaryFraction) (states : Fin M → TargetInterval ny)
    (B C : ℕ) (hstatesMem : states ∈ actions)
    (htau : tau.width ≤ B) (htheta : theta.width ≤ B) (hvel : velocity.width ≤ B)
    (hb : Nat.size b + 2 ≤ B) (hM : Nat.size M + 2 ≤ B)
    (hr : Nat.size r.lo + 2 ≤ B) (hrhi : Nat.size r.hi + 2 ≤ B)
    (hp : Nat.size parent.lo + 2 ≤ B)
    (hsource : ∀ i : Fin M, Nat.size (sourceChild parent i).lo + 2 ≤ B ∧
      Nat.size (sourceChild parent i).hi + 2 ≤ B)
    (hanchor : ∀ i : Fin M, Nat.size (r.lo + ((sourceChild parent i).lo - parent.lo)) + 2 ≤ B ∧
      Nat.size (r.lo + ((sourceChild parent i).hi - parent.lo)) + 2 ≤ B)
    (hradius : Nat.size (6 * b) + 2 ≤ B)
    (hstates : ∀ action ∈ actions, ∀ i,
      Nat.size (action i).lo + 2 ≤ B ∧ Nat.size (action i).hi + 2 ≤ B)
    (hchild : ∀ action ∈ actions, ∀ i, (child i (action i)).width ≤ B)
    (hC : ∀ j : Fin M, cutGuardBitBudget M j.val actions.length B ≤ C) :
    (bandPredicateWithWork parent r b tau theta velocity actions hne child states).2 ≤
      bandPredicateBitBudget M B C := by
  have hstate := hstates states hstatesMem
  have hlo (i : Fin M) : parent.lo ≤ (sourceChild parent i).lo := Nat.le_add_right _ _
  have hhi (i : Fin M) : parent.lo ≤ (sourceChild parent i).hi := Nat.le_add_right _ _
  have hconn := zeroConnectionWithWork_cost r.lo r.hi (List.ofFn states) B (by omega) (by omega) (by
    intro state hs
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
    have := hstate i
    omega)
  have hanchorCost (i : Fin M) :
      (let leftAnchor := translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).lo
       let rightAnchor := translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).hi
       let radius := binaryNaturalMulWithWork 6 b
       let left := naturalDistanceLeWithWork leftAnchor.1 (states i).lo (bitWordValue radius.1)
       let right := naturalDistanceLeWithWork rightAnchor.1 (states i).hi (bitWordValue radius.1)
       (left.1 && right.1, leftAnchor.2 + rightAnchor.2 + radius.2 + left.2 + right.2 + 3)).2 ≤
        anchorGuardBitBudget B := by
    have hl := translatedEndpointWithWork_cost r.lo parent.lo (sourceChild parent i).lo B
      (hlo i) (by omega) (by omega) (by have := hsource i; omega)
    have hh := translatedEndpointWithWork_cost r.lo parent.lo (sourceChild parent i).hi B
      (hhi i) (by omega) (by omega) (by have := hsource i; omega)
    have hrad := binaryNaturalMulWithWork_cost 6 b
    have hleft := naturalDistanceLeWithWork_cost
      (translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).lo).1 (states i).lo
      (bitWordValue (binaryNaturalMulWithWork 6 b).1) B
      (by rw [translatedEndpointWithWork_value _ _ _ (hlo i)]; exact (hanchor i).1)
      (hstate i).1 (by rw [binaryNaturalMulWithWork_value]; exact hradius)
    have hright := naturalDistanceLeWithWork_cost
      (translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).hi).1 (states i).hi
      (bitWordValue (binaryNaturalMulWithWork 6 b).1) B
      (by rw [translatedEndpointWithWork_value _ _ _ (hhi i)]; exact (hanchor i).2)
      (hstate i).2 (by rw [binaryNaturalMulWithWork_value]; exact hradius)
    norm_num only [show Nat.size 6 = 3 by decide] at hrad
    dsimp only
    unfold anchorGuardBitBudget
    omega
  have ha := allWithWork_cost _ (List.finRange M) (anchorGuardBitBudget B)
    (fun i _ => hanchorCost i)
  obtain ⟨htw, htc⟩ := bandToleranceWithWork_bounds tau theta b M B htau htheta hb hM
  have hc := allWithWork_cost
    (cutGuardWithWork parent r actions hne child states velocity (bandToleranceWithWork tau theta b M).1)
    (List.finRange M) C (by
      intro j _
      exact (cutGuardWithWork_cost parent r actions hne child states velocity
        (bandToleranceWithWork tau theta b M).1 j B hvel htw hr hp (hstate j).1
        (hsource j).1 (hsource j).1 hstates hchild).trans (hC j))
  simp only [List.length_ofFn] at hconn
  simp only [List.length_finRange] at ha hc
  change _ + _ + _ + _ + 4 ≤ _
  unfold bandPredicateBitBudget
  dsimp only at ha hc ⊢
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteBitPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A structural polynomial bound for finite Boolean arithmetic loops.
The expression language includes only operations whose magnitude is bounded
by a fixed power of a common input bound. -/

namespace EditApproximation

namespace FiniteBitPolynomial

theorem eval_le_pow {ι : Type*} (p : FiniteBitPolynomial ι) (env : ι → ℕ)
    (S : ℕ) (hS : 2 ≤ S) (henv : ∀ i, env i ≤ S) :
    p.eval env ≤ S ^ p.degree := by
  induction p with
  | input i => simpa only [eval, degree, pow_one] using henv i
  | constant n =>
    exact (Nat.lt_size_self n).le.trans (Nat.pow_le_pow_left hS _)
  | add a b ha hb =>
    have ha' := ha.trans (Nat.pow_le_pow_right (by omega : 0 < S) (Nat.le_max_left a.degree b.degree))
    have hb' := hb.trans (Nat.pow_le_pow_right (by omega : 0 < S) (Nat.le_max_right a.degree b.degree))
    change a.eval env + b.eval env ≤ S ^ (max a.degree b.degree + 1)
    calc
      _ ≤ 2 * S ^ max a.degree b.degree := by omega
      _ ≤ S * S ^ max a.degree b.degree := Nat.mul_le_mul_right _ hS
      _ = _ := (pow_succ' S _).symm
  | mul a b ha hb =>
    exact (Nat.mul_le_mul ha hb).trans_eq (pow_add S a.degree b.degree).symm
  | pow a n ha =>
    exact (Nat.pow_le_pow_left ha n).trans_eq (pow_mul S a.degree n).symm
  | maximum a b ha hb =>
    exact max_le
      (ha.trans (Nat.pow_le_pow_right (by omega) (Nat.le_max_left a.degree b.degree)))
      (hb.trans (Nat.pow_le_pow_right (by omega) (Nat.le_max_right a.degree b.degree)))
  | minimum a b ha _ =>
    exact (Nat.min_le_left _ _).trans
      (ha.trans (Nat.pow_le_pow_right (by omega) (Nat.le_max_left a.degree b.degree)))
  | bitLength a ha =>
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans ha

end FiniteBitPolynomial
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PrefixBitEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-degree polynomial envelope for the literal prefix and band-test
arithmetic. The finite expression represents the bit counters;
its degree is independent of every input length and parameter. -/

namespace EditApproximation

private theorem prefixAggregateExpression_eval (M j v B : ℕ) :
    prefixAggregateExpression.eval (prefixEnv M j v B) =
      BinaryFraction.prefixWordBudget M j B + BinaryFraction.prefixBitBudget M j B +
      BinaryFraction.prefixMinimumBitBudget M j v B + BinaryFraction.cutGuardWordBudget M j B +
      BinaryFraction.cutGuardBitBudget M j v B + BinaryFraction.naturalDistanceBitBudget B +
      BinaryFraction.bandToleranceBitBudget B := rfl

theorem prefix_guard_budgets_le_fixed_power (M j v B S : ℕ)
    (hS : 2 ≤ S) (hM : M ≤ S) (hj : j ≤ S) (hv : v ≤ S) (hB : B ≤ S) :
    BinaryFraction.prefixWordBudget M j B ≤ S ^ prefixArithmeticDegree ∧
    BinaryFraction.prefixBitBudget M j B ≤ S ^ prefixArithmeticDegree ∧
    BinaryFraction.prefixMinimumBitBudget M j v B ≤ S ^ prefixArithmeticDegree ∧
    BinaryFraction.cutGuardWordBudget M j B ≤ S ^ prefixArithmeticDegree ∧
    BinaryFraction.cutGuardBitBudget M j v B ≤ S ^ prefixArithmeticDegree ∧
    BinaryFraction.naturalDistanceBitBudget B ≤ S ^ prefixArithmeticDegree ∧
    BinaryFraction.bandToleranceBitBudget B ≤ S ^ prefixArithmeticDegree := by
  have henv : ∀ i, prefixEnv M j v B i ≤ S := by
    intro i
    fin_cases i <;> simp only [prefixEnv] <;> assumption
  have h := prefixAggregateExpression.eval_le_pow (prefixEnv M j v B) S hS henv
  rw [prefixAggregateExpression_eval] at h
  change _ ≤ S ^ prefixArithmeticDegree at h
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRepresentativeWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds for the executed representative scores and velocity. They use
only the widths of actual stored inputs, and apply on every seed. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

theorem endpointScoreWithWork_bounds {n M : ℕ} (r : TargetInterval n)
    (child : Fin M → TargetInterval n → BinaryFraction) (states : Fin M → TargetInterval n)
    (B : ℕ) (hrl : Nat.size r.lo + 2 ≤ B) (hrh : Nat.size r.hi + 2 ≤ B)
    (he : ∀ i, Nat.size (states i).lo + 2 ≤ B ∧ Nat.size (states i).hi + 2 ≤ B)
    (hv : ∀ i, (child i (states i)).width ≤ B) :
    (endpointScoreWithWork r child states).1.width ≤ endpointScoreWordBudget M B ∧
      (endpointScoreWithWork r child states).2 ≤ endpointScoreBitBudget M B := by
  have hlist : ∀ s ∈ List.ofFn states, Nat.size s.lo + 2 ≤ B ∧ Nat.size s.hi + 2 ≤ B := by
    intro s hs
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
    exact he i
  have hcw := connectionWithWork_width (nat r.lo) (nat r.hi) (List.ofFn states) B
    ((nat_width_le _).trans hrl) ((nat_width_le _).trans hrh) hlist
  have hcc := connectionWithWork_cost (nat r.lo) (nat r.hi) (List.ofFn states) B
    ((nat_width_le _).trans hrl) ((nat_width_le _).trans hrh) hlist
  simp only [List.length_ofFn] at hcw hcc
  have hew : (endpointConnectionWithWork r states).1.width ≤ connectionWordBudget M B := hcw
  have hec : (endpointConnectionWithWork r states).2 ≤ connectionBitBudget M B + 2 * B + M + 2 := by
    change _ + Nat.size r.lo + Nat.size r.hi + M + 2 ≤ _
    omega
  have hvlist : ∀ a ∈ List.ofFn (fun i => child i (states i)), a.width ≤ B := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hv i
  have hsw := sumListWithWork_width _ B hvlist
  have hsc := sumListWithWork_cost _ B hvlist
  simp only [List.length_ofFn] at hsw hsc
  have htw := canonicalAddWithWork_width (endpointConnectionWithWork r states).1
    (sumListWithWork (List.ofFn fun i => child i (states i))).1
    (connectionWordBudget M B + bandMassTotalStorageBudget M B) (by omega) (by omega)
  have htc := canonicalAddWithWork_cost (endpointConnectionWithWork r states).1
    (sumListWithWork (List.ofFn fun i => child i (states i))).1
    (connectionWordBudget M B + bandMassTotalStorageBudget M B) (by omega) (by omega)
  refine ⟨htw, ?_⟩
  change _ + _ + _ + 2 ≤ _
  unfold endpointScoreBitBudget
  omega

theorem wideMinimumWithWork_bounds {n M : ℕ} (r : TargetInterval n)
    (child : Fin M → TargetInterval n → BinaryFraction)
    (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ []) (B : ℕ)
    (hrl : Nat.size r.lo + 2 ≤ B) (hrh : Nat.size r.hi + 2 ≤ B)
    (he : ∀ states ∈ actions, ∀ i, Nat.size (states i).lo + 2 ≤ B ∧ Nat.size (states i).hi + 2 ≤ B)
    (hv : ∀ states ∈ actions, ∀ i, (child i (states i)).width ≤ B) :
    (wideMinimumWithWork r child actions hne).1.width ≤ endpointScoreWordBudget M B ∧
      (wideMinimumWithWork r child actions hne).2 ≤ wideMinimumBitBudget M actions.length B := by
  have hf := endpointScoreWithWork_bounds r child (actions.head hne) B hrl hrh
    (he _ (List.head_mem hne)) (hv _ (List.head_mem hne))
  let scores := arithmeticMapWithWork (endpointScoreWithWork r child) actions
  have hs : ∀ value ∈ scores.1, value.width ≤ endpointScoreWordBudget M B := by
    intro value hvalue
    simp only [scores, arithmeticMapWithWork_value] at hvalue
    obtain ⟨states, hstates, heq⟩ := List.mem_map.mp hvalue
    subst value
    exact (endpointScoreWithWork_bounds r child states B hrl hrh (he states hstates) (hv states hstates)).1
  have hlen : scores.1.length = actions.length := by
    simp only [scores, arithmeticMapWithWork_value, List.length_map]
  have hsc := arithmeticMapWithWork_cost (endpointScoreWithWork r child) actions
    (endpointScoreBitBudget M B) (fun states hstates =>
      (endpointScoreWithWork_bounds r child states B hrl hrh (he states hstates) (hv states hstates)).2)
  have hmw := minimumWithWork_width (endpointScoreWithWork r child (actions.head hne)).1
    scores.1 (endpointScoreWordBudget M B) hf.1 hs
  have hmc := minimumWithWork_cost (endpointScoreWithWork r child (actions.head hne)).1
    scores.1 (endpointScoreWordBudget M B) hf.1 hs
  rw [hlen] at hmc
  refine ⟨hmw, ?_⟩
  change (endpointScoreWithWork r child (actions.head hne)).2 + scores.2 +
    (minimumWithWork (endpointScoreWithWork r child (actions.head hne)).1 scores.1).2 + 2 ≤ _
  change scores.2 ≤ _ at hsc
  unfold wideMinimumBitBudget
  omega

theorem stateGapWithWork_bounds {n : ℕ} (sourceLength : ℕ) (r : TargetInterval n) (B : ℕ)
    (hs : Nat.size sourceLength + 2 ≤ B) (hrl : Nat.size r.lo + 2 ≤ B)
    (hrh : Nat.size r.hi + 2 ≤ B) :
    (stateGapWithWork sourceLength r).1.width ≤ stateGapWordBudget B ∧
      (stateGapWithWork sourceLength r).2 ≤ stateGapBitBudget B := by
  have htw := subWithWork_width (nat r.hi) (nat r.lo) B
    ((nat_width_le _).trans hrh) ((nat_width_le _).trans hrl)
  have htc := subWithWork_cost (nat r.hi) (nat r.lo) B
    ((nat_width_le _).trans hrh) ((nat_width_le _).trans hrl)
  have hsw : (nat sourceLength).width ≤ 8 * B + 6 := (nat_width_le _).trans (by omega)
  have hrw := subWithWork_width (subWithWork (nat r.hi) (nat r.lo)).1 (nat sourceLength)
    (8 * B + 6) htw hsw
  have hrc := subWithWork_cost (subWithWork (nat r.hi) (nat r.lo)).1 (nat sourceLength)
    (8 * B + 6) htw hsw
  constructor
  · change (subWithWork (subWithWork (nat r.hi) (nat r.lo)).1 (nat sourceLength)).1.width ≤ stateGapWordBudget B
    unfold stateGapWordBudget
    omega
  · change _ + _ + _ + _ + _ + 2 ≤ _
    simp only [Nat.add_assoc, Nat.reduceAdd] at hrc
    unfold stateGapBitBudget
    omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandTailWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Work of the literal representative tail. The sole callback premise is
an explicit bound on the already-defined band predicate, whose primitive
bound is `bandPredicateWithWork_cost`; no accuracy property is assumed. -/

namespace EditApproximation
namespace BinaryFraction

theorem bandFromActionsWithWork_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b : ℕ) (tau theta velocity : BinaryFraction)
    (child : Fin M → TargetInterval ny → BinaryFraction)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ []) (B C : ℕ)
    (hB : 1 ≤ B) (htau : tau.width ≤ B) (hvel : velocity.width ≤ B)
    (hC : ∀ states ∈ actions,
      (bandPredicateWithWork parent r b tau theta velocity actions hne child states).2 ≤ C) :
    (bandFromActionsWithWork parent r b tau theta velocity child actions hne).2 ≤
      bandFromActionsBitBudget actions.length B C := by
  let margin := subWithWork one tau
  have hmw := subWithWork_width one tau B (by exact hB) htau
  have hmc := subWithWork_cost one tau B (by exact hB) htau
  have hgc := leWithWork_cost velocity.absolute margin.1 (8 * B + 6)
    (by change velocity.width ≤ _; omega) hmw
  have hfc := filterWithWork_cost
    (bandPredicateWithWork parent r b tau theta velocity actions hne child) actions C hC
  unfold bandFromActionsWithWork
  dsimp only
  split_ifs
  · change margin.2 + (leWithWork velocity.absolute margin.1).2 +
      (filterWithWork (bandPredicateWithWork parent r b tau theta velocity actions hne child) actions).2 + 2 ≤ _
    change margin.2 ≤ _ at hmc
    unfold bandFromActionsBitBudget
    simp only [Nat.add_assoc, Nat.reduceAdd] at hgc
    omega
  · change margin.2 + (leWithWork velocity.absolute margin.1).2 + 1 ≤ _
    change margin.2 ≤ _ at hmc
    unfold bandFromActionsBitBudget
    simp only [Nat.add_assoc, Nat.reduceAdd] at hgc
    omega

theorem representativeFromActionsWithWork_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (sourceLength b : ℕ) (tau theta : BinaryFraction)
    (child : Fin M → TargetInterval ny → BinaryFraction)
    (actions : List (Fin M → TargetInterval ny)) (B C : ℕ)
    (htau : tau.width ≤ B) (hsource : Nat.size sourceLength + 2 ≤ B)
    (hrl : Nat.size r.lo + 2 ≤ B) (hrh : Nat.size r.hi + 2 ≤ B)
    (he : ∀ states ∈ actions, ∀ i, Nat.size (states i).lo + 2 ≤ B ∧
      Nat.size (states i).hi + 2 ≤ B)
    (hv : ∀ states ∈ actions, ∀ i, (child i (states i)).width ≤ B)
    (hC : ∀ (hne : actions ≠ []) (velocity : BinaryFraction),
      velocity.width ≤ 4 * representativeTailInputBudget M B + 4 →
      ∀ states ∈ actions,
        (bandPredicateWithWork parent r b tau theta velocity actions hne child states).2 ≤ C) :
    (representativeFromActionsWithWork parent r sourceLength b tau theta child actions).2 ≤
      representativeTailBitBudget M actions.length B C := by
  by_cases hnil : actions = []
  · simp only [representativeFromActionsWithWork, dite_eq_left hnil]
    dsimp only [representativeTailBitBudget]
    omega
  · let W := representativeTailInputBudget M B
    let Z := wideMinimumWithWork r child actions hnil
    have hW : B ≤ W := by dsimp only [W, representativeTailInputBudget]; omega
    have hWpos : 1 ≤ W := by dsimp only [W, representativeTailInputBudget]; omega
    have hz := wideMinimumWithWork_bounds r child actions hnil B hrl hrh he hv
    have hZw : Z.1.width ≤ W := hz.1.trans (by dsimp only [W, representativeTailInputBudget]; omega)
    have hpositive := ltWithWork_cost zero Z.1 W hWpos hZw
    have hgap := stateGapWithWork_bounds sourceLength r B hsource hrl hrh
    have hgapW : (stateGapWithWork sourceLength r).1.width ≤ W := hgap.1.trans (by
      dsimp only [W, representativeTailInputBudget]; omega)
    have hvel := divWithWork_width_uniform (stateGapWithWork sourceLength r).1 Z.1 W hgapW hZw
    have hvelc := divWithWork_cost (stateGapWithWork sourceLength r).1 Z.1 W hgapW hZw
    have hband := bandFromActionsWithWork_cost parent r b tau theta
      (divWithWork (stateGapWithWork sourceLength r).1 Z.1).1 child actions hnil (4 * W + 4) C
      (by omega) (htau.trans (by omega)) hvel (hC hnil _ hvel)
    unfold representativeFromActionsWithWork
    rw [dite_eq_right hnil]
    dsimp only
    split_ifs
    · change Z.2 + (ltWithWork zero Z.1).2 + (stateGapWithWork sourceLength r).2 +
        (divWithWork (stateGapWithWork sourceLength r).1 Z.1).2 +
        (bandFromActionsWithWork parent r b tau theta
          (divWithWork (stateGapWithWork sourceLength r).1 Z.1).1 child actions hnil).2 + 3 ≤
        wideMinimumBitBudget M actions.length B + 1000 * (W + 1) ^ 2 + stateGapBitBudget B +
          2100 * (W + 2) ^ 2 + bandFromActionsBitBudget actions.length (4 * W + 4) C + 3
      have hzc : Z.2 ≤ wideMinimumBitBudget M actions.length B := hz.2
      omega
    · change Z.2 + (ltWithWork zero Z.1).2 + 2 ≤
        wideMinimumBitBudget M actions.length B + 1000 * (W + 1) ^ 2 + stateGapBitBudget B +
          2100 * (W + 2) ^ 2 + bandFromActionsBitBudget actions.length (4 * W + 4) C + 3
      have hzc : Z.2 ≤ wideMinimumBitBudget M actions.length B := hz.2
      omega

/-- Every prefix-cut callback in the representative tail is bounded by
the proved finite-prefix implementation, rather than an assumed callback
budget. The premises concern only the stored input widths. -/
theorem representativeFromActionsWithWork_complete_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (sourceLength b : ℕ) (tau theta : BinaryFraction)
    (child : Fin M → TargetInterval ny → BinaryFraction)
    (actions : List (Fin M → TargetInterval ny)) (B : ℕ)
    (htau : tau.width ≤ B) (htheta : theta.width ≤ B)
    (hsourceLength : Nat.size sourceLength + 2 ≤ B)
    (hb : Nat.size b + 2 ≤ B) (hM : Nat.size M + 2 ≤ B)
    (hrl : Nat.size r.lo + 2 ≤ B) (hrh : Nat.size r.hi + 2 ≤ B)
    (hp : Nat.size parent.lo + 2 ≤ B)
    (hsource : ∀ i : Fin M, Nat.size (sourceChild parent i).lo + 2 ≤ B ∧
      Nat.size (sourceChild parent i).hi + 2 ≤ B)
    (hanchor : ∀ i : Fin M, Nat.size (r.lo + ((sourceChild parent i).lo - parent.lo)) + 2 ≤ B ∧
      Nat.size (r.lo + ((sourceChild parent i).hi - parent.lo)) + 2 ≤ B)
    (hradius : Nat.size (6 * b) + 2 ≤ B)
    (he : ∀ states ∈ actions, ∀ i, Nat.size (states i).lo + 2 ≤ B ∧
      Nat.size (states i).hi + 2 ≤ B)
    (hv : ∀ states ∈ actions, ∀ i, (child i (states i)).width ≤ B) :
    (representativeFromActionsWithWork parent r sourceLength b tau theta child actions).2 ≤
      representativeCompleteBitBudget M actions.length B := by
  let S := representativeGuardInputBudget M actions.length B
  have hBS : B ≤ S := by dsimp only [S, representativeGuardInputBudget]; omega
  have hS : 2 ≤ S := by dsimp only [S, representativeGuardInputBudget]; omega
  have hMS : M ≤ S := by dsimp only [S, representativeGuardInputBudget]; omega
  have hnS : actions.length ≤ S := by dsimp only [S, representativeGuardInputBudget]; omega
  apply representativeFromActionsWithWork_cost parent r sourceLength b tau theta child actions B
    (bandPredicateBitBudget M S (S ^ prefixArithmeticDegree)) htau hsourceLength hrl hrh he hv
  intro hne velocity hvelocity states hstates
  apply bandPredicateWithWork_cost parent r b tau theta velocity actions hne child states S
    (S ^ prefixArithmeticDegree) hstates (htau.trans hBS) (htheta.trans hBS)
    (hvelocity.trans (by dsimp only [S, representativeGuardInputBudget]; omega))
    (hb.trans hBS) (hM.trans hBS) (hrl.trans hBS) (hrh.trans hBS) (hp.trans hBS)
    (fun i => ⟨(hsource i).1.trans hBS, (hsource i).2.trans hBS⟩)
    (fun i => ⟨(hanchor i).1.trans hBS, (hanchor i).2.trans hBS⟩)
    (hradius.trans hBS)
    (fun a ha i => ⟨(he a ha i).1.trans hBS, (he a ha i).2.trans hBS⟩)
    (fun a ha i => (hv a ha i).trans hBS)
  intro j
  exact (prefix_guard_budgets_le_fixed_power M j.val actions.length S S hS hMS
    (j.isLt.le.trans hMS) hnS le_rfl).2.2.2.2.1

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryWideGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Actual wide-action materialization starts from binary balanced cuts and
bounded endpoint grids. The Cartesian-product routine receives the lists
just computed, so their construction is included in the counter. -/

namespace EditApproximation



theorem wideActionGridWithWork_cost {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P C : ℕ) (hP : 0 < P)
    (hc : ∀ i : Fin M, (wideChildGridWithWork parent r b P i).2 ≤ C) :
    (wideActionGridWithWork M parent r b P).2 ≤
      M * (C + 6) + (M + 1) * (6 * M + 10) * ((40 * P + 2) ^ 2 + 1) ^ (M + 1) + 1 := by
  let choices := vectorMapWithWork M (wideChildGridWithWork parent r b P)
  have hm := BinaryFraction.vectorMapWithWork_cost_le M (wideChildGridWithWork parent r b P) C hc
  have hchoice (i : Fin M) : (choices.1.get i).length ≤ (40 * P + 2) ^ 2 := by
    simp only [choices, vectorMapWithWork_value, wideChildGridWithWork_value _ _ _ _ _ hP]
    exact wideChildStateList_length_le parent r hP i
  have hp := materializedAssignmentsWithWork_cost M ((40 * P + 2) ^ 2) choices.1.get hchoice
  change choices.2 ≤ _ at hm
  change choices.2 + (materializedAssignmentsWithWork M choices.1.get).2 + 1 ≤ _
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryWideGridWork
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedRepresentativeWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete representative work, with every endpoint grid construction
and every score/prefix predicate charged. Only input word bounds occur. -/

namespace EditApproximation
namespace BinaryFraction

theorem wideActionGridWithWork_complete_cost {nx ny : ℕ} (M : ℕ)
    (parent : TargetInterval nx) (center : TargetInterval ny) (b P B : ℕ)
    (hPpos : 0 < P) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (hM : Nat.size M ≤ B) (hb : Nat.size b ≤ B) (hP : Nat.size P ≤ B) :
    (wideActionGridWithWork M parent center b P).2 ≤ wideMaterializationBitBudget M P B :=
  wideActionGridWithWork_cost M parent center b P _ hPpos
    (fun i => wideChildGridWithWork_cost parent center b P B i hPpos hnx hny hM hb hP)

theorem preparedRepresentativeWithWork_complete_cost_oai {nx ny M : ℕ}
    (parent : TargetInterval nx) (center : TargetInterval ny) (b P B : ℕ)
    (hPpos : 0 < P) (tau theta : BinaryFraction)
    (child : Fin M → TargetInterval ny → BinaryFraction)
    (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (hM : Nat.size M ≤ B) (hb : Nat.size b ≤ B) (hP : Nat.size P ≤ B)
    (htau : tau.width ≤ B) (htheta : theta.width ≤ B)
    (hchild : ∀ i q, (child i q).width ≤ B) :
    (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P tau theta child).2 ≤
      wideMaterializationBitBudget M P B +
      representativeCompleteBitBudget M (wideActionGridWithWork M parent center b P).1.length (4 * B + 20) +
      (wideActionGridWithWork M parent center b P).1.length + 1 := by
  let wide := wideActionGridWithWork M parent center b P
  let C := 4 * B + 20
  have hBC : B + 5 ≤ C := by dsimp only [C]; omega
  have hcenterlo : Nat.size center.lo ≤ B :=
    (Nat.size_le_size (center.ordered.trans center.valid)).trans hny
  have hcenterhi : Nat.size center.hi ≤ B := (Nat.size_le_size center.valid).trans hny
  have hparentlo : Nat.size parent.lo ≤ B :=
    (Nat.size_le_size (parent.ordered.trans parent.valid)).trans hnx
  have hparenthi : Nat.size parent.hi ≤ B := (Nat.size_le_size parent.valid).trans hnx
  have hsource (i : Fin M) : Nat.size (sourceChild parent i).lo ≤ B ∧
      Nat.size (sourceChild parent i).hi ≤ B :=
    ⟨(Nat.size_le_size ((sourceChild parent i).ordered.trans (sourceChild parent i).valid)).trans hnx,
      (Nat.size_le_size (sourceChild parent i).valid).trans hnx⟩
  have hanchor (x : ℕ) (hx : Nat.size x ≤ B) :
      Nat.size (center.lo + (x - parent.lo)) + 2 ≤ C := by
    have hs : Nat.size (x - parent.lo) ≤ B := (Nat.size_le_size (Nat.sub_le _ _)).trans hx
    have ha := binaryNaturalAdd_size_le center.lo (x - parent.lo)
    omega
  have hradius : Nat.size (6 * b) + 2 ≤ C := by
    have hp := natural_product_bit_length 6 b
    have h6 : Nat.size 6 = 3 := by decide
    omega
  have htail := representativeFromActionsWithWork_complete_cost parent center
    (parent.hi - parent.lo) b tau theta child (wide.1.map Vector.get) C
    (by omega) (by omega)
    (by have h := (Nat.size_le_size (Nat.sub_le parent.hi parent.lo)).trans hparenthi; omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun i => ⟨by have h := (hsource i).1; omega, by have h := (hsource i).2; omega⟩)
    (fun i => ⟨hanchor _ (hsource i).1, hanchor _ (hsource i).2⟩) hradius
    (fun states _ i =>
      ⟨by have h := (Nat.size_le_size ((states i).ordered.trans (states i).valid)).trans hny; omega,
       by have h := (Nat.size_le_size (states i).valid).trans hny; omega⟩)
    (fun _ _ i => (hchild i _).trans (by omega))
  have hwide := wideActionGridWithWork_complete_cost M parent center b P B hPpos hnx hny hM hb hP
  simp only [List.length_map] at htail
  change wide.2 + (representativeFromActionsWithWork parent center (parent.hi - parent.lo)
    b tau theta child (wide.1.map Vector.get)).2 + wide.1.length + 1 ≤ _
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hwide htail) _) _

end BinaryFraction
end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_complete_cost_oai := @OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_complete_cost_oai
