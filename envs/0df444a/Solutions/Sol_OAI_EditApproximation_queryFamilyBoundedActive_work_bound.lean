-- Prove2me | solution 1 for OAI.EditApproximation.queryFamilyBoundedActive_work_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:38:08.686211+00:00
-- url     : https://prove2.me/submissions/8473af2d-3f5b-4a50-8835-0d1147433c5f

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
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_OAIQ361V3Ea002
import Definitions.Def_OAIQ361V3Ea003
import Theorems.Thm_OAI_EditApproximation_queryLocalBand_work_bound

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
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
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
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
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
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalGrid
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandInputs
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandInputWork
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
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



theorem binaryNaturalDivModWithWork_cost (n d : ℕ) :
    (binaryNaturalDivModWithWork n d).2.2 ≤
      30 * (Nat.size n + 1) * (Nat.size n + Nat.size d + 1) := by
  simpa only [binaryNaturalDivModWithWork, Nat.size_eq_bits_len] using bitDivModWithWork_cost d.bits n.bits

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGridWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Endpoint rounding executed by binary division followed by multiplication. -/

namespace EditApproximation



theorem binaryGridRoundWithWork_cost (spacing position : ℕ) :
    (binaryGridRoundWithWork spacing position).2 ≤
      60 * (Nat.size spacing + Nat.size position + 1) ^ 2 := by
  have hd := binaryNaturalDivModWithWork_cost position spacing
  have hq := (bitDivModWithWork_lengths spacing.bits position.bits).1
  have hm := bitMulWithWork_cost spacing.bits (binaryNaturalDivModWithWork position spacing).1
  change (binaryNaturalDivModWithWork position spacing).1.length = position.bits.length at hq
  simp only [Nat.size_eq_bits_len] at hq hm
  rw [hq] at hm
  change (binaryNaturalDivModWithWork position spacing).2.2 +
    (bitMulWithWork spacing.bits (binaryNaturalDivModWithWork position spacing).1).2 + 2 ≤ _
  nlinarith only [hd, hm, Nat.zero_le (Nat.size spacing), Nat.zero_le (Nat.size position)]



theorem binaryIntervalRoundWithWork_cost (spacing lo hi B : ℕ)
    (hs : Nat.size spacing ≤ B) (hl : Nat.size lo ≤ B) (hh : Nat.size hi ≤ B) :
    (binaryIntervalRoundWithWork spacing lo hi).2 ≤ 500 * (B + 1) ^ 2 := by
  have hleft := binaryGridRoundWithWork_cost spacing lo
  have hright := binaryGridRoundWithWork_cost spacing hi
  have hfirst := Nat.mul_self_le_mul_self (show Nat.size spacing + Nat.size lo + 1 ≤ 2 * B + 1 by omega)
  have hsecond := Nat.mul_self_le_mul_self (show Nat.size spacing + Nat.size hi + 1 ≤ 2 * B + 1 by omega)
  simp only [← pow_two] at hfirst hsecond
  change (binaryGridRoundWithWork spacing lo).2 + (binaryGridRoundWithWork spacing hi).2 + 1 ≤ _
  nlinarith only [hleft, hright, hfirst, hsecond, Nat.zero_le B]

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRoundedWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boolean work for the actual canonical rounding and wide-membership
tests. Interval endpoints retain their original target bound after rounding. -/

namespace EditApproximation

theorem roundStateWithWork_cost {n : ℕ} (spacing : ℕ) (hspacing : 0 < spacing)
    (q : TargetInterval n) (B : ℕ) (hs : Nat.size spacing ≤ B) (hn : Nat.size n ≤ B) :
    (roundStateWithWork spacing hspacing q).2 ≤ 500 * (B + 1) ^ 2 + 1 := by
  have h := binaryIntervalRoundWithWork_cost spacing q.lo q.hi B hs
    ((Nat.size_le_size (q.ordered.trans q.valid)).trans hn)
    ((Nat.size_le_size q.valid).trans hn)
  change (binaryIntervalRoundWithWork spacing q.lo q.hi).2 + 1 ≤ _
  omega

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryScaleGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal dyadic scales and the finite initial-cone center list, with
binary rational comparisons and bounded grid enumeration. -/

namespace EditApproximation

theorem dyadicScalesWithWork_cost (N : ℕ) :
    (dyadicScalesWithWork N).2 ≤ (Nat.size N + 1) * (Nat.size N + 9) + 2 := by
  let count := max 1 N.bits.length
  have hc : count ≤ Nat.size N + 1 := by dsimp only [count]; rw [Nat.size_eq_bits_len]; omega
  have hm := arithmeticMapWithWork_cost
    (fun e => (bitWordValue (powerTwoWord e), e + 3)) (List.range count) (count + 3) (by
      intro e he
      have h := List.mem_range.mp he
      omega)
  simp only [List.length_range] at hm
  change (arithmeticMapWithWork _ (List.range count)).2 + N.bits.length + count + 2 ≤ _
  rw [Nat.size_eq_bits_len]
  nlinarith only [hm, hc, Nat.zero_le (Nat.size N)]



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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalCells
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
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
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCellGridWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCellCentersWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
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

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryWarmupAverage
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The warmup mass used in band construction is computed from the gathered
warmup entries by a stored sum and one stored division. -/

namespace EditApproximation
namespace BinaryFraction

theorem warmupAverageWithWork_bounds (values : List BinaryFraction) (B : ℕ)
    (hv : ∀ v ∈ values, v.width ≤ B) :
    (warmupAverageWithWork values).1.width ≤ warmupAverageWordBudget values.length B ∧
      (warmupAverageWithWork values).2 ≤ warmupAverageBitBudget values.length B := by
  have hs := sumListWithWork_width values B hv
  have hc := sumListWithWork_cost values B hv
  let W := bandMassTotalStorageBudget values.length B + Nat.size values.length + 2
  have hw : (sumListWithWork values).1.width ≤ W := hs.trans (by dsimp only [W]; omega)
  have hn : (nat values.length).width ≤ W := (nat_width_le _).trans (by dsimp only [W]; omega)
  have hd := divWithWork_width_uniform (sumListWithWork values).1 (nat values.length) W hw hn
  have hdc := divWithWork_cost (sumListWithWork values).1 (nat values.length) W hw hn
  refine ⟨hd, ?_⟩
  change (sumListWithWork values).2 + (divWithWork (sumListWithWork values).1 (nat values.length)).2 +
    Nat.size values.length + 2 ≤ _
  unfold warmupAverageBitBudget
  dsimp only [W] at hdc
  simp only [Nat.add_assoc, Nat.reduceAdd] at hdc ⊢
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGatheredValues
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Finite stored-word tables for gathered earlier values. The lookup scan
and the construction of every gathered warmup mean are explicit. -/

namespace EditApproximation
namespace BinaryFraction



theorem gatheredWordLookupWithWork_value {κ : Type*} [DecidableEq κ]
    (equal : κ → κ → Bool × ℕ) (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (keys : List κ) (values : List BinaryFraction) (query : κ) :
    (gatheredWordLookupWithWork equal keys values query).1.value =
      finiteAnswerTable keys (values.map BinaryFraction.value) query := by
  induction keys generalizing values with
  | nil => simp only [gatheredWordLookupWithWork, finiteAnswerTable, nat_value, Nat.cast_zero]
  | cons key keys ih =>
    cases values with
    | nil => simp only [gatheredWordLookupWithWork, List.map_nil, finiteAnswerTable, nat_value, Nat.cast_zero]
    | cons value values =>
      simp only [gatheredWordLookupWithWork, List.map_cons, finiteAnswerTable]
      by_cases h : query = key
      · rw [ite_eq_left ((heq query key).mpr h), ite_eq_left h]
      · rw [ite_eq_right (fun hx => h ((heq query key).mp hx)), ite_eq_right h]
        exact ih values

theorem gatheredWordLookupWithWork_width {κ : Type*}
    (equal : κ → κ → Bool × ℕ) (keys : List κ) (values : List BinaryFraction) (query : κ)
    (B : ℕ) (hB : 2 ≤ B) (hvalues : ∀ value ∈ values, value.width ≤ B) :
    (gatheredWordLookupWithWork equal keys values query).1.width ≤ B := by
  induction keys generalizing values with
  | nil => exact (nat_width_le 0).trans (by simpa using hB)
  | cons key keys ih =>
    cases values with
    | nil => exact (nat_width_le 0).trans (by simpa using hB)
    | cons value values =>
      simp only [gatheredWordLookupWithWork]
      split_ifs
      · exact hvalues value List.mem_cons_self
      · exact ih values (fun v hv => hvalues v (List.mem_cons_of_mem _ hv))

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitQueryKeys
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Key tagging and finite-domain restriction preserve the adaptive
reference program. Executed key tests carry their actual Boolean cost. -/

namespace EditApproximation.BitQuery



theorem mapKeysWithWork_work {ι κ β : Type*} (f : ι → κ × ℕ)
    (program : BitQuery ι β) (oracle : κ → BinaryFraction) (readWork : κ → ℕ) :
    (mapKeysWithWork f program).work oracle readWork =
      program.work (fun key => oracle (f key).1) (fun key => (f key).2 + readWork (f key).1) := by
  induction program with
  | done result => rfl
  | charge steps next ih => exact congrArg (steps + ·) ih
  | read key next ih =>
    simp only [mapKeysWithWork, work, ih, Nat.add_assoc]



end EditApproximation.BitQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_MemoCodeWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Address generation is charged separately from binary trie traversal.
The loops visit only coordinates in a key, never the ambient key space. -/
namespace EditApproximation



 theorem naturalPairWithWork_cost (a b : ℕ) : (naturalPairWithWork a b).2 ≤ 5 := by
  unfold naturalPairWithWork
  split_ifs <;> dsimp only <;> decide



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



 theorem physicalScalarCodeWithWork_cost {M J N n exponent F Q R B : ℕ}
    (key : PhysicalScalarKey M J N n exponent F Q R B) :
    (physicalScalarCodeWithWork key).2 ≤ 5 * J + 40 := by
  rcases key with ⟨online | group, index⟩
  · have hn := physicalEntryCodeWithWork_cost (online.1.1.val, online.1.2.2)
    have ha := naturalPairWithWork_cost online.2.val.val index.val
    have hb := naturalPairWithWork_cost online.1.2.1.val
      (naturalPairWithWork online.2.val.val index.val).1
    have hc := naturalPairWithWork_cost (physicalEntryCodeWithWork (online.1.1.val, online.1.2.2)).1
      (naturalPairWithWork online.1.2.1.val (naturalPairWithWork online.2.val.val index.val).1).1
    dsimp only [physicalScalarCodeWithWork]
    omega
  · have hn := physicalNodeCodeWithWork_cost group.1.val
    have ha := naturalPairWithWork_cost index.2.1.val index.2.2.val
    have hb := naturalPairWithWork_cost index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1
    have hc := naturalPairWithWork_cost group.2.2.2.val
      (naturalPairWithWork index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1).1
    have hd := naturalPairWithWork_cost group.2.2.1.val
      (naturalPairWithWork group.2.2.2.val
        (naturalPairWithWork index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1).1).1
    have he := naturalPairWithWork_cost group.2.1.val
      (naturalPairWithWork group.2.2.1.val
        (naturalPairWithWork group.2.2.2.val
          (naturalPairWithWork index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1).1).1).1
    have hf := naturalPairWithWork_cost (physicalNodeCodeWithWork group.1.val).1
      (naturalPairWithWork group.2.1.val
        (naturalPairWithWork group.2.2.1.val
          (naturalPairWithWork group.2.2.2.val
            (naturalPairWithWork index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1).1).1).1).1
    dsimp only [physicalScalarCodeWithWork]
    omega

section Family
variable {α : Type*} {M J R : ℕ} (target : List α) (N P F exponent H Q passes copies : ℕ)



 theorem physicalFamilyCodeWithWork_cost
    (key : PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies) :
    (physicalFamilyCodeWithWork target N P F exponent H Q passes copies key).2 ≤ 5 * J + 52 := by
  have hs := physicalScalarCodeWithWork_cost key.2.2
  have hc := naturalPairWithWork_cost key.2.1.val (physicalScalarCodeWithWork key.2.2).1
  have hp := naturalPairWithWork_cost key.1.val
    (naturalPairWithWork key.2.1.val (physicalScalarCodeWithWork key.2.2).1).1
  dsimp only [physicalFamilyCodeWithWork]
  omega
end Family



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteBufferRanges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The default-zero finite buffers preserve the nonnegative bounds of
paired initial/history coordinates when the initial buffer covers them. -/

namespace EditApproximation

theorem finiteAnswerTable_nonneg {κ : Type*} [DecidableEq κ]
    (keys : List κ) (values : List ℚ) (query : κ) (hv : ∀ value ∈ values, 0 ≤ value) :
    0 ≤ finiteAnswerTable keys values query := by
  induction keys generalizing values with
  | nil => exact le_rfl
  | cons key keys ih =>
    cases values with
    | nil => exact le_rfl
    | cons value values =>
      unfold finiteAnswerTable
      split_ifs
      · exact hv value List.mem_cons_self
      · exact ih values (fun v h => hv v (List.mem_cons_of_mem _ h))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryListWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
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



theorem queryIntervalEqualWithWork_cost {n : ℕ} (a b : TargetInterval n)
    (B : ℕ) (hn : Nat.size n ≤ B) :
    (queryIntervalEqualWithWork a b).2 ≤ 16 * B + 5 := by
  have hl := naturalEqualWithWork_cost a.lo b.lo B
    ((Nat.size_le_size (a.ordered.trans a.valid)).trans hn)
    ((Nat.size_le_size (b.ordered.trans b.valid)).trans hn)
  have hh := naturalEqualWithWork_cost a.hi b.hi B
    ((Nat.size_le_size a.valid).trans hn) ((Nat.size_le_size b.valid).trans hn)
  change _ + _ + 1 ≤ _
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryCodeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Key encoding uses only a fixed number of natural-word operations.
Its word sizes and Boolean work are polynomial in the coordinate widths. -/

namespace EditApproximation

theorem queryNaturalMul_cost (a b K : ℕ) (ha : Nat.size a ≤ K) (hb : Nat.size b ≤ K) :
    (binaryNaturalMulWithWork a b).2 ≤ 20 * (K + 1) * (2 * K + 1) := by
  apply (binaryNaturalMulWithWork_cost a b).trans
  gcongr
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryScalarDispatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The physical scalar sources locate a dyadic scale by a counted scan.
The scan computes the original first index and works also for absent scales. -/

namespace EditApproximation



theorem queryNaturalIndexWithWork_cost (a B : ℕ) (ha : Nat.size a ≤ B)
    (xs : List ℕ) (hx : ∀ b ∈ xs, Nat.size b ≤ B) :
    (queryNaturalIndexWithWork a xs).2 ≤ 1 + xs.length * (8 * B + 4) := by
  induction xs with
  | nil => simp only [queryNaturalIndexWithWork, List.length_nil, Nat.zero_mul, Nat.add_zero, le_refl]
  | cons b xs ih =>
    have hc := naturalEqualWithWork_cost a b B ha (hx b (by simp))
    have ht := ih (fun c hc => hx c (List.mem_cons_of_mem b hc))
    simp only [queryNaturalIndexWithWork, List.length_cons]
    split <;> dsimp only
    · nlinarith only [hc, Nat.zero_le xs.length, Nat.zero_le B]
    · nlinarith only [hc, ht]



theorem dyadicScales_size_bound (N b : ℕ) (hb : b ∈ dyadicScales N) :
    Nat.size b ≤ Nat.size N + 1 := by
  rw [← dyadicScalesWithWork_value N] at hb
  simp only [dyadicScalesWithWork, arithmeticMapWithWork_value, List.mem_map] at hb
  obtain ⟨e, he, rfl⟩ := hb
  rw [powerTwoWord_value, Nat.size_pow]
  have he' := List.mem_range.mp he
  rw [Nat.size_eq_bits_len] at he'
  omega

theorem queryScaleDispatchWithWork_cost (N b B : ℕ)
    (hN : Nat.size N ≤ B) (hb : Nat.size b ≤ B) :
    (queryScaleDispatchWithWork N b).2 ≤ 20 * (B + 2) ^ 2 := by
  have hs := dyadicScalesWithWork_cost N
  have hl : (dyadicScalesWithWork N).1.length ≤ B + 1 := by
    simp only [dyadicScalesWithWork, arithmeticMapWithWork_value, List.length_map, List.length_range]
    rw [Nat.size_eq_bits_len]
    omega
  have hi := queryNaturalIndexWithWork_cost b (B + 1) (by omega) (dyadicScalesWithWork N).1
    (fun c hc => (dyadicScales_size_bound N c (by simpa only [dyadicScalesWithWork_value] using hc)).trans (by omega))
  change (dyadicScalesWithWork N).2 + (queryNaturalIndexWithWork b (dyadicScalesWithWork N).1).2 +
    (dyadicScalesWithWork N).1.length + 2 ≤ _
  nlinarith only [hs, hi, hl, hN, Nat.zero_le B]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryFamilyScalarReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Counted pass/copy indexing for the independent scalar family.  Both
remainders and the complete family address are computed before lookup. -/

namespace EditApproximation



theorem queryFinOfNatWithWork_cost (bound value B : ℕ) (hb : 0 < bound)
    (hbound : Nat.size bound ≤ B) (hvalue : Nat.size value ≤ B) :
    (queryFinOfNatWithWork bound value hb).2 ≤ 60 * (B + 1) ^ 2 + 1 := by
  have h := binaryNaturalDivModWithWork_cost value bound
  change (binaryNaturalDivModWithWork value bound).2.2 + 1 ≤ _
  nlinarith only [h, hbound, hvalue, Nat.zero_le B]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInitialGather
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The first adaptive gather executes its binary support construction
after reading the parent value, then requests those keys in their original
order. Its continuation receives only the stored words actually read. -/

namespace EditApproximation



theorem queryInitialGather_work {ι β : Type*} {n : ℕ}
    (N P F exponent : ℕ) (hP : 0 < P) (a : BinaryFraction) (q : TargetInterval n)
    (reader : TargetInterval n → BitQuery ι BinaryFraction)
    (next : List (TargetInterval n) → List BinaryFraction → BitQuery ι β)
    (oracle : ι → BinaryFraction) (readWork : ι → ℕ) :
    let value := (reader q).value oracle
    let support := BinaryFraction.queryInitialSupportWithWork N P F exponent hP a value q
    (queryInitialGather N P F exponent hP a q reader next).work oracle readWork =
      (reader q).work oracle readWork + support.2 +
      (support.1.map fun key => (reader key).work oracle readWork + 3).sum +
      (next support.1 (support.1.map fun key => (reader key).value oracle)).work oracle readWork := by
  simp only [queryInitialGather, BitQuery.work_bind, BitQuery.compute,
    BitQuery.work, BitQuery.value, BitQuery.work_collect, Nat.add_zero, Nat.add_assoc]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySourceBuffers
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Source words are decoded only by counted buffer lookups, natural
floor and remainder routines. The resulting draws are exactly the draws
used by the semantic adaptive query, for every stored answer list. -/

namespace EditApproximation



namespace BinaryFraction



@[simp] theorem queryOnlineIntegerReadWithWork_value {n : ℕ} (keys : List (ℕ × TargetInterval n))
    (values : List BinaryFraction) (b : ℕ) (q : TargetInterval n) :
    (queryOnlineIntegerReadWithWork keys values b q).1 =
      ⌊finiteAnswerTable keys (values.map value) (b, q)⌋₊ := by
  simp only [queryOnlineIntegerReadWithWork, naturalFloorWithWork_value,
    gatheredWordLookupWithWork_value _ queryOnlineKeyEqualWithWork_value]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryDataBuffers
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Counted local data buffers for the adaptive gathers. Bounds depend on
stored keys and the requested key, not on an unbounded ambient key type. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem queryChildReadWithWork_value {M n : ℕ}
    (keys : List (Fin M × TargetInterval n)) (values : List BinaryFraction)
    (i : Fin M) (q : TargetInterval n) :
    (queryChildReadWithWork keys values i q).1.value =
      finiteAnswerTable keys (values.map value) (i, q) :=
  gatheredWordLookupWithWork_value _ coordinateEqualWithWork_value keys values (i, q)



@[simp] theorem queryHistoryReadWithWork_value {M n : ℕ}
    (keys : List (Fin M × ℕ × TargetInterval n)) (values : List BinaryFraction)
    (s : ℕ) (input : Fin M × TargetInterval n) :
    (queryHistoryReadWithWork keys values s input).1.value =
      finiteAnswerTable keys (values.map value) (input.1, s, input.2) :=
  gatheredWordLookupWithWork_value _ queryHistoryEqualWithWork_value keys values (input.1, s, input.2)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalBuffers
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Finite reader budgets for the executable adaptive program. These
uniform bounds follow from stored-key widths, regardless of answer values. -/

namespace EditApproximation.BinaryFraction



@[simp] theorem queryParentReadWithWork_value {n : ℕ} (keys : List (TargetInterval n))
    (words : List BinaryFraction) (r : TargetInterval n) :
    (queryParentReadWithWork keys words r).1.value = finiteAnswerTable keys (words.map value) r :=
  gatheredWordLookupWithWork_value _ queryIntervalEqualWithWork_value keys words r

theorem queryParentReadWithWork_cost {n : ℕ} (keys : List (TargetInterval n))
    (words : List BinaryFraction) (r : TargetInterval n) :
    (queryParentReadWithWork keys words r).2 ≤ 1 + keys.length * (16 * Nat.size n + 6) := by
  exact gatheredWordLookupWithWork_cost queryIntervalEqualWithWork (16 * Nat.size n + 5)
    (fun a b => queryIntervalEqualWithWork_cost a b _ le_rfl) keys words r

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryMeanRead
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Counted averaging of the warmup words actually requested. The fixed
requested denominator is retained even in the simulation of arbitrary
intermediate answer lists. -/

namespace EditApproximation
namespace BinaryFraction



theorem queryMeanWithWork_eq_average (count : ℕ) (words : List BinaryFraction)
    (h : words.length = count) : queryMeanWithWork count words = warmupAverageWithWork words := by
  subst count
  rfl

end BinaryFraction



theorem queryMeanRead_work {ι : Type*} (count : ℕ)
    (reader : Fin count → BitQuery ι BinaryFraction)
    (oracle : ι → BinaryFraction) (readWork : ι → ℕ) :
    (queryMeanRead count reader).work oracle readWork =
      count + 1 + ((List.ofFn fun i : Fin count => i).map
        (fun i => (reader i).work oracle readWork + 3)).sum +
      (BinaryFraction.queryMeanWithWork count
        ((List.ofFn fun i : Fin count => i).map fun i => (reader i).value oracle)).2 := by
  simp only [queryMeanRead, BitQuery.work_collect, BitQuery.compute, BitQuery.work,
    Nat.add_zero, Nat.add_assoc]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryPhysicalReaders
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Actual ranked physical reads for the charged local program.  Table
addresses are constructed before lookup, mass reads execute their mean,
and the total history reader executes its natural-word guard. -/

namespace EditApproximation



theorem queryPhysicalTableRead_work {M J n : ℕ} (copies T S : ℕ)
    (parent : PhysicalTableRequest M J n)
    (child : {r : PhysicalTableRequest M J n // r.combinedRank T S < parent.combinedRank T S})
    (oracle : {r : PhysicalTableRequest M J n // r.combinedRank T S < parent.combinedRank T S} → BinaryFraction)
    (readWork : {r : PhysicalTableRequest M J n // r.combinedRank T S < parent.combinedRank T S} → ℕ) :
    (queryPhysicalTableRead copies T S parent child).work oracle readWork ≤
      7 * J + 30 + readWork child := by
  have h := physicalTableCodeWithWork_cost copies T S child.val
  change _ + 1 + (readWork child + 0) ≤ _
  omega



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryPhysicalScalarCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bit costs for the three physical source guards.  Bounds
use only the words in the request, not the size of the ambient source set. -/

namespace EditApproximation

theorem queryScalePresentWithWork_cost (N b B : ℕ)
    (hN : Nat.size N ≤ B) (hb : Nat.size b ≤ B) :
    (queryScalePresentWithWork N b).2 ≤ 40 * (B + 2) ^ 2 := by
  have hs := queryScaleDispatchWithWork_cost N b B hN hb
  have hl : (dyadicScales N).length ≤ B + 1 := by
    rw [← dyadicScalesWithWork_value N]
    simp only [dyadicScalesWithWork, arithmeticMapWithWork_value, List.length_map, List.length_range]
    rw [Nat.size_eq_bits_len]
    omega
  have hi : (queryScaleDispatchWithWork N b).1 ≤ B + 1 := by
    rw [queryScaleDispatchWithWork_value]
    exact (List.idxOf_le_length (a := b) (l := dyadicScales N)).trans hl
  have hidx : Nat.size (queryScaleDispatchWithWork N b).1 ≤ B + 1 :=
    Nat.size_le.mpr (hi.trans_lt Nat.lt_two_pow_self)
  have hc : max 1 N.bits.length ≤ B + 1 := by
    rw [Nat.size_eq_bits_len]
    omega
  have hlen : Nat.size (max 1 N.bits.length) ≤ B + 1 :=
    Nat.size_le.mpr (hc.trans_lt Nat.lt_two_pow_self)
  have ht := binaryNaturalCompareWithWork_cost (queryScaleDispatchWithWork N b).1 (max 1 N.bits.length)
  change (queryScaleDispatchWithWork N b).2 +
    (binaryNaturalCompareWithWork (queryScaleDispatchWithWork N b).1 (max 1 N.bits.length)).2 + 2 ≤ _
  nlinarith only [hs, ht, hidx, hlen, Nat.zero_le B]

theorem queryRangeValidWithWork_cost (bound range B : ℕ)
    (hb : Nat.size bound ≤ B) (hr : Nat.size range ≤ B) :
    (queryRangeValidWithWork bound range).2 ≤ 12 * B + 5 := by
  have hp := binaryNaturalCompareWithWork_cost 0 range
  have hu := wordLEWithWork_cost range.bits bound.bits
  simp only [Nat.size_zero] at hp
  simp only [Nat.size_eq_bits_len] at hu
  change _ + _ + 2 ≤ _
  omega

theorem queryCellValidWithWork_cost (n exponent B : ℕ) (cell : ℕ × ℕ)
    (hn : Nat.size n ≤ B) (he : exponent + 1 ≤ B)
    (hl : Nat.size cell.1 ≤ B) (hr : Nat.size cell.2 ≤ B) :
    (queryCellValidWithWork n exponent cell).2 ≤ 100 * (B + 1) ^ 2 := by
  have hp : Nat.size (bitWordValue (powerTwoWord exponent)) ≤ B := by
    rw [powerTwoWord_value, Nat.size_pow]
    exact he
  have hm := queryNaturalMul_cost n (bitWordValue (powerTwoWord exponent)) B hn hp
  have hlength := bitMulWithWork_length n.bits (bitWordValue (powerTwoWord exponent)).bits
  change (binaryNaturalMulWithWork n (bitWordValue (powerTwoWord exponent))).1.length ≤ _ at hlength
  simp only [Nat.size_eq_bits_len] at hlength
  have hleft := wordLEWithWork_cost cell.1.bits
    (binaryNaturalMulWithWork n (bitWordValue (powerTwoWord exponent))).1
  have hright := wordLEWithWork_cost cell.2.bits
    (binaryNaturalMulWithWork n (bitWordValue (powerTwoWord exponent))).1
  simp only [Nat.size_eq_bits_len] at hleft hright
  change (binaryNaturalMulWithWork n (bitWordValue (powerTwoWord exponent))).2 +
    (wordLEWithWork cell.1.bits (binaryNaturalMulWithWork n (bitWordValue (powerTwoWord exponent))).1).2 +
    (wordLEWithWork cell.2.bits (binaryNaturalMulWithWork n (bitWordValue (powerTwoWord exponent))).1).2 +
    exponent + 4 ≤ _
  nlinarith only [hm, hlength, hleft, hright, hn, hp, hl, hr, he, Nat.zero_le B]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryPhysicalSourceCosts
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete execution costs of guarded scalar source queries, including
the actual finite address construction and the source lookup. -/

namespace EditApproximation

section Scalar
variable (M J N n exponent F Q R B : ℕ)
  (oracle : PhysicalScalarKey M J N n exponent F Q R B → BinaryFraction)
  (readWork : PhysicalScalarKey M J N n exponent F Q R B → ℕ)
  (W : ℕ) (hW : ∀ key, readWork key ≤ W)

include hW in
theorem queryPhysicalScalarRead_work (key : PhysicalScalarKey M J N n exponent F Q R B) :
    (queryPhysicalScalarRead M J N n exponent F Q R B key).work oracle readWork ≤ 5 * J + 41 + W := by
  have hc := physicalScalarCodeWithWork_cost key
  have hw := hW key
  change _ + 1 + (readWork key + 0) ≤ _
  omega

private theorem queryGroup_cost_transport (b c : ℕ) (h : b = c)
    (actual : BitPhysicalGroupQueries M J N n exponent F Q R B b)
    (K : ℕ) (he : ∀ scale sample, (actual scale sample).work oracle readWork ≤ K) :
    ∀ scale sample,
      ((Eq.mp (congrArg (BitPhysicalGroupQueries M J N n exponent F Q R B) h) actual)
        scale sample).work oracle readWork ≤ K := by
  subst c
  exact he

include hW in
theorem queryPhysicalScalarGroupRead_work (node : PhysicalInternalNode M J) (time : Fin R)
    (key : GroupScalarKey M F Q) :
    (queryPhysicalScalarGroupRead M J N n exponent F Q R B node time key).work oracle readWork ≤
      (queryScalePresentWithWork N key.1.1).2 + (queryCellValidWithWork n exponent key.1.2).2 +
        5 * J + 43 + W := by
  have hc : (queryPhysicalScalarGroupQueries M J N n exponent F Q R B node time
      key.1.1 key.1.2 key.2.1 key.2.2).work oracle readWork ≤ 5 * J + 41 + W := by
    unfold queryPhysicalScalarGroupQueries
    split_ifs with hb hcell
    · exact queryGroup_cost_transport M J N n exponent F Q R B oracle readWork _ _
        (physicalScaleIndex_get N key.1.1 ((queryScalePresentWithWork_value N key.1.1).mp hb))
        _ (5 * J + 41 + W)
        (fun _ _ => queryPhysicalScalarRead_work M J N n exponent F Q R B oracle readWork W hW _)
        key.2.1 key.2.2
    · exact Nat.zero_le _
    · exact Nat.zero_le _
  change _ + _ ≤ _
  omega

include hW in
theorem queryPhysicalScalarOnlineRead_work (node : PhysicalInternalNode M J) (time : Fin R)
    (key : ℕ × TargetInterval n) (range : ℕ) :
    (queryPhysicalScalarOnlineRead M J N n exponent F Q R B node time key range).work oracle readWork ≤
      (queryScalePresentWithWork N key.1).2 + (queryRangeValidWithWork B range).2 + 5 * J + 43 + W := by
  unfold queryPhysicalScalarOnlineRead
  simp only [BitQuery.work]
  split_ifs
  · apply (Nat.add_le_add_left
      (queryPhysicalScalarRead_work M J N n exponent F Q R B oracle readWork W hW _) _).trans
    omega
  · simp only [BitQuery.work]; omega
  · simp only [BitQuery.work]; omega

end Scalar
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryFamilySourceCosts
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Family
variable {α : Type*} {M J R : ℕ} (target : List α)
  (N P F exponent H Q passes copies pass copy : ℕ)

theorem queryFamilyTagWithWork_cost (B : ℕ)
    (hp : Nat.size pass ≤ B) (hc : Nat.size copy ≤ B)
    (hps : Nat.size (passes + 1) ≤ B) (hcs : Nat.size (copies + 1) ≤ B)
    (scalar : PhysicalScalarKey M J N target.length exponent F Q R (localOnlineMassBound M P H)) :
    (queryFamilyTagWithWork target N P F exponent H Q passes copies pass copy scalar).2 ≤
      120 * (B + 1) ^ 2 + 5 * J + 55 := by
  have h1 := queryFinOfNatWithWork_cost (passes + 1) pass B (Nat.succ_pos _) hps hp
  have h2 := queryFinOfNatWithWork_cost (copies + 1) copy B (Nat.succ_pos _) hcs hc
  have h3 := physicalFamilyCodeWithWork_cost target N P F exponent H Q passes copies
    ((queryFinOfNatWithWork (passes + 1) pass (Nat.succ_pos _)).1,
      (queryFinOfNatWithWork (copies + 1) copy (Nat.succ_pos _)).1, scalar)
  change (queryFinOfNatWithWork (passes + 1) pass (Nat.succ_pos _)).2 +
    (queryFinOfNatWithWork (copies + 1) copy (Nat.succ_pos _)).2 + _ + 1 ≤ _
  omega

variable
  (oracle : PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies → BinaryFraction)
  (readWork : PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies → ℕ)
  (K W : ℕ)
  (hK : ∀ scalar : PhysicalScalarKey M J N target.length exponent F Q R (localOnlineMassBound M P H),
    (queryFamilyTagWithWork target N P F exponent H Q passes copies pass copy scalar).2 ≤ K)
  (hW : ∀ key, readWork key ≤ W)

include hK hW in
theorem queryFamilyGroupRead_work (node : PhysicalInternalNode M J) (time : Fin R)
    (key : GroupScalarKey M F Q) :
    (queryFamilyGroupRead target N P F exponent H Q passes copies pass copy node time key).work
      oracle readWork ≤ (queryScalePresentWithWork N key.1.1).2 +
        (queryCellValidWithWork target.length exponent key.1.2).2 + 5 * J + 43 + (K + W) := by
  unfold queryFamilyGroupRead
  rw [BitQuery.mapKeysWithWork_work]
  apply queryPhysicalScalarGroupRead_work
  intro scalar
  exact Nat.add_le_add (hK scalar) (hW _)

include hK hW in
theorem queryFamilyOnlineRead_work (node : PhysicalInternalNode M J) (time : Fin R)
    (key : ℕ × TargetInterval target.length) (range : ℕ) :
    (queryFamilyOnlineRead target N P F exponent H Q passes copies pass copy node time key range).work
      oracle readWork ≤ (queryScalePresentWithWork N key.1).2 +
        (queryRangeValidWithWork (localOnlineMassBound M P H) range).2 + 5 * J + 43 + (K + W) := by
  unfold queryFamilyOnlineRead
  rw [BitQuery.mapKeysWithWork_work]
  apply queryPhysicalScalarOnlineRead_work
  intro scalar
  exact Nat.add_le_add (hK scalar) (hW _)

end Family
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryGridCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A scale guard bounds the number of grid points even when the center
radius is as large as the input.  These bounds include construction of
all points, before subsequent eligibility filtering. -/

namespace EditApproximation

theorem queryGridSpacing_count (P b radius K : ℕ) (hP : 0 < P) (hr : radius ≤ K * b) :
    2 * radius / seedGridSpacing b P + 2 ≤ 4 * K * P + 2 := by
  have hg : 0 < seedGridSpacing b P := by unfold seedGridSpacing; omega
  have hq : b / P ≤ seedGridSpacing b P := le_max_right _ _
  have hdiv := Nat.lt_mul_div_succ b hP
  have hb : b ≤ 2 * P * seedGridSpacing b P := by nlinarith only [hq, hdiv, hg]
  have hn : 2 * radius ≤ 4 * K * P * seedGridSpacing b P := by
    nlinarith only [hr, Nat.mul_le_mul_left (2 * K) hb]
  have hfloor := Nat.div_mul_le_self (2 * radius) (seedGridSpacing b P)
  nlinarith only [hfloor, hn, hg]

theorem queryGridPointsWithWork_bounds {n : ℕ} (P b radius K B : ℕ) (q : TargetInterval n)
    (hP : 0 < P) (hPb : Nat.size P ≤ B) (hb : Nat.size b ≤ B)
    (hr : Nat.size radius ≤ B) (hn : Nat.size n ≤ B) (hcount : radius ≤ K * b) :
    (queryGridPointsWithWork P b radius q).1.length ≤ (4 * K * P + 2) ^ 2 ∧
    (queryGridPointsWithWork P b radius q).2 ≤ queryGridPointsBitBudget P K B := by
  let spacing := seedGridSpacingWithWork b P
  have hs := seedGridSpacingWithWork_bounds b P B hb hPb
  have hp := seedGridSpacingWithWork_pos b P hP
  have hsp : Nat.size (bitWordValue spacing.1) ≤ B + 1 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length spacing.1)).trans hs.1
  have hc := queryGridSpacing_count P b radius K hP hcount
  have hv : bitWordValue spacing.1 = seedGridSpacing b P := seedGridSpacingWithWork_value b P hP
  have hgc := gridStateBoxWithWork_cost n (bitWordValue spacing.1) radius q.lo q.hi (B + 1)
    hp (by omega) hsp (by omega)
    ((Nat.size_le_size (q.ordered.trans q.valid)).trans (by omega))
    ((Nat.size_le_size q.valid).trans (by omega))
  rw [hv] at hgc
  have hgc' := hgc.trans (gridStateBoxBitBudget_mono_count _ _ (B + 1) hc)
  have hlength : (gridStateBoxWithWork n (bitWordValue spacing.1) radius q.lo q.hi).1.length ≤
      (4 * K * P + 2) ^ 2 := by
    rw [gridStateBoxWithWork_value _ _ _ _ _ hp, hv]
    exact (localTargetStates_length_le (by unfold seedGridSpacing; omega) q).trans
      (Nat.pow_le_pow_left hc 2)
  have hcost : spacing.2 +
      (gridStateBoxWithWork n (bitWordValue spacing.1) radius q.lo q.hi).2 + 1 ≤
      queryGridPointsBitBudget P K B := by
    rw [hv]
    exact Nat.add_le_add_right (Nat.add_le_add hs.2 hgc') 1
  simpa only [queryGridPointsWithWork, spacing] using And.intro hlength hcost

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryRawCenterCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete work of scale enumeration and unfiltered center construction.
Quadratic duplicate removal is bounded by the actual local grid sizes. -/

namespace EditApproximation.BinaryFraction

theorem queryScalesWithWork_bounds (N F B : ℕ) (a value : BinaryFraction)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (ha : a.width ≤ B) (hv : value.width ≤ B) :
    (queryScalesWithWork N F a value).1.length ≤ B + 1 ∧
    (queryScalesWithWork N F a value).2 ≤ queryScalesBitBudget B := by
  let exponents := queryExponentsWithWork N F a value
  have he := queryExponentsWithWork_bounds N F B a value hB hN hF ha hv
  have hc := arithmeticMapWithWork_cost (fun e => (bitWordValue (powerTwoWord e), e + 3))
    exponents.1 (B + 3) (by
      intro e he
      change e ∈ (queryExponentsWithWork N F a value).1 at he
      simp only [queryExponentsWithWork, filterWithWork_value] at he
      have hr := List.mem_range.mp (List.mem_filter.mp he).1
      rw [Nat.size_eq_bits_len] at hr
      change e + 3 ≤ B + 3
      omega)
  constructor
  · simpa only [queryScalesWithWork, arithmeticMapWithWork_value, List.length_map] using he.2
  · have hm := hc.trans (Nat.mul_le_mul_right _ he.2)
    change exponents.2 +
      (arithmeticMapWithWork (fun e => (bitWordValue (powerTwoWord e), e + 3)) exponents.1).2 + 1 ≤ _
    dsimp only [queryScalesBitBudget]
    simp only [Nat.add_assoc, Nat.reduceAdd] at hm
    have hex : exponents.2 ≤ queryExponentsBitBudget B := he.1
    omega

theorem queryScalesWithWork_member (N F B : ℕ) (a value : BinaryFraction)
    (hN : Nat.size N ≤ B) (hF : 1 ≤ F) (b : ℕ)
    (hb : b ∈ (queryScalesWithWork N F a value).1) :
    Nat.size b ≤ B + 1 ∧ ⌈value.value⌉₊ ≤ (16 * F) * b := by
  rw [queryScalesWithWork_value] at hb
  obtain ⟨hdyadic, hguard⟩ := List.mem_filter.mp hb
  have hguard' := of_decide_eq_true hguard
  refine ⟨(dyadicScales_size_bound N b hdyadic).trans (by omega), ?_⟩
  apply Nat.ceil_le.mpr
  have hp : (0 : ℚ) < 16 * F := by
    have hf : (0 : ℚ) < F := by exact_mod_cast (show 0 < F by omega)
    positivity
  have h := (div_le_iff₀ hp).mp hguard'.1
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_comm] using h

theorem queryRawCentersWithWork_bounds {n : ℕ} (N P F B : ℕ)
    (a value : BinaryFraction) (q : TargetInterval n)
    (hB : 8 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hP : 0 < P) (hPb : Nat.size P ≤ B) (hn : Nat.size n ≤ B)
    (ha : a.width ≤ B) (hv : value.width ≤ B) :
    (queryRawCentersWithWork N P F a value q).1.length ≤ (B + 1) * (64 * F * P + 2) ^ 2 ∧
    (queryRawCentersWithWork N P F a value q).2 ≤ queryRawCentersBitBudget P F B := by
  let scales := queryScalesWithWork N F a value
  let radius := naturalCeilingWithWork value
  let run := fun b => queryGridPointsWithWork P b (bitWordValue radius.1) q
  let centers := arithmeticFlatMapWithWork run scales.1
  let L := (64 * F * P + 2) ^ 2
  let count := (B + 1) * L
  have hs := queryScalesWithWork_bounds N F B a value (by omega) hN hF ha hv
  have hr : Nat.size (bitWordValue radius.1) ≤ B + 2 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length radius.1)).trans
      ((naturalCeilingWithWork_length value).trans (by omega))
  have hrun (b : ℕ) (hb : b ∈ scales.1) :
      (run b).1.length ≤ L ∧ (run b).2 ≤ queryGridPointsBitBudget P (16 * F) (B + 2) := by
    have hm := queryScalesWithWork_member N F B a value hN hFpos b hb
    have hc : bitWordValue radius.1 ≤ (16 * F) * b := by
      rw [naturalCeilingWithWork_value]
      exact hm.2
    have hg := queryGridPointsWithWork_bounds P b (bitWordValue radius.1) (16 * F) (B + 2) q
      hP (by omega) (by omega) hr (by omega) hc
    simpa only [run, L, show 4 * (16 * F) * P = 64 * F * P by ring] using hg
  have hl := arithmeticFlatMapWithWork_length run scales.1 L (fun b hb => (hrun b hb).1)
  have hw := arithmeticFlatMapWithWork_cost run scales.1
    (queryGridPointsBitBudget P (16 * F) (B + 2)) L
    (fun b hb => (hrun b hb).2) (fun b hb => (hrun b hb).1)
  have hl' : centers.1.length ≤ count := hl.trans (Nat.mul_le_mul_right L hs.1)
  have hw' := hw.trans (Nat.mul_le_mul_right _ hs.1)
  change centers.2 ≤ (B + 1) * (queryGridPointsBitBudget P (16 * F) (B + 2) + L + 3) at hw'
  have he := queryEraseWithWork_cost queryIntervalEqualWithWork (16 * B + 5)
    (fun r s => queryIntervalEqualWithWork_cost r s B hn) centers.1
  have he' := he.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.add_le_add_right hl' 1) 2))
  rw [show 16 * B + 5 + 4 = 16 * B + 9 by omega] at he'
  have hu := (queryEraseWithWork_length queryIntervalEqualWithWork centers.1).trans hl'
  have hrad := (naturalCeilingWithWork_cost value).trans
    (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (Nat.add_le_add_right hv 1) 2))
  refine ⟨hu, ?_⟩
  change scales.2 + radius.2 + centers.2 +
    (queryEraseWithWork queryIntervalEqualWithWork centers.1).2 + 3 ≤ _
  change _ ≤ queryScalesBitBudget B + 500 * (B + 1) ^ 2 +
    (B + 1) * (queryGridPointsBitBudget P (16 * F) (B + 2) + L + 3) +
    (count + 1) ^ 2 * (16 * B + 9) + 3
  have hsc : scales.2 ≤ queryScalesBitBudget B := hs.2
  change radius.2 ≤ _ at hrad
  omega

end EditApproximation.BinaryFraction

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryGroupKeyCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Size, construction work and coordinate widths of the actual group
key list, including the binary dyadic scale enumeration. -/

namespace EditApproximation.BinaryFraction

theorem queryGroupKeysWithWork_bounds {n : ℕ} (N F exponent B : ℕ)
    (a value : BinaryFraction) (q : TargetInterval n)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hFpos : 1 ≤ F) (he : exponent + 1 ≤ B) (hn : Nat.size n ≤ B)
    (ha : a.width ≤ B) (hv : value.width ≤ B) (hw : 0 ≤ value.value) :
    (queryGroupKeysWithWork N F exponent a value q).1.length ≤
      (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 ∧
    (queryGroupKeysWithWork N F exponent a value q).2 ≤ queryGroupKeysBitBudget F exponent B ∧
    ∀ key ∈ (queryGroupKeysWithWork N F exponent a value q).1,
      Nat.size key.1 ≤ B + 1 ∧ (∃ e : ℕ, key.1 = 2 ^ e) ∧
      Nat.size key.2.1 ≤ 16 * B + 183 ∧ Nat.size key.2.2 ≤ 16 * B + 183 := by
  let scales := queryScalesWithWork N F a value
  let radius := naturalCeilingWithWork value
  let cells := fun b => targetCellsWithWork
    (canonicalMulWithWork (inversePowerTwo exponent) (nat b)).1 (bitWordValue radius.1) q
  let run := fun b =>
    let side := canonicalMulWithWork (inversePowerTwo exponent) (nat b)
    let labeled := arithmeticMapWithWork (fun cell => ((b, cell), 1)) (cells b).1
    (labeled.1, side.2 + (cells b).2 + labeled.2 + 2)
  let L := ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  have hs := queryScalesWithWork_bounds N F B a value hB hN hF ha hv
  have hc (b : ℕ) (hb : b ∈ scales.1) :
      (cells b).1.length ≤ L ∧
      (canonicalMulWithWork (inversePowerTwo exponent) (nat b)).2 + (cells b).2 ≤
        queryCellScanBitBudget F exponent B ∧
      ∀ cell ∈ (cells b).1, Nat.size cell.1 ≤ 16 * B + 183 ∧ Nat.size cell.2 ≤ 16 * B + 183 := by
    have hm := queryScalesWithWork_member N F B a value hN hFpos b hb
    have hw' := queryScalesWithWork_window N F a value b hb
    have hbp : 1 ≤ b := by obtain ⟨e, rfl⟩ := hw'.1; exact Nat.succ_le_of_lt (Nat.two_pow_pos e)
    exact queryCellScan_bounds F b exponent B value q hFpos hbp hm.1 he hn hv hw hw'.2
  have hlen (b : ℕ) (hb : b ∈ scales.1) : (run b).1.length ≤ L := by
    simpa only [run, arithmeticMapWithWork_value, List.length_map] using (hc b hb).1
  have hwork (b : ℕ) (hb : b ∈ scales.1) :
      (run b).2 ≤ queryCellScanBitBudget F exponent B + 4 * L + 2 := by
    have hm := arithmeticMapWithWork_cost (fun cell => ((b, cell), 1)) (cells b).1 1
      (fun _ _ => le_rfl)
    have hh := hc b hb
    have hm' := hm.trans (Nat.mul_le_mul_right _ hh.1)
    change _ + _ + _ + 2 ≤ _
    simp only [Nat.reduceAdd] at hm'
    rw [Nat.mul_comm L 4] at hm'
    omega
  have hl := (arithmeticFlatMapWithWork_length run scales.1 L hlen).trans
    (Nat.mul_le_mul_right L hs.1)
  have hf := (arithmeticFlatMapWithWork_cost run scales.1
    (queryCellScanBitBudget F exponent B + 4 * L + 2) L hwork hlen).trans
      (Nat.mul_le_mul_right _ hs.1)
  have hrad := (naturalCeilingWithWork_cost value).trans
    (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (Nat.add_le_add_right hv 1) 2))
  refine ⟨hl, ?_, ?_⟩
  · change scales.2 + radius.2 + (arithmeticFlatMapWithWork run scales.1).2 + exponent + 4 ≤ _
    change _ ≤ queryScalesBitBudget B + 500 * (B + 1) ^ 2 +
      (B + 1) * (queryCellScanBitBudget F exponent B + 5 * L + 5) + exponent + 4
    rw [show queryCellScanBitBudget F exponent B + 4 * L + 2 + L + 3 =
      queryCellScanBitBudget F exponent B + 5 * L + 5 by omega] at hf
    have hsc : scales.2 ≤ queryScalesBitBudget B := hs.2
    change radius.2 ≤ _ at hrad
    omega
  · intro key hk
    change key ∈ (arithmeticFlatMapWithWork run scales.1).1 at hk
    rw [arithmeticFlatMapWithWork_value] at hk
    obtain ⟨b, hb, hk⟩ := List.mem_flatMap.mp hk
    simp only [run, arithmeticMapWithWork_value] at hk
    obtain ⟨cell, hcell, rfl⟩ := List.mem_map.mp hk
    exact ⟨(queryScalesWithWork_member N F B a value hN hFpos b hb).1,
      (queryScalesWithWork_window N F a value b hb).1, (hc b hb).2.2 cell hcell⟩

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryFamilyReaderBounds
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
section Family
variable {α : Type*} {M J R : ℕ} (target : List α)
  (N P F exponent H Q passes copies pass copy B W : ℕ)
  (oracle : PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies → BinaryFraction)
  (readWork : PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies → ℕ)
  (hN : Nat.size N ≤ B) (hp : Nat.size pass ≤ B) (hc : Nat.size copy ≤ B)
  (hps : Nat.size (passes + 1) ≤ B) (hcs : Nat.size (copies + 1) ≤ B)
  (hW : ∀ key, readWork key ≤ W)

include hN hp hc hps hcs hW in
theorem queryFamilyGroupRead_bounded_work
    (hn : Nat.size target.length ≤ B) (he : exponent + 1 ≤ B)
    (node : PhysicalInternalNode M J) (time : Fin R) (key : GroupScalarKey M F Q)
    (hk : queryGroupKeySize key ≤ 40 * B + 500) :
    (queryFamilyGroupRead target N P F exponent H Q passes copies pass copy node time key).work oracle readWork ≤
      BinaryFraction.queryFamilySourceReadBudget J B W := by
  let D := 1000 * (B + 1) + 1000
  let K := 120 * (B + 1) ^ 2 + 5 * J + 55
  have hb : B ≤ D := by dsimp only [D]; omega
  have hkey : queryGroupKeySize key ≤ D := by dsimp only [D]; omega
  have hscale := queryScalePresentWithWork_cost N key.1.1 D (hN.trans hb)
    (by unfold queryGroupKeySize at hkey; omega)
  have hcell := queryCellValidWithWork_cost target.length exponent D key.1.2
    (hn.trans hb) (he.trans hb) (by unfold queryGroupKeySize at hkey; omega)
    (by unfold queryGroupKeySize at hkey; omega)
  have hr := queryFamilyGroupRead_work target N P F exponent H Q passes copies pass copy oracle readWork K W
    (fun scalar => queryFamilyTagWithWork_cost target N P F exponent H Q passes copies pass copy B hp hc hps hcs scalar)
    hW node time key
  change _ ≤ 200 * (D + 2) ^ 2 + 120 * (B + 1) ^ 2 + 10 * J + 100 + W
  dsimp only [K] at hr
  nlinarith only [hscale, hcell, hr, Nat.zero_le D]

include hN hp hc hps hcs hW in
theorem queryFamilyOnlineRead_bounded_work
    (hbound : Nat.size (localOnlineMassBound M P H) ≤ B)
    (node : PhysicalInternalNode M J) (time : Fin R) (key : ℕ × TargetInterval target.length)
    (range : ℕ) (hk : Nat.size key.1 ≤ B + 1) (hrange : Nat.size range ≤ 240 * (B + 5) + 7) :
    (queryFamilyOnlineRead target N P F exponent H Q passes copies pass copy node time key range).work oracle readWork ≤
      BinaryFraction.queryFamilySourceReadBudget J B W := by
  let D := 1000 * (B + 1) + 1000
  let K := 120 * (B + 1) ^ 2 + 5 * J + 55
  have hb : B ≤ D := by dsimp only [D]; omega
  have hs := queryScalePresentWithWork_cost N key.1 D (hN.trans hb) (by dsimp only [D]; omega)
  have hv := queryRangeValidWithWork_cost (localOnlineMassBound M P H) range D
    (hbound.trans hb) (by dsimp only [D]; omega)
  have hr := queryFamilyOnlineRead_work target N P F exponent H Q passes copies pass copy oracle readWork K W
    (fun scalar => queryFamilyTagWithWork_cost target N P F exponent H Q passes copies pass copy B hp hc hps hcs scalar)
    hW node time key range
  change _ ≤ 200 * (D + 2) ^ 2 + 120 * (B + 1) ^ 2 + 10 * J + 100 + W
  dsimp only [K] at hr
  nlinarith only [hs, hv, hr, Nat.zero_le D]

end Family
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryOnlineKeyCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

theorem queryOnlineKeysWithWork_bounds {n : ℕ} (N P F B : ℕ) (hP : 0 < P)
    (a value : BinaryFraction) (q : TargetInterval n)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hFpos : 1 ≤ F) (hPb : Nat.size P ≤ B) (hn : Nat.size n ≤ B)
    (ha : a.width ≤ B) (hv : value.width ≤ B) :
    (queryOnlineKeysWithWork N P F hP a value q).1.length ≤ B + 1 ∧
    (queryOnlineKeysWithWork N P F hP a value q).2 ≤ queryOnlineKeysBitBudget B := by
  let scales := queryScalesWithWork N F a value
  let run := fun b =>
    let spacing := seedGridSpacingWithWork b P
    let center := roundStateWithWork (bitWordValue spacing.1) (seedGridSpacingWithWork_pos b P hP) q
    ((b, center.1), spacing.2 + center.2 + 2)
  have hs := queryScalesWithWork_bounds N F B a value hB hN hF ha hv
  have hc (b : ℕ) (hb : b ∈ scales.1) : (run b).2 ≤ 600 * (B + 3) ^ 2 + 3 := by
    have hm := queryScalesWithWork_member N F B a value hN hFpos b hb
    have hsp := seedGridSpacingWithWork_bounds b P (B + 1) hm.1 (by omega)
    have hsize : Nat.size (bitWordValue (seedGridSpacingWithWork b P).1) ≤ B + 2 :=
      (Nat.size_le.mpr (bitWordValue_lt_pow_length _)).trans hsp.1
    have hr := roundStateWithWork_cost (bitWordValue (seedGridSpacingWithWork b P).1)
      (seedGridSpacingWithWork_pos b P hP) q (B + 2) hsize (by omega)
    have hspc := hsp.2
    dsimp only [run]
    simp only [Nat.add_assoc, Nat.reduceAdd] at hspc hr
    omega
  have hm := (arithmeticMapWithWork_cost run scales.1 (600 * (B + 3) ^ 2 + 3) hc).trans
    (Nat.mul_le_mul_right _ hs.1)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hm
  constructor
  · simpa only [queryOnlineKeysWithWork, arithmeticMapWithWork_value, List.length_map] using hs.1
  · change scales.2 + (arithmeticMapWithWork run scales.1).2 + 1 ≤ _
    have hsc : scales.2 ≤ queryScalesBitBudget B := hs.2
    unfold queryOnlineKeysBitBudget
    omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryCellStateCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.queryChildReadWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryHistoryReadWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineIntegerReadWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryParentReadWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

theorem queryCellStatesWithWork_bounds (n P b exponent B : ℕ) (cell : ℕ × ℕ)
    (hP : 0 < P) (hPb : Nat.size P ≤ B) (hb : Nat.size b ≤ B + 1)
    (he : exponent + 1 ≤ B) (hn : Nat.size n ≤ B)
    (hc : Nat.size cell.1 ≤ 16 * B + 183 ∧ Nat.size cell.2 ≤ 16 * B + 183)
    (hbd : ∃ e : ℕ, b = 2 ^ e) (hPd : ∃ e : ℕ, P = 2 ^ e) :
    (queryCellStatesWithWork n P b exponent cell).1.length ≤ P ^ 2 ∧
    (queryCellStatesWithWork n P b exponent cell).2 ≤ queryCellStatesBitBudget P exponent B := by
  let spacing := seedGridSpacingWithWork b P
  let theta := inversePowerTwo exponent
  let side := canonicalMulWithWork theta (nat b)
  let states := cellStatesWithWork n (bitWordValue spacing.1) side.1 cell
  let C := 16 * B + 200
  have hsp := seedGridSpacingWithWork_bounds b P (B + 3) (by omega) (by omega)
  have hgs : Nat.size (bitWordValue spacing.1) ≤ B + 4 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length _)).trans hsp.1
  have ht : theta.width ≤ B + 3 := by dsimp only [theta]; rw [inversePowerTwo_width]; omega
  have hsw := canonicalMulWithWork_width theta (nat b) (B + 3) ht ((nat_width_le b).trans (by omega))
  have hsc := canonicalMulWithWork_cost theta (nat b) (B + 3) ht ((nat_width_le b).trans (by omega))
  have htheta : 0 ≤ theta.value ∧ theta.value ≤ 1 := by
    rw [inversePowerTwo_value]
    exact ⟨by positivity, zpow_le_one_of_nonpos₀ (by norm_num) (by omega)⟩
  have hv : side.1.value = theta.value * b := by rw [canonicalMulWithWork_value, nat_value]
  have hg : (0 : ℚ) < seedGridSpacing b P := by
    exact_mod_cast (show 0 < seedGridSpacing b P by unfold seedGridSpacing; omega)
  have hcover : (b : ℚ) ≤ P * (seedGridSpacing b P : ℚ) := by
    exact_mod_cast seedGridSpacing_covers_dyadic hbd hPd
  have hratio : theta.value * b / seedGridSpacing b P ≤ (P : ℚ) := by
    apply (div_le_iff₀ hg).2
    exact (mul_le_mul_of_nonneg_right htheta.2 (Nat.cast_nonneg b)).trans (by simpa only [one_mul] using hcover)
  have hlen (j : ℕ) : (cellGridPoints side.1.value (bitWordValue spacing.1) j).length ≤ P := by
    rw [hv, seedGridSpacingWithWork_value b P hP]
    exact cellGridPoints_length_le (mul_nonneg htheta.1 (Nat.cast_nonneg _)) hratio
  have hstate := cellStatesWithWork_cost n (bitWordValue spacing.1) C side.1 cell
    (by dsimp only [C]; omega) (by dsimp only [C]; omega)
    (by dsimp only [C]; change side.1.width ≤ _ at hsw; omega)
    (by dsimp only [C]; omega) (by dsimp only [C]; omega)
  have hstate' : states.2 ≤ cellStatesBitBudget P P C := hstate.trans (by
    unfold cellStatesBitBudget cellGridPointsBitBudget
    gcongr <;> apply hlen)
  constructor
  · have hlength := (cellStatesWithWork_length n (bitWordValue spacing.1) side.1 cell).trans
      (Nat.mul_le_mul (hlen cell.1) (hlen cell.2))
    simpa only [queryCellStatesWithWork, spacing, theta, side, states, pow_two] using hlength
  · change spacing.2 + side.2 + states.2 + exponent + 3 ≤ _
    exact Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add (Nat.add_le_add hsp.2 hsc) hstate') exponent) 3

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInitialSupportCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete initial-support gather, including repeated cells and
unfiltered raw centers, has a local-parameter bound. -/

namespace EditApproximation.BinaryFraction

theorem queryInitialSupportWithWork_bounds {n : ℕ} (N P F exponent B : ℕ) (hP : 0 < P)
    (a value : BinaryFraction) (q : TargetInterval n)
    (hB : 8 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hFpos : 1 ≤ F) (hPb : Nat.size P ≤ B) (hn : Nat.size n ≤ B)
    (he : exponent + 1 ≤ B) (ha : a.width ≤ B) (hv : value.width ≤ B)
    (hw : 0 ≤ value.value) (hPd : ∃ e : ℕ, P = 2 ^ e) :
    (queryInitialSupportWithWork N P F exponent hP a value q).1.length ≤
      queryInitialSupportLength P F exponent B ∧
    (queryInitialSupportWithWork N P F exponent hP a value q).2 ≤
      queryInitialSupportBitBudget P F exponent B := by
  let raw := queryRawCentersWithWork N P F a value q
  let groups := queryGroupKeysWithWork N F exponent a value q
  let run := fun key : ℕ × (ℕ × ℕ) => queryCellStatesWithWork n P key.1 exponent key.2
  let cells := arithmeticFlatMapWithWork run groups.1
  let online := queryOnlineKeysWithWork N P F hP a value q
  let onlineStates := arithmeticMapWithWork (fun key : ℕ × TargetInterval n => (key.2, 1)) online.1
  let R := (B + 1) * (64 * F * P + 2) ^ 2
  let G := (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  have hr := queryRawCentersWithWork_bounds N P F B a value q hB hN hF hFpos hP hPb hn ha hv
  have hg := queryGroupKeysWithWork_bounds N F exponent B a value q (by omega) hN hF hFpos he hn ha hv hw
  have ho := queryOnlineKeysWithWork_bounds N P F B hP a value q (by omega) hN hF hFpos hPb hn ha hv
  have hrun (key : ℕ × (ℕ × ℕ)) (hk : key ∈ groups.1) :
      (run key).1.length ≤ P ^ 2 ∧ (run key).2 ≤ queryCellStatesBitBudget P exponent B := by
    obtain ⟨hb, hd, hc⟩ := hg.2.2 key hk
    exact queryCellStatesWithWork_bounds n P key.1 exponent B key.2 hP hPb hb he hn hc hd hPd
  have hcl : cells.1.length ≤ G * P ^ 2 :=
    (arithmeticFlatMapWithWork_length run groups.1 (P ^ 2) (fun key hk => (hrun key hk).1)).trans
      (Nat.mul_le_mul_right _ hg.1)
  have hcw := (arithmeticFlatMapWithWork_cost run groups.1
    (queryCellStatesBitBudget P exponent B) (P ^ 2)
    (fun key hk => (hrun key hk).2) (fun key hk => (hrun key hk).1)).trans
      (Nat.mul_le_mul_right _ hg.1)
  change cells.2 ≤ G * (queryCellStatesBitBudget P exponent B + P ^ 2 + 3) at hcw
  have hom := (arithmeticMapWithWork_cost (fun key : ℕ × TargetInterval n => (key.2, 1))
    online.1 1 (fun _ _ => le_rfl)).trans (Nat.mul_le_mul_right _ ho.1)
  change onlineStates.2 ≤ (B + 1) * (1 + 3) at hom
  have hol : onlineStates.1.length ≤ B + 1 := by
    simpa only [onlineStates, arithmeticMapWithWork_value, List.length_map] using ho.1
  have hrl : raw.1.length ≤ R := hr.1
  have hrw : raw.2 ≤ queryRawCentersBitBudget P F B := hr.2
  have hgw : groups.2 ≤ queryGroupKeysBitBudget F exponent B := hg.2.1
  have how : online.2 ≤ queryOnlineKeysBitBudget B := ho.2
  constructor
  · change (q :: (raw.1 ++ cells.1 ++ onlineStates.1)).length ≤ _
    simp only [List.length_cons, List.length_append]
    change _ ≤ 1 + R + G * P ^ 2 + (B + 1)
    omega
  · change raw.2 + groups.2 + cells.2 + online.2 + onlineStates.2 +
      2 * raw.1.length + cells.1.length + 5 ≤ _
    have hr2 := Nat.mul_le_mul_left 2 hrl
    change _ ≤ queryRawCentersBitBudget P F B + queryGroupKeysBitBudget F exponent B +
      G * (queryCellStatesBitBudget P exponent B + P ^ 2 + 3) +
      queryOnlineKeysBitBudget B + 4 * (B + 1) + 2 * R + G * P ^ 2 + 5
    rw [Nat.mul_comm (B + 1) (1 + 3)] at hom
    norm_num only at hom
    omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryOuterGatherCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

private theorem outer_read_sum_bound {κ : Type*} (keys : List κ) (cost : κ → ℕ) (B : ℕ)
    (h : ∀ key ∈ keys, cost key ≤ B) : (keys.map cost).sum ≤ keys.length * B := by
  induction keys with
  | nil => simp
  | cons key keys ih =>
    have hh := h key List.mem_cons_self
    have ht := ih (fun k hk => h k (List.mem_cons_of_mem key hk))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

open BinaryFraction

theorem queryInitialGather_work_bound {ι β : Type*} {n : ℕ}
    (N P F exponent B R K : ℕ) (hP : 0 < P) (a : BinaryFraction) (q : TargetInterval n)
    (reader : TargetInterval n → BitQuery ι BinaryFraction)
    (next : List (TargetInterval n) → List BinaryFraction → BitQuery ι β)
    (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (hB : 8 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hPb : Nat.size P ≤ B) (hn : Nat.size n ≤ B) (he : exponent + 1 ≤ B) (ha : a.width ≤ B)
    (hv : ((reader q).value oracle).width ≤ B) (hw : 0 ≤ ((reader q).value oracle).value)
    (hPd : ∃ e : ℕ, P = 2 ^ e) (hR : ∀ r, (reader r).work oracle readWork ≤ R)
    (hnext :
      let keys := (queryInitialSupportWithWork N P F exponent hP a ((reader q).value oracle) q).1
      (next keys (keys.map fun r => (reader r).value oracle)).work oracle readWork ≤ K) :
    (queryInitialGather N P F exponent hP a q reader next).work oracle readWork ≤
      queryInitialGatherBitBudget P F exponent B R K := by
  let support := queryInitialSupportWithWork N P F exponent hP a ((reader q).value oracle) q
  have hs := queryInitialSupportWithWork_bounds N P F exponent B hP a ((reader q).value oracle) q
    hB hN hF hFpos hPb hn he ha hv hw hPd
  have hr := (outer_read_sum_bound support.1 (fun r => (reader r).work oracle readWork + 3) (R + 3)
    (fun r _ => Nat.add_le_add_right (hR r) 3)).trans (Nat.mul_le_mul_right _ hs.1)
  have hsc : support.2 ≤ queryInitialSupportBitBudget P F exponent B := hs.2
  change (next support.1 (support.1.map fun r => (reader r).value oracle)).work oracle readWork ≤ K at hnext
  rw [queryInitialGather_work]
  change (reader q).work oracle readWork + support.2 +
    (support.1.map fun r => (reader r).work oracle readWork + 3).sum +
    (next support.1 (support.1.map fun r => (reader r).value oracle)).work oracle readWork ≤ _
  have hq := hR q
  unfold queryInitialGatherBitBudget
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalProgramCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A complete work bound for the actual adaptive local program. Premises
are numeric parameter bounds, stored-word sizes, and the existing history
range invariant; all intermediate enumeration and scans are included. -/

namespace EditApproximation
section Program
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF B E S : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (readParent : TargetInterval target.length → BitQuery ι BinaryFraction)
  (readMass readInitial : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (oracle : ι → BinaryFraction) (readWork : ι → ℕ)

open BinaryFraction

theorem queryLocalProgram_work_bound (W : ℕ)
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E S (t - 1) tau a eta kappa delta (fun _ _ => 0))
    (htime : 0 < t) (ht : Nat.size t ≤ B) (hPd : ∃ j : ℕ, P = 2 ^ j)
    (hpW : ∀ key, ((readParent key).value oracle).width ≤ B)
    (hmW : ∀ key, ((readMass key).value oracle).width ≤ B)
    (hiW : ∀ key, ((readInitial key).value oracle).width ≤ B)
    (hgW : ∀ key, ((readGroup key).value oracle).width ≤ B)
    (hzW : ∀ key range, ((readInteger key range).value oracle).width ≤ B)
    (heW : ∀ key, ((readEarlier key).value oracle).width ≤ B)
    (hcW : ∀ key, ((readCurrent key).value oracle).width ≤ B)
    (hpN : ∀ key, 0 ≤ ((readParent key).value oracle).value)
    (hiN : ∀ key, 0 ≤ ((readInitial key).value oracle).value)
    (heN : ∀ key, 0 ≤ ((readEarlier key).value oracle).value)
    (heI : ∀ key, ((readEarlier key).value oracle).value ≤
      ((readInitial (key.1, key.2.2)).value oracle).value)
    (hpR : ∀ key, (readParent key).work oracle readWork ≤ W)
    (hmR : ∀ key, (readMass key).work oracle readWork ≤ W)
    (hiR : ∀ key, (readInitial key).work oracle readWork ≤ W)
    (hgR : ∀ key, queryGroupKeySize key ≤ 40 * B + 500 →
      (readGroup key).work oracle readWork ≤ W)
    (hzR : ∀ key range, Nat.size key.1 ≤ B + 1 → Nat.size range ≤ 240 * (B + 5) + 7 →
      (readInteger key range).work oracle readWork ≤ W)
    (heR : ∀ key, Nat.size key.2.1 ≤ B → (readEarlier key).work oracle readWork ≤ W)
    (hcR : ∀ key, (readCurrent key).work oracle readWork ≤ W) :
    (queryLocalProgram source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta t readParent readMass readInitial readGroup readInteger
      q readEarlier readCurrent).work oracle readWork ≤
      queryLocalProgramBitBudget M N P F exponent eM eF B S t W := by
  have hB : 10 ≤ B := hn.largeBits
  have hny : Nat.size target.length ≤ B := by have := hn.targetSize; omega
  have hFpos : 1 ≤ F := by rw [hF]; exact Nat.one_le_two_pow
  let keys := (queryInitialSupportWithWork N P F exponent hP a ((readParent q).value oracle) q).1
  let words := keys.map fun key => (readParent key).value oracle
  have hkeys := (queryInitialSupportWithWork_bounds N P F exponent B hP a ((readParent q).value oracle) q
    (by omega) hn.inputSize hn.factorSize hFpos hn.precisionSize hny hn.thetaSize
    hn.factorWidth (hpW q) (hpN q) hPd).1
  have hpw : ∀ w ∈ words, w.width ≤ B := by
    intro w hw
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
    exact hpW key
  have hpr : ∀ r, (queryParentReadWithWork keys words r).2 ≤ queryParentBufferReadBudget P F exponent B := by
    intro r
    apply (queryParentReadWithWork_cost keys words r).trans
    unfold queryParentBufferReadBudget
    exact Nat.add_le_add_left (Nat.mul_le_mul hkeys (by omega)) 1
  have hpn : ∀ r, 0 ≤ (queryParentReadWithWork keys words r).1.value := by
    intro r
    rw [queryParentReadWithWork_value]
    apply finiteAnswerTable_nonneg
    intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
    exact hpN key
  unfold queryLocalProgram queryLocalProgramBitBudget
  apply queryInitialGather_work_bound N P F exponent B W _ hP a q readParent _ oracle readWork
    (by omega) hn.inputSize hn.factorSize hFpos hn.precisionSize hny hn.thetaSize
    hn.factorWidth (hpW q) (hpN q) hPd hpR
  apply queryLocalBand_work_bound source target parent N P F exponent H Q eM eF B E S hP hM hF
    tau a eta kappa delta t (queryParentReadWithWork keys words) readMass readInitial readGroup readInteger
    q readEarlier readCurrent oracle readWork _ W hn htime ht hPd hpr
    (fun r => gatheredWordLookupWithWork_width _ keys words r B (by omega) hpw) hpn
    hmW hiW hgW hzW heW hcW hiN heN heI hmR hiR hgR hzR heR hcR

end Program
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryPhysicalReaderBounds
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

private theorem reader_cost_sum {κ : Type*} (keys : List κ) (cost : κ → ℕ) (C : ℕ)
    (h : ∀ key ∈ keys, cost key ≤ C) : (keys.map cost).sum ≤ keys.length * C := by
  induction keys with
  | nil => simp
  | cons key keys ih =>
    have hh := h key List.mem_cons_self
    have ht := ih (fun k hk => h k (List.mem_cons_of_mem key hk))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem queryMeanRead_bounds {ι : Type*} (count B C : ℕ)
    (reader : Fin count → BitQuery ι BinaryFraction)
    (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (hw : ∀ i, ((reader i).value oracle).width ≤ B)
    (hc : ∀ i, (reader i).work oracle readWork ≤ C) :
    ((queryMeanRead count reader).value oracle).width ≤ BinaryFraction.warmupAverageWordBudget count B ∧
      (queryMeanRead count reader).work oracle readWork ≤
        count + 1 + count * (C + 3) + BinaryFraction.warmupAverageBitBudget count B := by
  let inputs := List.ofFn fun i : Fin count => i
  let words := inputs.map fun i => (reader i).value oracle
  have hlen : words.length = count := by simp only [words, inputs, List.length_map, List.length_ofFn]
  have havg := BinaryFraction.warmupAverageWithWork_bounds words B (by
    intro w hw'
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hw'
    exact hw i)
  rw [← BinaryFraction.queryMeanWithWork_eq_average count words hlen] at havg
  rw [hlen] at havg
  have hs := reader_cost_sum inputs (fun i => (reader i).work oracle readWork + 3) (C + 3)
    (fun i _ => Nat.add_le_add_right (hc i) 3)
  simp only [inputs, List.length_ofFn] at hs
  change (inputs.map fun i => (reader i).work oracle readWork + 3).sum ≤ count * (C + 3) at hs
  constructor
  · simpa only [queryMeanRead, BitQuery.value, BitQuery.value_collect, BitQuery.compute, words, inputs] using havg.1
  · rw [queryMeanRead_work]
    change count + 1 + (inputs.map fun i => (reader i).work oracle readWork + 3).sum +
      (BinaryFraction.queryMeanWithWork count words).2 ≤ _
    omega

section Physical
variable {M J n : ℕ} (copies pass copy T S t : ℕ) (ht : 0 < t)
  (node : PhysicalNode M J) (hbelow : node.1.val < J) (q : TargetInterval n)
  (oracle : {child : PhysicalTableRequest M J n // child.combinedRank T S <
    (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} → BinaryFraction)
  (readWork : {child : PhysicalTableRequest M J n // child.combinedRank T S <
    (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} → ℕ)

theorem queryPhysicalWarmupRead_work_bound (W : ℕ) (hW : ∀ key, key.val.pass = pass → key.val.copy = copy → readWork key ≤ W)
    (other : PhysicalNode M J) (hnode : node.1.val ≤ other.1.val) (j : ℕ) (hj : j ≤ T)
    (r : TargetInterval n) :
    (queryPhysicalWarmupRead copies pass copy T S t ht node q other hnode j hj r).work oracle readWork ≤
      7 * J + 30 + W := by
  exact (queryPhysicalTableRead_work copies T S _ _ oracle readWork).trans
    (Nat.add_le_add_left (hW _ rfl rfl) _)

theorem queryPhysicalCurrentRead_work_bound (W : ℕ) (hW : ∀ key, key.val.pass = pass → key.val.copy = copy → readWork key ≤ W)
    (input : Fin M × TargetInterval n) :
    (queryPhysicalCurrentRead copies pass copy T S t node hbelow q input).work oracle readWork ≤
      7 * J + 30 + W := by
  exact (queryPhysicalTableRead_work copies T S _ _ oracle readWork).trans
    (Nat.add_le_add_left (hW _ rfl rfl) _)

theorem queryPhysicalEarlierRead_work_bound (B W : ℕ) (hW : ∀ key, key.val.pass = pass → key.val.copy = copy → readWork key ≤ W)
    (htime : Nat.size t ≤ B) (input : Fin M × ℕ × TargetInterval n) (hi : Nat.size input.2.1 ≤ B) :
    (queryPhysicalEarlierRead copies pass copy T S t node hbelow q input).work oracle readWork ≤
      8 * B + 7 * J + 32 + W := by
  have hcmp := binaryNaturalCompareWithWork_cost input.2.1 t
  have hr (child : {r : PhysicalTableRequest M J n // r.combinedRank T S <
      (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S})
      (hp : child.val.pass = pass) (hc : child.val.copy = copy) :
      (queryPhysicalTableRead copies T S _ child).work oracle readWork ≤ 7 * J + 30 + W :=
    (queryPhysicalTableRead_work copies T S _ child oracle readWork).trans
      (Nat.add_le_add_left (hW child hp hc) _)
  unfold queryPhysicalEarlierRead
  simp only [BitQuery.work]
  split
  · apply (Nat.add_le_add_left (hr _ rfl rfl) _).trans
    omega
  · simp only [BitQuery.work]
    omega

theorem queryPhysicalMassRead_bounds (B W : ℕ) (hW : ∀ key, key.val.pass = pass → key.val.copy = copy → readWork key ≤ W)
    (hw : ∀ key, (oracle key).width ≤ B) (input : Fin M × TargetInterval n) :
    ((queryPhysicalMassRead copies pass copy T S t ht node hbelow q input).value oracle).width ≤
        BinaryFraction.warmupAverageWordBudget T B ∧
      (queryPhysicalMassRead copies pass copy T S t ht node hbelow q input).work oracle readWork ≤
        T + 1 + T * (7 * J + 30 + W + 3) + BinaryFraction.warmupAverageBitBudget T B := by
  apply queryMeanRead_bounds T B (7 * J + 30 + W)
  · intro j
    exact hw _
  · intro j
    exact queryPhysicalWarmupRead_work_bound copies pass copy T S t ht node q oracle readWork W hW _ _ _ _ _

theorem queryPhysicalEarlierRead_width (B : ℕ) (hB : 2 ≤ B)
    (hw : ∀ key, (oracle key).width ≤ B) (input : Fin M × ℕ × TargetInterval n) :
    ((queryPhysicalEarlierRead copies pass copy T S t node hbelow q input).value oracle).width ≤ B := by
  unfold queryPhysicalEarlierRead
  simp only [BitQuery.value]
  split
  · exact hw _
  · exact (BinaryFraction.nat_width_le 0).trans (by simpa only [Nat.size_zero, Nat.zero_add] using hB)

theorem queryPhysicalEarlierRead_nonneg (hw : ∀ key, 0 ≤ (oracle key).value)
    (input : Fin M × ℕ × TargetInterval n) :
    0 ≤ ((queryPhysicalEarlierRead copies pass copy T S t node hbelow q input).value oracle).value := by
  unfold queryPhysicalEarlierRead
  simp only [BitQuery.value]
  split
  · exact hw _
  · simp only [BitQuery.value, BinaryFraction.nat_value, Nat.cast_zero, le_refl]

end Physical
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySourceWidths
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BitQuery

theorem mapKeysWithWork_value {ι κ β : Type*} (f : ι → κ × ℕ)
    (program : BitQuery ι β) (oracle : κ → BinaryFraction) :
    (mapKeysWithWork f program).value oracle = program.value (fun key => oracle (f key).1) := by
  induction program with
  | done result => rfl
  | charge steps next ih => exact ih
  | read key next ih => exact ih (oracle (f key).1)

end EditApproximation.BitQuery

namespace EditApproximation
section Scalar
variable (M J N n exponent F Q R B : ℕ)
  (oracle : PhysicalScalarKey M J N n exponent F Q R B → BinaryFraction)
  (V : ℕ) (hV : 2 ≤ V) (hv : ∀ key, (oracle key).width ≤ V)

private theorem group_width_transport (b c : ℕ) (h : b = c)
    (actual : BitPhysicalGroupQueries M J N n exponent F Q R B b)
    (hwidth : ∀ scale sample, ((actual scale sample).value oracle).width ≤ V) :
    ∀ scale sample,
      (((Eq.mp (congrArg (BitPhysicalGroupQueries M J N n exponent F Q R B) h) actual)
        scale sample).value oracle).width ≤ V := by
  subst c
  exact hwidth

include hV hv in
theorem queryPhysicalScalarGroupRead_width (node : PhysicalInternalNode M J) (time : Fin R)
    (key : GroupScalarKey M F Q) :
    ((queryPhysicalScalarGroupRead M J N n exponent F Q R B node time key).value oracle).width ≤ V := by
  simp only [queryPhysicalScalarGroupRead, BitQuery.value]
  unfold queryPhysicalScalarGroupQueries
  split_ifs with hb hcell
  · refine group_width_transport M J N n exponent F Q R B oracle V _ _
      (physicalScaleIndex_get N key.1.1 ((queryScalePresentWithWork_value N key.1.1).mp hb))
      _ ?_ key.2.1 key.2.2
    intro scale sample
    exact hv _
  · exact (BinaryFraction.nat_width_le 0).trans (by simpa only [Nat.size_zero, Nat.zero_add] using hV)
  · exact (BinaryFraction.nat_width_le 0).trans (by simpa only [Nat.size_zero, Nat.zero_add] using hV)

include hV hv in
theorem queryPhysicalScalarOnlineRead_width (node : PhysicalInternalNode M J) (time : Fin R)
    (key : ℕ × TargetInterval n) (range : ℕ) :
    ((queryPhysicalScalarOnlineRead M J N n exponent F Q R B node time key range).value oracle).width ≤ V := by
  unfold queryPhysicalScalarOnlineRead
  simp only [BitQuery.value]
  split_ifs
  · exact hv _
  · exact (BinaryFraction.nat_width_le 0).trans (by simpa only [Nat.size_zero, Nat.zero_add] using hV)
  · exact (BinaryFraction.nat_width_le 0).trans (by simpa only [Nat.size_zero, Nat.zero_add] using hV)

end Scalar

section Family
variable {α : Type*} {M J R : ℕ} (target : List α)
  (N P F exponent H Q passes copies pass copy V : ℕ)
  (oracle : PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies → BinaryFraction)
  (hV : 2 ≤ V) (hv : ∀ key, (oracle key).width ≤ V)

include hV hv in
theorem queryFamilyGroupRead_width (node : PhysicalInternalNode M J) (time : Fin R)
    (key : GroupScalarKey M F Q) :
    ((queryFamilyGroupRead target N P F exponent H Q passes copies pass copy node time key).value oracle).width ≤ V := by
  rw [queryFamilyGroupRead, BitQuery.mapKeysWithWork_value]
  exact queryPhysicalScalarGroupRead_width M J N target.length exponent F Q R _ _ V hV (fun _ => hv _) node time key

include hV hv in
theorem queryFamilyOnlineRead_width (node : PhysicalInternalNode M J) (time : Fin R)
    (key : ℕ × TargetInterval target.length) (range : ℕ) :
    ((queryFamilyOnlineRead target N P F exponent H Q passes copies pass copy node time key range).value oracle).width ≤ V := by
  rw [queryFamilyOnlineRead, BitQuery.mapKeysWithWork_value]
  exact queryPhysicalScalarOnlineRead_width M J N target.length exponent F Q R _ _ V hV (fun _ => hv _) node time key range

end Family
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryPhysicalProgramCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
section Physical
variable {σ α : Type*} (source target : List α) {M J : ℕ} [NeZero M]
  (N P F exponent H Q eM eF B E Scale : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction)
  (copies pass copy T S t : ℕ) (ht : 0 < t)
  (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (readGroup : GroupScalarKey M F Q → BitQuery σ BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery σ BinaryFraction)
  (q : TargetInterval target.length)
  (oracle : Sum σ {child : PhysicalTableRequest M J target.length // child.combinedRank T S <
    (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} → BinaryFraction)
  (readWork : Sum σ {child : PhysicalTableRequest M J target.length // child.combinedRank T S <
    (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} → ℕ)

local notation "tableOracle" => (fun key => oracle (Sum.inr key))
local notation "sourceOracle" => (fun key => oracle (Sum.inl key))
local notation "sourceWork" => (fun key => 1 + readWork (Sum.inl key))

open BinaryFraction

theorem queryPhysicalRandomDataRequest_work_bound (V C W : ℕ)
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E Scale (t - 1) tau a eta kappa delta (fun _ _ => 0))
    (htime : Nat.size t ≤ B) (hPd : ∃ j : ℕ, P = 2 ^ j)
    (hV : 2 ≤ V) (hVB : V ≤ B) (hMean : warmupAverageWordBudget T V ≤ B)
    (hc : ∀ key, key.val.pass = pass → key.val.copy = copy → readWork (Sum.inr key) ≤ C)
    (hv : ∀ key, (tableOracle key).width ≤ V)
    (hnonneg : ∀ key, 0 ≤ (tableOracle key).value)
    (hprior : ∀ input : Fin M × ℕ × TargetInterval target.length,
      ((queryPhysicalEarlierRead copies pass copy T S t node hbelow q input).value tableOracle).value ≤
        ((queryPhysicalWarmupRead copies pass copy T S t ht node q
          (physicalChild node hbelow input.1) (by change node.1.val ≤ node.1.val + 1; omega)
          0 (Nat.zero_le T) input.2.2).value tableOracle).value)
    (hgW : ∀ key, ((readGroup key).value sourceOracle).width ≤ B)
    (hzW : ∀ key range, ((readInteger key range).value sourceOracle).width ≤ B)
    (hgR : ∀ key, queryGroupKeySize key ≤ 40 * B + 500 →
      (readGroup key).work sourceOracle sourceWork ≤ W)
    (hzR : ∀ key range, Nat.size key.1 ≤ B + 1 → Nat.size range ≤ 240 * (B + 5) + 7 →
      (readInteger key range).work sourceOracle sourceWork ≤ W) :
    (queryPhysicalRandomDataRequest source target N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta copies pass copy T S t ht node hbelow readGroup readInteger q).work oracle readWork ≤
      queryLocalProgramBitBudget M N P F exponent eM eF B Scale t (queryPhysicalDataBudget T J B V C W) := by
  have htable : ∀ key, key.val.pass = pass → key.val.copy = copy →
      1 + readWork (Sum.inr key) ≤ C + 1 := fun key hp hc' => by have := hc key hp hc'; omega
  have hsmall : 7 * J + 30 + (C + 1) ≤ queryPhysicalDataBudget T J B V C W := by
    unfold queryPhysicalDataBudget; omega
  have hearlier : 8 * B + 7 * J + 32 + (C + 1) ≤ queryPhysicalDataBudget T J B V C W := by
    unfold queryPhysicalDataBudget; omega
  have hmass : T + 1 + T * (7 * J + 30 + (C + 1) + 3) + warmupAverageBitBudget T V ≤
      queryPhysicalDataBudget T J B V C W := by unfold queryPhysicalDataBudget; omega
  have hsource : W ≤ queryPhysicalDataBudget T J B V C W := by unfold queryPhysicalDataBudget; omega
  unfold queryPhysicalRandomDataRequest
  apply queryLocalProgram_work_bound source target (physicalSourceInterval source.length node)
    N P F exponent H Q eM eF B E Scale hP hM hF tau a eta kappa delta t _ _ _ _ _ q _ _
    oracle readWork _ hn ht htime hPd
  · intro r
    rw [BitQuery.mapKeysWithWork_value]
    exact (hv _).trans hVB
  · intro input
    rw [BitQuery.mapKeysWithWork_value]
    exact (queryPhysicalMassRead_bounds copies pass copy T S t ht node hbelow q tableOracle
      (fun key => 1 + readWork (Sum.inr key)) V (C + 1) htable hv input).1.trans hMean
  · intro input
    rw [BitQuery.mapKeysWithWork_value]
    exact (hv _).trans hVB
  · intro key
    simpa only [BitQuery.mapKeysWithWork_value] using hgW key
  · intro key range
    simpa only [BitQuery.mapKeysWithWork_value] using hzW key range
  · intro input
    rw [BitQuery.mapKeysWithWork_value]
    exact (queryPhysicalEarlierRead_width copies pass copy T S t node hbelow q tableOracle V hV hv input).trans hVB
  · intro input
    rw [BitQuery.mapKeysWithWork_value]
    exact (hv _).trans hVB
  · intro r
    rw [BitQuery.mapKeysWithWork_value]
    exact hnonneg _
  · intro input
    rw [BitQuery.mapKeysWithWork_value]
    exact hnonneg _
  · intro input
    rw [BitQuery.mapKeysWithWork_value]
    exact queryPhysicalEarlierRead_nonneg copies pass copy T S t node hbelow q tableOracle hnonneg input
  · intro input
    simpa only [BitQuery.mapKeysWithWork_value] using hprior input
  · intro r
    rw [BitQuery.mapKeysWithWork_work]
    exact (queryPhysicalWarmupRead_work_bound copies pass copy T S t ht node q tableOracle
      (fun key => 1 + readWork (Sum.inr key)) (C + 1) htable node le_rfl 0 (Nat.zero_le T) r).trans hsmall
  · intro input
    rw [BitQuery.mapKeysWithWork_work]
    exact (queryPhysicalMassRead_bounds copies pass copy T S t ht node hbelow q tableOracle
      (fun key => 1 + readWork (Sum.inr key)) V (C + 1) htable hv input).2.trans hmass
  · intro input
    rw [BitQuery.mapKeysWithWork_work]
    exact (queryPhysicalWarmupRead_work_bound copies pass copy T S t ht node q tableOracle
      (fun key => 1 + readWork (Sum.inr key)) (C + 1) htable _ _ 0 (Nat.zero_le T) input.2).trans hsmall
  · intro key hk
    rw [BitQuery.mapKeysWithWork_work]
    exact (hgR key hk).trans hsource
  · intro key range hk hr
    rw [BitQuery.mapKeysWithWork_work]
    exact (hzR key range hk hr).trans hsource
  · intro input hi
    rw [BitQuery.mapKeysWithWork_work]
    exact (queryPhysicalEarlierRead_work_bound copies pass copy T S t node hbelow q tableOracle
      (fun key => 1 + readWork (Sum.inr key)) B (C + 1) htable htime input hi).trans hearlier
  · intro input
    rw [BitQuery.mapKeysWithWork_work]
    exact (queryPhysicalCurrentRead_work_bound copies pass copy T S t node hbelow q tableOracle
      (fun key => 1 + readWork (Sum.inr key)) (C + 1) htable input).trans hsmall

end Physical
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryFamilyRefinementCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
section Family
variable {α : Type*} {M J R : ℕ} [NeZero M] (source target : List α)
  (N P F exponent H Q eM eF B E Scale : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (passes copies pass copy T S t : ℕ) (ht : 0 < t)
  (node : PhysicalNode M J) (hbelow : node.1.val < J) (time : Fin R) (q : TargetInterval target.length)
  (oracle : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)
    {child : PhysicalTableRequest M J target.length // child.combinedRank T S <
      (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} → BinaryFraction)
  (readWork : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)
    {child : PhysicalTableRequest M J target.length // child.combinedRank T S <
      (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} → ℕ)

local notation "tableOracle" => (fun key => oracle (Sum.inr key))
open BinaryFraction

theorem queryFamilyRefinement_work_bound (V C : ℕ)
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E Scale (t - 1) tau a eta kappa delta (fun _ _ => 0))
    (htime : Nat.size t ≤ B) (hPd : ∃ j : ℕ, P = 2 ^ j)
    (hV : 2 ≤ V) (hVB : V ≤ B) (hMean : warmupAverageWordBudget T V ≤ B)
    (hc : ∀ key, key.val.pass = pass → key.val.copy = copy → readWork (Sum.inr key) ≤ C)
    (hs : ∀ key, readWork (Sum.inl key) ≤ C)
    (hv : ∀ key, (tableOracle key).width ≤ V)
    (hsv : ∀ key, (oracle (Sum.inl key)).width ≤ B)
    (hnonneg : ∀ key, 0 ≤ (tableOracle key).value)
    (hprior : ∀ input : Fin M × ℕ × TargetInterval target.length,
      ((queryPhysicalEarlierRead copies pass copy T S t node hbelow q input).value tableOracle).value ≤
        ((queryPhysicalWarmupRead copies pass copy T S t ht node q
          (physicalChild node hbelow input.1) (by change node.1.val ≤ node.1.val + 1; omega)
          0 (Nat.zero_le T) input.2.2).value tableOracle).value)
    (hp : Nat.size pass ≤ B) (hcopy : Nat.size copy ≤ B)
    (hps : Nat.size (passes + 1) ≤ B) (hcs : Nat.size (copies + 1) ≤ B)
    (hbound : Nat.size (localOnlineMassBound M P H) ≤ B) :
    (queryFamilyRefinement source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
      passes copies pass copy T S t ht node hbelow time q).work oracle readWork ≤
      queryLocalProgramBitBudget M N P F exponent eM eF B Scale t
        (queryPhysicalDataBudget T J B V C (queryFamilySourceReadBudget J B (C + 1))) := by
  have hB : 2 ≤ B := by have := hn.largeBits; omega
  have htarget : Nat.size target.length ≤ B := by have := hn.targetSize; omega
  unfold queryFamilyRefinement
  apply queryPhysicalRandomDataRequest_work_bound source target N P F exponent H Q eM eF B E Scale
    hP hM hF tau a eta kappa delta copies pass copy T S t ht node hbelow _ _ q oracle readWork
    V C (queryFamilySourceReadBudget J B (C + 1)) hn htime hPd hV hVB hMean hc hv hnonneg hprior
  · intro key
    exact queryFamilyGroupRead_width target N P F exponent H Q passes copies pass copy B
      (fun key => oracle (Sum.inl key)) hB hsv ⟨node, hbelow⟩ time key
  · intro key range
    exact queryFamilyOnlineRead_width target N P F exponent H Q passes copies pass copy B
      (fun key => oracle (Sum.inl key)) hB hsv ⟨node, hbelow⟩ time key range
  · intro key hk
    exact queryFamilyGroupRead_bounded_work target N P F exponent H Q passes copies pass copy B (C + 1)
      (fun key => oracle (Sum.inl key)) (fun key => 1 + readWork (Sum.inl key))
      hn.inputSize hp hcopy hps hcs (fun key => by have := hs key; omega)
      htarget hn.thetaSize ⟨node, hbelow⟩ time key hk
  · intro key range hk hr
    exact queryFamilyOnlineRead_bounded_work target N P F exponent H Q passes copies pass copy B (C + 1)
      (fun key => oracle (Sum.inl key)) (fun key => 1 + readWork (Sum.inl key))
      hn.inputSize hp hcopy hps hcs (fun key => by have := hs key; omega)
      hbound ⟨node, hbelow⟩ time key range hk hr

end Family
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryRestrictionCost
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BitQuery

theorem restrictWithWork_work {ι : Type*} (P : ι → Prop) (test : ι → Bool × ℕ)
    (htest : ∀ key, (test key).1 = true ↔ P key)
    (program : BitQuery ι BinaryFraction) (oracle : {key // P key} → BinaryFraction)
    (readWork : {key // P key} → ℕ) :
    (restrictWithWork P test htest program).work oracle readWork =
      program.work (restrictedOracle P test htest oracle) (restrictedReadWork P test htest readWork) := by
  induction program with
  | done result => rfl
  | charge steps next ih => exact congrArg (steps + ·) ih
  | read key next ih =>
    by_cases h : (test key).1 = true
    · simp only [restrictWithWork, h, dite_true, work, restrictedOracle, restrictedReadWork, ih,
        Nat.add_assoc]
    · simp only [restrictWithWork, h, Bool.false_eq_true, dite_false, work, restrictedOracle, restrictedReadWork, ih,
        Nat.add_zero]

end EditApproximation.BitQuery

namespace EditApproximation

theorem queryPhysicalBoundedWithWork_cost {M J n : ℕ} (passes copies T S B : ℕ)
    (request : PhysicalTableRequest M J n)
    (hp : Nat.size passes ≤ B) (hc : Nat.size copies ≤ B)
    (hT : Nat.size T ≤ B) (hS : Nat.size S ≤ B)
    (hrp : Nat.size request.pass ≤ B) (hrc : Nat.size request.copy ≤ B)
    (hri : Nat.size request.index ≤ B) :
    (queryPhysicalBoundedWithWork passes copies T S request).2 ≤ 50 * B + 20 := by
  have hpass := binaryNaturalCompareWithWork_cost request.pass passes
  have hcopy := binaryNaturalCompareWithWork_cost request.copy copies
  have hcap := binaryNaturalAddWithWork_cost T S
  have hlen := bitAddWithWork_length T.bits S.bits false
  have hlen' : (binaryNaturalAddWithWork T S).1.length ≤ B + 1 := by
    change (bitAddWithWork T.bits S.bits false).1.length ≤ _
    apply hlen.trans
    simpa only [Nat.size_eq_bits_len] using Nat.add_le_add_right (max_le hT hS) 1
  have hindex := wordLEWithWork_cost request.index.bits (binaryNaturalAddWithWork T S).1
  rw [Nat.size_eq_bits_len] at hindex
  change (binaryNaturalCompareWithWork request.pass passes).2 +
    (binaryNaturalCompareWithWork request.copy copies).2 + (binaryNaturalAddWithWork T S).2 +
    (wordLEWithWork request.index.bits (binaryNaturalAddWithWork T S).1).2 + 4 ≤ _
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryBoundedWork
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
section Body
variable {σ : Type*} {M J n : ℕ} (passes copies T S : ℕ)
  (parent : {r : PhysicalTableRequest M J n // r.Bounded passes copies T S})

theorem queryRestrictPhysicalBody_work
    (program : BitQuery (QueryPhysicalChild (σ := σ) passes copies T S parent) BinaryFraction)
    (oracle : QueryBoundedChild (σ := σ) passes copies T S parent → BinaryFraction)
    (readWork : QueryBoundedChild (σ := σ) passes copies T S parent → ℕ) :
    (queryRestrictPhysicalBody passes copies T S parent program).work oracle readWork =
      program.work (queryRestrictedPhysicalOracle passes copies T S parent oracle)
        (queryRestrictedPhysicalReadWork passes copies T S parent readWork) := by
  rw [queryRestrictPhysicalBody, BitQuery.mapKeysWithWork_work, BitQuery.restrictWithWork_work]
  rfl

theorem queryRestrictedPhysicalOracle_table_width
    (oracle : QueryBoundedChild (σ := σ) passes copies T S parent → BinaryFraction)
    (B : ℕ) (hB : 2 ≤ B) (hw : ∀ key, (oracle (Sum.inr key)).width ≤ B) (child) :
    (queryRestrictedPhysicalOracle passes copies T S parent oracle (Sum.inr child)).width ≤ B := by
  unfold queryRestrictedPhysicalOracle BitQuery.restrictedOracle
  split
  · exact hw _
  · exact (BinaryFraction.nat_width_le 0).trans (by simpa only [Nat.size_zero, Nat.zero_add] using hB)

theorem queryRestrictedPhysicalOracle_table_nonneg
    (oracle : QueryBoundedChild (σ := σ) passes copies T S parent → BinaryFraction)
    (hn : ∀ key, 0 ≤ (oracle (Sum.inr key)).value) (child) :
    0 ≤ (queryRestrictedPhysicalOracle passes copies T S parent oracle (Sum.inr child)).value := by
  unfold queryRestrictedPhysicalOracle BitQuery.restrictedOracle
  split
  · exact hn _
  · simp only [BinaryFraction.nat_value, Nat.cast_zero, le_refl]

private theorem index_le_combinedRank (request : PhysicalTableRequest M J n) :
    request.index ≤ request.combinedRank T S := by
  unfold PhysicalTableRequest.combinedRank PhysicalTableRequest.rank
  omega

private theorem pass_le_combinedRank (request : PhysicalTableRequest M J n) :
    request.pass ≤ request.combinedRank T S := by
  have hmul : request.pass ≤ request.pass * (T + S + 1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold PhysicalTableRequest.combinedRank PhysicalTableRequest.rank
  omega

theorem queryRestrictedPhysicalReadWork_bound
    (readWork : QueryBoundedChild (σ := σ) passes copies T S parent → ℕ) (B W : ℕ)
    (hp : Nat.size passes ≤ B) (hc : Nat.size copies ≤ B) (hT : Nat.size T ≤ B) (hS : Nat.size S ≤ B)
    (hr : Nat.size (parent.val.combinedRank T S) ≤ B) (hcopy : Nat.size parent.val.copy ≤ B)
    (hW : ∀ key, readWork key ≤ W)
    (key : QueryPhysicalChild (σ := σ) passes copies T S parent)
    (hk : ∀ child, key = Sum.inr child → child.val.copy = parent.val.copy) :
    queryRestrictedPhysicalReadWork passes copies T S parent readWork key ≤ 50 * B + 21 + W := by
  have hread (k) := hW (SourceRanked.supportedChildMap (PhysicalTableRequest.combinedRank T S)
    (PhysicalTableRequest.Bounded passes copies T S) parent k)
  cases key with
  | inl source =>
    change 1 + (1 + readWork _) ≤ _
    have := hread ⟨Sum.inl source, trivial⟩
    omega
  | inr child =>
    have hpass : Nat.size child.val.pass ≤ B :=
      (Nat.size_le_size ((pass_le_combinedRank T S child.val).trans child.property.le)).trans hr
    have hindex : Nat.size child.val.index ≤ B :=
      (Nat.size_le_size ((index_le_combinedRank T S child.val).trans child.property.le)).trans hr
    have hcopy' : Nat.size child.val.copy ≤ B := by rw [hk child rfl]; exact hcopy
    have hguard := queryPhysicalBoundedWithWork_cost passes copies T S B child.val hp hc hT hS hpass hcopy' hindex
    unfold queryRestrictedPhysicalReadWork BitQuery.restrictedReadWork
    change (querySupportedChildWithWork (σ := σ) passes copies T S parent (Sum.inr child)).2 ≤ 50 * B + 20 at hguard
    by_cases hgate : (querySupportedChildWithWork (σ := σ) passes copies T S parent (Sum.inr child)).1 = true
    · rw [dite_eq_left hgate]
      dsimp only
      have := hread ⟨Sum.inr child, (querySupportedChildWithWork_value passes copies T S parent _).mp hgate⟩
      omega
    · rw [dite_eq_right hgate]
      omega

end Body
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryActiveCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Active
variable {α : Type*} {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q eM eF B E Scale : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (T S passes copies : ℕ)
  (request : PhysicalTableRequest M J target.length)
  (hindex : T < request.index) (hbelow : request.node.1.val < J)
  (oracle : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)
    {child : PhysicalTableRequest M J target.length // child.combinedRank T S < request.combinedRank T S} → BinaryFraction)
  (readWork : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)
    {child : PhysicalTableRequest M J target.length // child.combinedRank T S < request.combinedRank T S} → ℕ)

local notation "tableOracle" => (fun key => queryActiveOracle T request hindex S oracle (Sum.inr key))
open BinaryFraction

theorem queryFamilyActive_work_bound (V C : ℕ)
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E Scale (request.index - T - 1) tau a eta kappa delta (fun _ _ => 0))
    (htime : Nat.size (request.index - T) ≤ B) (hPd : ∃ j : ℕ, P = 2 ^ j)
    (hV : 2 ≤ V) (hVB : V ≤ B) (hMean : warmupAverageWordBudget T V ≤ B)
    (hc : ∀ key, key.val.pass = request.pass → key.val.copy = request.copy → readWork (Sum.inr key) ≤ C)
    (hs : ∀ key, readWork (Sum.inl key) ≤ C)
    (hv : ∀ key, (oracle (Sum.inr key)).width ≤ V)
    (hsv : ∀ key, (oracle (Sum.inl key)).width ≤ B)
    (hnonneg : ∀ key, 0 ≤ (oracle (Sum.inr key)).value)
    (hprior : ∀ input : Fin M × ℕ × TargetInterval target.length,
      ((queryPhysicalEarlierRead copies request.pass request.copy T S (request.index - T)
        request.node hbelow request.state input).value tableOracle).value ≤
      ((queryPhysicalWarmupRead copies request.pass request.copy T S (request.index - T)
        (Nat.sub_pos_of_lt hindex) request.node request.state
        (physicalChild request.node hbelow input.1) (by change request.node.1.val ≤ request.node.1.val + 1; omega)
        0 (Nat.zero_le T) input.2.2).value tableOracle).value)
    (hp : Nat.size request.pass ≤ B) (hcopy : Nat.size request.copy ≤ B)
    (hps : Nat.size (passes + 1) ≤ B) (hcs : Nat.size (copies + 1) ≤ B)
    (hbound : Nat.size (localOnlineMassBound M P H) ≤ B) :
    (queryFamilyActive (R := R) source target N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta T S passes copies request hindex hbelow).work oracle readWork ≤
      queryLocalProgramBitBudget M N P F exponent eM eF B Scale (request.index - T)
        (queryPhysicalDataBudget T J B V (C + 1) (queryFamilySourceReadBudget J B (C + 1 + 1))) := by
  rw [queryFamilyActive, BitQuery.mapKeysWithWork_work]
  change (queryFamilyRefinement (R := R) source target N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta passes copies request.pass request.copy T S (request.index - T)
    (Nat.sub_pos_of_lt hindex) request.node hbelow (Fin.ofNat R (request.index - T - 1)) request.state).work
    (queryActiveOracle T request hindex S oracle) (queryActiveReadWork T request hindex S readWork) ≤ _
  apply queryFamilyRefinement_work_bound source target N P F exponent H Q eM eF B E Scale hP hM hF
    tau a eta kappa delta passes copies request.pass request.copy T S (request.index - T)
    (Nat.sub_pos_of_lt hindex) request.node hbelow (Fin.ofNat R (request.index - T - 1)) request.state
    _ _ V (C + 1) hn htime hPd hV hVB hMean
  · intro key hpass hcopy'
    have h := hc ⟨key.val, by simpa only [queryRefinementRequest_eq T request hindex] using key.property⟩ hpass hcopy'
    change 1 + readWork (Sum.inr ⟨key.val, _⟩) ≤ C + 1
    omega
  · intro key
    change 1 + readWork (Sum.inl key) ≤ C + 1
    have := hs key
    omega
  · intro key
    exact hv _
  · exact hsv
  · intro key
    exact hnonneg _
  · exact hprior
  · exact hp
  · exact hcopy
  · exact hps
  · exact hcs
  · exact hbound

end Active
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryBoundedActiveCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
section Bounded
variable {α : Type*} {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q eM eF B E Scale : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (T S passes copies : ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S})
  (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J)
  (oracle : QueryBoundedChild (σ := PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies) (passes + 1) copies T S parent → BinaryFraction)
  (readWork : QueryBoundedChild (σ := PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies) (passes + 1) copies T S parent → ℕ)

local notation "rawOracle" => queryRestrictedPhysicalOracle (passes + 1) copies T S parent oracle
local notation "rawWork" => queryRestrictedPhysicalReadWork (passes + 1) copies T S parent readWork
local notation "tableOracle" => (fun key => queryActiveOracle T parent.val hindex S rawOracle (Sum.inr key))
open BinaryFraction

theorem queryFamilyBoundedActive_work_bound_oai (V C : ℕ)
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E Scale (parent.val.index - T - 1) tau a eta kappa delta (fun _ _ => 0))
    (htime : Nat.size (parent.val.index - T) ≤ B) (hPd : ∃ j : ℕ, P = 2 ^ j)
    (hV : 2 ≤ V) (hVB : V ≤ B) (hMean : warmupAverageWordBudget T V ≤ B)
    (hc : ∀ key, readWork key ≤ C)
    (hv : ∀ key, (oracle (Sum.inr key)).width ≤ V)
    (hsv : ∀ key, (oracle (Sum.inl key)).width ≤ B)
    (hnonneg : ∀ key, 0 ≤ (oracle (Sum.inr key)).value)
    (hprior : ∀ input : Fin M × ℕ × TargetInterval target.length,
      ((queryPhysicalEarlierRead copies parent.val.pass parent.val.copy T S (parent.val.index - T)
        parent.val.node hbelow parent.val.state input).value tableOracle).value ≤
      ((queryPhysicalWarmupRead copies parent.val.pass parent.val.copy T S (parent.val.index - T)
        (Nat.sub_pos_of_lt hindex) parent.val.node parent.val.state
        (physicalChild parent.val.node hbelow input.1) (by change parent.val.node.1.val ≤ parent.val.node.1.val + 1; omega)
        0 (Nat.zero_le T) input.2.2).value tableOracle).value)
    (hp : Nat.size parent.val.pass ≤ B) (hcopy : Nat.size parent.val.copy ≤ B)
    (hps : Nat.size (passes + 1) ≤ B) (hcs : Nat.size (copies + 1) ≤ B)
    (hT : Nat.size T ≤ B) (hS : Nat.size S ≤ B)
    (hrank : Nat.size (parent.val.combinedRank T S) ≤ B)
    (hbound : Nat.size (localOnlineMassBound M P H) ≤ B) :
    (queryFamilyBoundedActive (R := R) source target N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta T S passes copies parent hindex hbelow).work oracle readWork ≤
      queryLocalProgramBitBudget M N P F exponent eM eF B Scale (parent.val.index - T)
        (queryPhysicalDataBudget T J B V (50 * B + 21 + C + 1)
          (queryFamilySourceReadBudget J B (50 * B + 21 + C + 1 + 1))) := by
  rw [queryFamilyBoundedActive, queryRestrictPhysicalBody_work]
  apply queryFamilyActive_work_bound source target N P F exponent H Q eM eF B E Scale hP hM hF
    tau a eta kappa delta T S passes copies parent.val hindex hbelow rawOracle rawWork V
    (50 * B + 21 + C) hn htime hPd hV hVB hMean
  · intro key _ hcopy'
    apply queryRestrictedPhysicalReadWork_bound (passes + 1) copies T S parent readWork B C
      hps ((Nat.size_le_size (Nat.le_succ copies)).trans hcs) hT hS hrank hcopy hc (Sum.inr key)
    intro child heq
    cases heq
    exact hcopy'
  · intro key
    apply queryRestrictedPhysicalReadWork_bound (passes + 1) copies T S parent readWork B C
      hps ((Nat.size_le_size (Nat.le_succ copies)).trans hcs) hT hS hrank hcopy hc (Sum.inl key)
    intro child heq
    cases heq
  · exact queryRestrictedPhysicalOracle_table_width (passes + 1) copies T S parent oracle V hV hv
  · intro key
    exact hsv key
  · exact queryRestrictedPhysicalOracle_table_nonneg (passes + 1) copies T S parent oracle hnonneg
  · exact hprior
  · exact hp
  · exact hcopy
  · exact hps
  · exact hcs
  · exact hbound

end Bounded
end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.queryFamilyBoundedActive_work_bound_oai.{u_1} := @OAI.EditApproximation.queryFamilyBoundedActive_work_bound_oai.{u_1}
