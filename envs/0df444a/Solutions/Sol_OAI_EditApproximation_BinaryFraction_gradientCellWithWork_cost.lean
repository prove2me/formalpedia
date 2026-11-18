-- Prove2me | solution 1 for OAI.EditApproximation.BinaryFraction.gradientCellWithWork_cost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:22:20.656325+00:00
-- url     : https://prove2.me/submissions/5d10a909-2451-4b42-ab42-957b4fc18453

import Mathlib
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_11
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

/-- Every logarithm series term is bounded on nonnegative inputs;
this controls the returned numerator without transcendental arithmetic. -/
theorem rationalLogApproximation_abs_bound (r : ℚ) (K : ℕ) (hr : 0 ≤ r) :
    |rationalLogApproximation r K| ≤ 2 * K := by
  let b := (r - 1) / (r + 1)
  have hrden : 0 < r + 1 := by linarith
  have hb : |b| ≤ 1 := by
    dsimp only [b]
    rw [abs_div, abs_of_pos hrden]
    apply (div_le_one₀ hrden).mpr
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hterm (k : ℕ) : |b ^ (2 * k + 1) / (2 * k + 1 : ℕ)| ≤ 1 := by
    have hden : (1 : ℚ) ≤ (2 * k + 1 : ℕ) := by norm_cast; omega
    have hdenpos : (0 : ℚ) < (2 * k + 1 : ℕ) := by positivity
    rw [abs_div, abs_pow, abs_of_pos hdenpos]
    calc
      _ ≤ (1 : ℚ) / (2 * k + 1 : ℕ) := div_le_div_of_nonneg_right
        (pow_le_one₀ (abs_nonneg b) hb) hdenpos.le
      _ ≤ 1 := (div_le_one₀ hdenpos).mpr hden
  have hsum : |∑ k ∈ range K, b ^ (2 * k + 1) / (2 * k + 1 : ℕ)| ≤ K := by
    calc
      _ ≤ ∑ k ∈ range K, |b ^ (2 * k + 1) / (2 * k + 1 : ℕ)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ range K, (1 : ℚ) := sum_le_sum (fun k _ => hterm k)
      _ = K := by simp
  unfold rationalLogApproximation
  push_cast at hsum
  dsimp only [b] at hsum
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 2)]
  linarith

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

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_UnreducedNumerics
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.nat_representation _root_.OAI.EditApproximation.BinaryFraction.representation_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The numerical primitives executed on unreduced fractions. Their exact
values agree with the rational routines; their stored denominators
have polynomial bit length without cancellation or Euclidean normalization. -/

namespace EditApproximation

open Finset
namespace UnreducedRational

theorem pow_den (a : UnreducedRational) (n : ℕ) : (a.pow n).den = a.den ^ n := by
  induction n with
  | zero => simp [pow, one, ofRat]
  | succ n ih => simp [pow, mul, ih, pow_succ]

theorem pow_den_bits (a : UnreducedRational) (n : ℕ) :
    Nat.size (a.pow n).den ≤ n * Nat.size a.den + 1 := by
  rw [pow_den]
  exact natural_power_bit_length _ _

theorem nat_inv_den (n : ℕ) (hn : 0 < n) : (nat n).inv.den = n := by
  simp [nat, inv, hn.ne']

theorem logarithmPartial_value (b : UnreducedRational) (K : ℕ) :
    (logarithmPartial b K).value =
      ∑ k ∈ range K, b.value ^ (2 * k + 1) / (2 * k + 1 : ℕ) := by
  induction K with
  | zero => simp [logarithmPartial]
  | succ K ih => simp [logarithmPartial, ih, sum_range_succ]

@[simp] theorem logarithm_value (r : UnreducedRational) (K : ℕ) :
    (logarithm r K).value = rationalLogApproximation r.value K := by
  simp [logarithm, logarithmPartial_value, rationalLogApproximation]

theorem logarithmPartial_den_bits (b : UnreducedRational) (K : ℕ) :
    Nat.size (logarithmPartial b K).den ≤
      K * K * Nat.size b.den + K * (Nat.size (2 * K + 1) + 1) + 1 := by
  induction K with
  | zero => simp [logarithmPartial, zero]
  | succ K ih =>
    have hp := pow_den_bits b (2 * K + 1)
    have ht := mul_den_bits (b.pow (2 * K + 1)) (nat (2 * K + 1)).inv
    rw [nat_inv_den _ (by omega)] at ht
    have ha := add_den_bits (logarithmPartial b K)
      ((b.pow (2 * K + 1)).div (nat (2 * K + 1)))
    have hs := Nat.size_le_size (by omega : 2 * K + 1 ≤ 2 * (K + 1) + 1)
    change Nat.size ((logarithmPartial b K).add
      ((b.pow (2 * K + 1)).div (nat (2 * K + 1)))).den ≤ _
    change Nat.size ((b.pow (2 * K + 1)).div (nat (2 * K + 1))).den ≤ _ at ht
    have hweighted := Nat.mul_le_mul_left K hs
    nlinarith only [ih, hp, ht, ha, hweighted, hs]

theorem logarithm_storageBits (r : UnreducedRational) (K : ℕ) (hr : 0 ≤ r.value) :
    (logarithm r K).storageBits ≤ Nat.size (2 * K) +
      2 * (K * K * Nat.size ((r.sub one).div (r.add one)).den +
        K * (Nat.size (2 * K + 1) + 1) + 1) + 1 := by
  apply storageBits_le
  · rw [logarithm_value]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using rationalLogApproximation_abs_bound r.value K hr
  · simpa only [logarithm, mul, nat, Nat.one_mul] using
      logarithmPartial_den_bits ((r.sub one).div (r.add one)) K

end UnreducedRational
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_CanonicalFractionWork
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_representation _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.UnreducedRational.logarithm_value _root_.OAI.EditApproximation.UnreducedRational.value_pow _root_.OAI.EditApproximation.UnreducedRational.value_sub _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
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



theorem powWithWork_representation (a : BinaryFraction) (k : ℕ) :
    (a.powWithWork k).1.representation = a.representation.pow k := by
  induction k with
  | zero => exact one_representation
  | succ k ih => simp only [powWithWork, canonicalMulWithWork_representation,
      UnreducedRational.pow, ih]



theorem logarithmPartialWithWork_representation (b : BinaryFraction) (k : ℕ) :
    (b.logarithmPartialWithWork k).1.representation = b.representation.logarithmPartial k := by
  induction k with
  | zero => exact zero_representation
  | succ k ih => simp only [logarithmPartialWithWork, canonicalAddWithWork_representation,
      divWithWork_representation, powWithWork_representation, nat_representation,
      UnreducedRational.logarithmPartial, ih]



theorem logarithmWithWork_representation (r : BinaryFraction) (k : ℕ) :
    (r.logarithmWithWork k).1.representation = r.representation.logarithm k := by
  simp only [logarithmWithWork, canonicalMulWithWork_representation,
    logarithmPartialWithWork_representation, divWithWork_representation,
    subWithWork_representation, canonicalAddWithWork_representation,
    nat_representation, one_representation, UnreducedRational.logarithm]



theorem nat_width_le_storageBits (n : ℕ) : (nat n).width ≤ (nat n).representation.storageBits := by
  rw [nat_representation]
  have hw : (nat n).width = max (Nat.size n) 1 := by
    simp only [nat, width, SignedBinary.ofInt, Int.natAbs_natCast, ← Nat.size_eq_bits_len,
      List.length_cons, List.length_nil]
  rw [hw]
  simp only [UnreducedRational.nat, UnreducedRational.storageBits, Int.natAbs_natCast, Nat.size_one]
  omega

theorem zero_width_le_storageBits : zero.width ≤ zero.representation.storageBits := by decide

theorem powWithWork_width_le_storageBits (a : BinaryFraction) (n : ℕ) :
    (a.powWithWork n).1.width ≤ (a.powWithWork n).1.representation.storageBits := by
  cases n with
  | zero => exact nat_width_le_storageBits 1
  | succ n =>
    dsimp only [powWithWork]
    exact canonicalMulWithWork_self_width (a.powWithWork n).1 a

theorem logarithmPartialWithWork_width_le_storageBits (b : BinaryFraction) (n : ℕ) :
    (b.logarithmPartialWithWork n).1.width ≤
      (b.logarithmPartialWithWork n).1.representation.storageBits := by
  cases n with
  | zero => exact zero_width_le_storageBits
  | succ n =>
    dsimp only [logarithmPartialWithWork]
    exact canonicalAddWithWork_self_width _ _

theorem logarithmWithWork_width_le_storageBits (r : BinaryFraction) (n : ℕ) :
    (r.logarithmWithWork n).1.width ≤ (r.logarithmWithWork n).1.representation.storageBits := by
  dsimp only [logarithmWithWork]
  exact canonicalMulWithWork_self_width _ _

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

theorem storageBits_one : one.storageBits = 3 := by decide

theorem storageBits_zero : zero.storageBits = 2 := by decide

theorem storageBits_neg (a : UnreducedRational) : a.neg.storageBits = a.storageBits := by
  simp [neg, storageBits]

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

theorem storageBits_sub (a b : UnreducedRational) :
    (a.sub b).storageBits ≤ 2 * a.storageBits + 2 * b.storageBits + 2 := by
  simpa only [sub, storageBits_neg] using storageBits_add a b.neg

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

theorem logarithmRatio_storageBits (r : UnreducedRational) :
    ((r.sub one).div (r.add one)).storageBits ≤ 4 * r.storageBits + 18 := by
  have hsub := storageBits_sub r one
  have hadd := storageBits_add r one
  have hdiv := storageBits_div (r.sub one) (r.add one)
  rw [storageBits_one] at hsub hadd
  omega

theorem logarithm_storageBits_poly (r : UnreducedRational) (K : ℕ) (hr : 0 ≤ r.value) :
    (logarithm r K).storageBits ≤
      Nat.size (2 * K) + 2 * (K * K * (4 * r.storageBits + 18) +
        K * (Nat.size (2 * K + 1) + 1) + 1) + 1 := by
  have h := logarithm_storageBits r K hr
  have hratio := logarithmRatio_storageBits r
  have hd : Nat.size ((r.sub one).div (r.add one)).den ≤ 4 * r.storageBits + 18 := by
    exact (by dsimp only [storageBits]; omega :
      Nat.size ((r.sub one).div (r.add one)).den ≤ ((r.sub one).div (r.add one)).storageBits).trans hratio
  have hm := Nat.mul_le_mul_left (K * K) hd
  omega

theorem logarithmPartial_abs_le (b : UnreducedRational) (K : ℕ) (hb : |b.value| ≤ 1) :
    |(logarithmPartial b K).value| ≤ K := by
  rw [logarithmPartial_value]
  calc
    _ ≤ ∑ k ∈ range K, |b.value ^ (2 * k + 1) / (2 * k + 1 : ℕ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ range K, (1 : ℚ) := by
      apply sum_le_sum
      intro k _
      have hd : (0 : ℚ) < (2 * k + 1 : ℕ) := by positivity
      have hd1 : (1 : ℚ) ≤ (2 * k + 1 : ℕ) := by norm_cast; omega
      rw [abs_div, abs_pow, abs_of_pos hd]
      exact (div_le_div_of_nonneg_right (pow_le_one₀ (abs_nonneg _) hb) hd.le).trans
        ((div_le_one₀ hd).mpr hd1)
    _ = K := by simp

theorem logarithmPartial_storageBits (b : UnreducedRational) (K : ℕ) (hb : |b.value| ≤ 1) :
    (logarithmPartial b K).storageBits ≤ Nat.size K +
      2 * (K * K * Nat.size b.den + K * (Nat.size (2 * K + 1) + 1) + 1) + 1 :=
  storageBits_le _ K _ (logarithmPartial_abs_le b K hb) (logarithmPartial_den_bits b K)

theorem pow_storageBits_abs_le_one (b : UnreducedRational) (K : ℕ) (hb : |b.value| ≤ 1) :
    (b.pow K).storageBits ≤ 2 * (K * Nat.size b.den + 1) + 2 := by
  have hv : |(b.pow K).value| ≤ (1 : ℕ) := by
    rw [value_pow, abs_pow]
    exact pow_le_one₀ (abs_nonneg _) hb
  have h := storageBits_le (b.pow K) 1 _ hv (pow_den_bits b K)
  simp only [Nat.size_one] at h
  omega

theorem pow_storageBits (a : UnreducedRational) (n : ℕ) :
    (a.pow n).storageBits ≤ 3 + n * a.storageBits := by
  induction n with
  | zero => simpa only [pow, Nat.zero_mul, Nat.add_zero] using storageBits_one.le
  | succ n ih =>
    have hm := storageBits_mul (a.pow n) a
    simp only [pow]
    nlinarith only [ih, hm]

theorem logarithmStorageBudget_mono {A B : ℕ} (h : A ≤ B) (K : ℕ) :
    logarithmStorageBudget A K ≤ logarithmStorageBudget B K := by
  have hm := Nat.mul_le_mul_left (K * K) (show 4 * A + 18 ≤ 4 * B + 18 by omega)
  unfold logarithmStorageBudget
  omega

theorem logarithmPartial_storageBits_uniform (b : UnreducedRational) (j K : ℕ)
    (hj : j ≤ K) (hb : |b.value| ≤ 1) :
    (logarithmPartial b j).storageBits ≤ Nat.size K +
      2 * (K * K * Nat.size b.den + K * (Nat.size (2 * K + 1) + 1) + 1) + 1 := by
  have h := logarithmPartial_storageBits b j hb
  have hs := Nat.size_le_size hj
  have hsodd := Nat.size_le_size (show 2 * j + 1 ≤ 2 * K + 1 by omega)
  have hquad := Nat.mul_le_mul_right (Nat.size b.den) (Nat.mul_le_mul hj hj)
  have hlinear := Nat.mul_le_mul hj (Nat.add_le_add_right hsodd 1)
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

theorem powWithWork_cost_of_width (a : BinaryFraction) (n B : ℕ)
    (ha : a.width ≤ B)
    (hprevious : ∀ j < n, (a.powWithWork j).1.width ≤ B) :
    (a.powWithWork n).2 ≤ 1 + n * (2000 * (B + 1) ^ 2 + 1) := by
  induction n with
  | zero => simp [powWithWork]
  | succ n ih =>
    have hp := ih (fun j hj => hprevious j (by omega))
    have hm := canonicalMulWithWork_cost (a.powWithWork n).1 a B
      (hprevious n (by omega)) ha
    change (a.powWithWork n).2 + (canonicalMulWithWork (a.powWithWork n).1 a).2 + 1 ≤ _
    nlinarith only [hp, hm]

theorem powWithWork_width_abs_le_one (a : BinaryFraction) (n : ℕ) (ha : |a.value| ≤ 1) :
    (a.powWithWork n).1.width ≤ 2 * (n * Nat.size a.representation.den + 1) + 2 := by
  have hwidth := powWithWork_width_le_storageBits a n
  rw [powWithWork_representation] at hwidth
  exact hwidth.trans (UnreducedRational.pow_storageBits_abs_le_one _ _ ha)

theorem representation_den_bits_le_width (a : BinaryFraction) :
    Nat.size a.representation.den ≤ a.width := by
  have hd : Nat.size (bitWordValue a.denominator) ≤ a.denominator.length :=
    Nat.size_le.mpr (bitWordValue_lt_pow_length _)
  exact hd.trans (le_max_right _ _)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLogWork
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bit cost of the finite logarithm series on unreduced Boolean fractions.
Every bound is for the executed power/division/addition loops. -/

namespace EditApproximation
namespace BinaryFraction

theorem logarithmPartialWordBudget_input (b : BinaryFraction) (K : ℕ) :
    b.width ≤ logarithmPartialWordBudget b K := by
  unfold logarithmPartialWordBudget
  omega

theorem logarithmPartialWordBudget_power (b : BinaryFraction) (K j : ℕ)
    (hj : j ≤ 2 * K + 1) (hb : |b.value| ≤ 1) :
    (b.powWithWork j).1.width ≤ logarithmPartialWordBudget b K := by
  have h := powWithWork_width_abs_le_one b j hb
  have hm := Nat.mul_le_mul_right (Nat.size b.representation.den) hj
  unfold logarithmPartialWordBudget
  omega

theorem logarithmPartialWordBudget_partial (b : BinaryFraction) (K j : ℕ)
    (hj : j ≤ K) (hb : |b.value| ≤ 1) :
    (b.logarithmPartialWithWork j).1.width ≤ logarithmPartialWordBudget b K := by
  have hw := logarithmPartialWithWork_width_le_storageBits b j
  rw [logarithmPartialWithWork_representation] at hw
  have hs := UnreducedRational.logarithmPartial_storageBits_uniform b.representation j K hj hb
  unfold logarithmPartialWordBudget
  omega

theorem logarithmPartialWordBudget_nat (b : BinaryFraction) (K j : ℕ) (hj : j ≤ K) :
    (nat (2 * j + 1)).width ≤ logarithmPartialWordBudget b K := by
  have hw := nat_width_le_storageBits (2 * j + 1)
  rw [nat_representation, UnreducedRational.storageBits_nat] at hw
  have hs := Nat.size_le_size (show 2 * j + 1 ≤ 2 * K + 1 by omega)
  unfold logarithmPartialWordBudget
  omega

theorem divWithWork_self_width (a b : BinaryFraction) :
    (a.divWithWork b).1.width ≤ (a.divWithWork b).1.representation.storageBits :=
  canonicalMulWithWork_self_width _ _

theorem logarithmPartialWordBudget_term (b : BinaryFraction) (K j : ℕ)
    (hj : j ≤ K) (hb : |b.value| ≤ 1) :
    ((b.powWithWork (2 * j + 1)).1.divWithWork (nat (2 * j + 1))).1.width ≤
      logarithmPartialWordBudget b K := by
  have hw := divWithWork_self_width (b.powWithWork (2 * j + 1)).1 (nat (2 * j + 1))
  rw [divWithWork_representation, powWithWork_representation, nat_representation] at hw
  have hs := UnreducedRational.storageBits_div (b.representation.pow (2 * j + 1))
    (UnreducedRational.nat (2 * j + 1))
  rw [UnreducedRational.storageBits_nat] at hs
  have hp := UnreducedRational.pow_storageBits_abs_le_one b.representation (2 * j + 1) hb
  have hm := Nat.mul_le_mul_right (Nat.size b.representation.den)
    (show 2 * j + 1 ≤ 2 * K + 1 by omega)
  have hn := Nat.size_le_size (show 2 * j + 1 ≤ 2 * K + 1 by omega)
  unfold logarithmPartialWordBudget
  omega

theorem logarithmPartialWithWork_cost_le (b : BinaryFraction) (K j : ℕ)
    (hj : j ≤ K) (hb : |b.value| ≤ 1) :
    (b.logarithmPartialWithWork j).2 ≤
      1 + j * logarithmPartialBitStep (logarithmPartialWordBudget b K) K := by
  induction j with
  | zero => simp [logarithmPartialWithWork]
  | succ j ih =>
    let W := logarithmPartialWordBudget b K
    have hp := ih (by omega)
    have hpower := powWithWork_cost_of_width b (2 * j + 1) W
      (logarithmPartialWordBudget_input b K) (by
        intro m hm
        exact logarithmPartialWordBudget_power b K m (by omega) hb)
    have hpower' : (b.powWithWork (2 * j + 1)).2 ≤
        1 + (2 * K + 1) * (2000 * (W + 1) ^ 2 + 1) := by
      have hm := Nat.mul_le_mul_right (2000 * (W + 1) ^ 2 + 1)
        (show 2 * j + 1 ≤ 2 * K + 1 by omega)
      omega
    have hdiv := divWithWork_cost (b.powWithWork (2 * j + 1)).1 (nat (2 * j + 1)) W
      (logarithmPartialWordBudget_power b K (2 * j + 1) (by omega) hb)
      (logarithmPartialWordBudget_nat b K j (by omega))
    have hadd := canonicalAddWithWork_cost (b.logarithmPartialWithWork j).1
      ((b.powWithWork (2 * j + 1)).1.divWithWork (nat (2 * j + 1))).1 W
      (logarithmPartialWordBudget_partial b K j (by omega) hb)
      (logarithmPartialWordBudget_term b K j (by omega) hb)
    have hn := Nat.size_le_size (show 2 * j + 1 ≤ 2 * K + 1 by omega)
    change (b.logarithmPartialWithWork j).2 + (b.powWithWork (2 * j + 1)).2 +
      ((b.powWithWork (2 * j + 1)).1.divWithWork (nat (2 * j + 1))).2 +
      (canonicalAddWithWork (b.logarithmPartialWithWork j).1
        ((b.powWithWork (2 * j + 1)).1.divWithWork (nat (2 * j + 1))).1).2 +
      Nat.size (2 * j + 1) + 5 ≤ _
    change (b.logarithmPartialWithWork j).2 ≤ 1 + j * logarithmPartialBitStep W K at hp
    change _ ≤ 1 + (j + 1) * logarithmPartialBitStep W K
    unfold logarithmPartialBitStep at hp ⊢
    nlinarith only [hp, hpower', hdiv, hadd, hn]

theorem logarithmPartialWithWork_cost (b : BinaryFraction) (K : ℕ) (hb : |b.value| ≤ 1) :
    (b.logarithmPartialWithWork K).2 ≤
      1 + K * logarithmPartialBitStep (logarithmPartialWordBudget b K) K :=
  logarithmPartialWithWork_cost_le b K K le_rfl hb

theorem logarithmRatio_abs_le_one (r : BinaryFraction) (hr : 0 ≤ r.value) :
    |((r.subWithWork one).1.divWithWork (canonicalAddWithWork r one).1).1.value| ≤ 1 := by
  rw [← representation_value, divWithWork_representation, subWithWork_representation,
    canonicalAddWithWork_representation, one_representation]
  simp only [UnreducedRational.value_div, UnreducedRational.value_sub,
    UnreducedRational.value_add, UnreducedRational.value_one, representation_value]
  have hd : 0 < r.value + 1 := by linarith
  rw [abs_div, abs_of_pos hd]
  exact (div_le_one₀ hd).mpr (abs_le.mpr ⟨by linarith, by linarith⟩)

theorem logarithmPartialWordBudget_le (b : BinaryFraction) (B K : ℕ) (hw : b.width ≤ B) :
    logarithmPartialWordBudget b K ≤ logarithmUniversalWordBudget B K := by
  have hd := (representation_den_bits_le_width b).trans hw
  have hquad := Nat.mul_le_mul_left (K * K) hd
  have hlin := Nat.mul_le_mul_left (2 * K + 1) hd
  unfold logarithmPartialWordBudget logarithmUniversalWordBudget
  omega

theorem logarithmPartialBitStep_mono {A B : ℕ} (h : A ≤ B) (K : ℕ) :
    logarithmPartialBitStep A K ≤ logarithmPartialBitStep B K := by
  have h1 := Nat.mul_self_le_mul_self (show A + 1 ≤ B + 1 by omega)
  have h2 := Nat.mul_self_le_mul_self (show A + 2 ≤ B + 2 by omega)
  simp only [← pow_two] at h1 h2
  have hm := Nat.mul_le_mul_left (2 * K + 1)
    (show 2000 * (A + 1) ^ 2 + 1 ≤ 2000 * (B + 1) ^ 2 + 1 by omega)
  unfold logarithmPartialBitStep
  omega

theorem logarithmRatio_width (r : BinaryFraction) : (logarithmRatio r).width ≤ 8 * r.width + 22 := by
  have hw := divWithWork_self_width (r.subWithWork one).1 (canonicalAddWithWork r one).1
  rw [divWithWork_representation, subWithWork_representation, canonicalAddWithWork_representation,
    one_representation] at hw
  have hs := UnreducedRational.logarithmRatio_storageBits r.representation
  have hr := representation_storageBits_le r
  change (logarithmRatio r).width ≤ _ at hw
  omega

theorem one_width : one.width ≤ 3 := by decide

theorem sub_one_width (r : BinaryFraction) : (r.subWithWork one).1.width ≤ 4 * r.width + 10 := by
  have hw := canonicalAddWithWork_self_width r one.neg
  change (r.subWithWork one).1.width ≤ (r.subWithWork one).1.representation.storageBits at hw
  rw [subWithWork_representation, one_representation] at hw
  have hs := UnreducedRational.storageBits_sub r.representation UnreducedRational.one
  rw [UnreducedRational.storageBits_one] at hs
  have hr := representation_storageBits_le r
  omega

theorem add_one_width (r : BinaryFraction) : (canonicalAddWithWork r one).1.width ≤ 4 * r.width + 10 := by
  have hw := canonicalAddWithWork_width_le_storageBits r one
  rw [one_representation] at hw
  have hs := UnreducedRational.storageBits_add r.representation UnreducedRational.one
  rw [UnreducedRational.storageBits_one] at hs
  have hr := representation_storageBits_le r
  omega

theorem logarithmWithWork_cost (r : BinaryFraction) (K : ℕ) (hr : 0 ≤ r.value) :
    (r.logarithmWithWork K).2 ≤ logarithmBitBudget r.width K := by
  let b := logarithmRatio r
  let W := logarithmUniversalWordBudget (8 * r.width + 22) K
  have hb : |b.value| ≤ 1 := logarithmRatio_abs_le_one r hr
  have hW : logarithmPartialWordBudget b K ≤ W :=
    logarithmPartialWordBudget_le b (8 * r.width + 22) K (logarithmRatio_width r)
  have hsub := subWithWork_cost r one (r.width + 3) (by omega) (by have h := one_width; omega)
  have hadd := canonicalAddWithWork_cost r one (r.width + 3) (by omega) (by have h := one_width; omega)
  have hdiv := divWithWork_cost (r.subWithWork one).1 (canonicalAddWithWork r one).1
    (4 * r.width + 10) (sub_one_width r) (add_one_width r)
  have hpartial := logarithmPartialWithWork_cost b K hb
  have hstep := Nat.mul_le_mul_left K (logarithmPartialBitStep_mono hW K)
  have hpartial' : (b.logarithmPartialWithWork K).2 ≤ 1 + K * logarithmPartialBitStep W K := by omega
  have hpwidth := (logarithmPartialWordBudget_partial b K K le_rfl hb).trans hW
  have htwo : (nat 2).width ≤ 4 := by decide
  have hmul := canonicalMulWithWork_cost (nat 2) (b.logarithmPartialWithWork K).1
    (W + 4) (by omega) (by omega)
  change (r.subWithWork one).2 + (canonicalAddWithWork r one).2 +
    ((r.subWithWork one).1.divWithWork (canonicalAddWithWork r one).1).2 +
    (b.logarithmPartialWithWork K).2 +
    (canonicalMulWithWork (nat 2) (b.logarithmPartialWithWork K).1).2 + 5 ≤ _
  change _ ≤ 12000 * (r.width + 4) ^ 2 + 2100 * (4 * r.width + 12) ^ 2 +
    K * logarithmPartialBitStep W K + 2000 * (W + 5) ^ 2 + 10
  nlinarith only [hsub, hadd, hdiv, hpartial', hmul]

theorem powWithWork_cost_general (a : BinaryFraction) (n : ℕ) :
    (a.powWithWork n).2 ≤ 1 + n * (2000 * (generalPowerWordBudget a n + 1) ^ 2 + 1) := by
  apply powWithWork_cost_of_width
  · unfold generalPowerWordBudget
    omega
  · intro j hj
    have hw := powWithWork_width_le_storageBits a j
    rw [powWithWork_representation] at hw
    have hs := UnreducedRational.pow_storageBits a.representation j
    have hi := representation_storageBits_le a
    have hm := Nat.mul_le_mul hj.le hi
    unfold generalPowerWordBudget
    omega

theorem logarithmUniversalWordBudget_mono {A B : ℕ} (h : A ≤ B) (K : ℕ) :
    logarithmUniversalWordBudget A K ≤ logarithmUniversalWordBudget B K := by
  have hquad := Nat.mul_le_mul_left (K * K) h
  have hlin := Nat.mul_le_mul_left (2 * K + 1) h
  unfold logarithmUniversalWordBudget
  omega

theorem logarithmBitBudget_mono {A B : ℕ} (h : A ≤ B) (K : ℕ) :
    logarithmBitBudget A K ≤ logarithmBitBudget B K := by
  have hw := logarithmUniversalWordBudget_mono (show 8 * A + 22 ≤ 8 * B + 22 by omega) K
  have hs := Nat.mul_le_mul_left K (logarithmPartialBitStep_mono hw K)
  have h1 := Nat.mul_self_le_mul_self (show A + 4 ≤ B + 4 by omega)
  have h2 := Nat.mul_self_le_mul_self (show 4 * A + 12 ≤ 4 * B + 12 by omega)
  have h3 := Nat.mul_self_le_mul_self (show logarithmUniversalWordBudget (8 * A + 22) K + 5 ≤
      logarithmUniversalWordBudget (8 * B + 22) K + 5 by omega)
  simp only [← pow_two] at h1 h2 h3
  unfold logarithmBitBudget
  dsimp only
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGradientWork
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bit-operation bound for each actually materialized gradient coordinate. -/

namespace EditApproximation
namespace BinaryFraction

theorem gradientCellWithWork_cost_oai {d : ℕ} (G : ℕ) (linear point : Vector BinaryFraction d)
    (i : Fin d) (hpoint : 0 ≤ (point.get i).value) :
    (gradientCellWithWork G linear point i).2 ≤
      gradientCellBitBudget G (point.get i).width (linear.get i).width := by
  let smoothing := powWithWork (nat G) 50
  let shifted := canonicalAddWithWork (point.get i) smoothing.1.invWithWork.1
  let logarithm := logarithmWithWork shifted.1 (G ^ 60)
  let deficit := subWithWork logarithm.1.neg one
  let S := smoothingStorageBudget G
  let R := shiftedStorageBudget G (point.get i).width
  let L := gradientLogStorageBudget G (point.get i).width
  have hsm : smoothing.1.representation.storageBits ≤ S := by
    rw [powWithWork_representation, nat_representation]
    simpa only [UnreducedRational.storageBits_nat, S, smoothingStorageBudget] using
      UnreducedRational.pow_storageBits (UnreducedRational.nat G) 50
  have hsw : smoothing.1.width ≤ S := (powWithWork_width_le_storageBits (nat G) 50).trans hsm
  have his : smoothing.1.invWithWork.1.representation.storageBits ≤ S + 2 := by
    rw [invWithWork_representation]
    exact (UnreducedRational.storageBits_inv _).trans (Nat.add_le_add_right hsm 2)
  have hsi : smoothing.1.invWithWork.1.width ≤ S + 1 :=
    (invWithWork_width smoothing.1).trans (Nat.add_le_add_right hsw 1)
  have hps := representation_storageBits_le (point.get i)
  have hshift : shifted.1.representation.storageBits ≤ R := by
    change (canonicalAddWithWork (point.get i) smoothing.1.invWithWork.1).1.representation.storageBits ≤ R
    rw [canonicalAddWithWork_representation]
    have h := UnreducedRational.storageBits_add (point.get i).representation smoothing.1.invWithWork.1.representation
    dsimp only [R, shiftedStorageBudget]
    omega
  have hshiftw : shifted.1.width ≤ R := (canonicalAddWithWork_self_width _ _).trans hshift
  have hshiftpos : 0 ≤ shifted.1.value := by
    change 0 ≤ (canonicalAddWithWork (point.get i) smoothing.1.invWithWork.1).1.value
    rw [← representation_value, canonicalAddWithWork_representation, invWithWork_representation,
      powWithWork_representation, nat_representation]
    simp only [UnreducedRational.value_add, UnreducedRational.value_inv,
      UnreducedRational.value_pow, UnreducedRational.value_nat, representation_value]
    exact add_nonneg hpoint (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg G) 50))
  have hlogs : logarithm.1.representation.storageBits ≤ L := by
    rw [logarithmWithWork_representation]
    exact (UnreducedRational.logarithm_storageBits_poly shifted.1.representation (G ^ 60) hshiftpos).trans
      (UnreducedRational.logarithmStorageBudget_mono hshift _)
  have hlogw : logarithm.1.width ≤ L := (logarithmWithWork_width_le_storageBits _ _).trans hlogs
  have hdeficit : deficit.1.width ≤ 2 * L + 8 := by
    have hwidth := canonicalAddWithWork_self_width logarithm.1.neg one.neg
    change deficit.1.width ≤ deficit.1.representation.storageBits at hwidth
    rw [subWithWork_representation, neg_representation, one_representation] at hwidth
    have h := UnreducedRational.storageBits_sub logarithm.1.representation.neg UnreducedRational.one
    rw [UnreducedRational.storageBits_neg, UnreducedRational.storageBits_one] at h
    omega
  have csm := powWithWork_cost_general (nat G) 50
  have csi := invWithWork_cost smoothing.1
  have cshift := canonicalAddWithWork_cost (point.get i) smoothing.1.invWithWork.1
    ((point.get i).width + S + 1) (by omega) (by omega)
  have clog := (logarithmWithWork_cost shifted.1 (G ^ 60) hshiftpos).trans
    (logarithmBitBudget_mono hshiftw _)
  have cdef := subWithWork_cost logarithm.1.neg one (L + 3)
    (by rw [neg_width]; omega) (by have h := one_width; omega)
  have cfinal := canonicalAddWithWork_cost deficit.1 (linear.get i)
    ((linear.get i).width + 2 * L + 8) (by omega) (by omega)
  change smoothing.2 + smoothing.1.invWithWork.2 + shifted.2 + logarithm.2 + deficit.2 +
    (canonicalAddWithWork deficit.1 (linear.get i)).2 + Nat.size G + 70 ≤ _
  change _ ≤ (1 + 50 * (2000 * (generalPowerWordBudget (nat G) 50 + 1) ^ 2 + 1)) +
    (4 * S + 3) + 6000 * ((point.get i).width + S + 2) ^ 2 + logarithmBitBudget R (G ^ 60) +
    (6000 * (L + 4) ^ 2 + 1) + 6000 * ((linear.get i).width + 2 * L + 9) ^ 2 + Nat.size G + 70
  change logarithm.2 ≤ logarithmBitBudget R (G ^ 60) at clog
  change deficit.2 ≤ 6000 * (L + 3 + 1) ^ 2 + 1 at cdef
  change smoothing.2 ≤ _ at csm
  nlinarith only [csm, csi, cshift, clog, cdef, cfinal, hsw]

end BinaryFraction
end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.BinaryFraction.gradientCellWithWork_cost_oai := @OAI.EditApproximation.BinaryFraction.gradientCellWithWork_cost_oai
