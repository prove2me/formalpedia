-- Prove2me | solution 1 for OAI.EditApproximation.BinaryFraction.localWarmupKernelWithWork_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:23:25.642141+00:00
-- url     : https://prove2.me/submissions/f13ea518-d811-4ecb-a398-0666778924c6

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_07
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_bellmanWithWork_bounds
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_localRepresentativesWithWork_cost
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_wideActionGridWithWork_complete_cost

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
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
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
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
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
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
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

theorem neg_width (a : BinaryFraction) : a.neg.width = a.width := rfl

theorem subWithWork_cost (a b : BinaryFraction) (B : ℕ) (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (a.subWithWork b).2 ≤ 6000 * (B + 1) ^ 2 + 1 := by
  have h := canonicalAddWithWork_cost a b.neg B ha (by simpa only [neg_width] using hb)
  exact Nat.add_le_add_right h 1

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
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandInputs
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandInputWork
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
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
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Executed finite filters and stored fraction reductions used by the
band tests. Callback costs and list construction are included. -/

namespace EditApproximation



namespace BinaryFraction



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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryDistanceWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability
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



end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRepresentativeWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability
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

theorem endpointDistanceWithWork_bounds {n : ℕ} (q r : TargetInterval n) (B : ℕ)
    (hql : Nat.size q.lo + 2 ≤ B) (hqh : Nat.size q.hi + 2 ≤ B)
    (hrl : Nat.size r.lo + 2 ≤ B) (hrh : Nat.size r.hi + 2 ≤ B) :
    (endpointDistanceWithWork q r).1.width ≤ endpointDistanceWordBudget B ∧
      (endpointDistanceWithWork q r).2 ≤ endpointDistanceBitBudget B := by
  have hlw := distanceWithWork_width (nat q.lo) (nat r.lo) B
    ((nat_width_le _).trans hql) ((nat_width_le _).trans hrl)
  have hhw := distanceWithWork_width (nat q.hi) (nat r.hi) B
    ((nat_width_le _).trans hqh) ((nat_width_le _).trans hrh)
  have hlc := distanceWithWork_cost (nat q.lo) (nat r.lo) B
    ((nat_width_le _).trans hql) ((nat_width_le _).trans hrl)
  have hhc := distanceWithWork_cost (nat q.hi) (nat r.hi) B
    ((nat_width_le _).trans hqh) ((nat_width_le _).trans hrh)
  have hw := canonicalAddWithWork_width (distanceWithWork (nat q.lo) (nat r.lo)).1
    (distanceWithWork (nat q.hi) (nat r.hi)).1 (8 * B + 6) hlw hhw
  have hc := canonicalAddWithWork_cost (distanceWithWork (nat q.lo) (nat r.lo)).1
    (distanceWithWork (nat q.hi) (nat r.hi)).1 (8 * B + 6) hlw hhw
  constructor
  · change (canonicalAddWithWork (distanceWithWork (nat q.lo) (nat r.lo)).1
      (distanceWithWork (nat q.hi) (nat r.hi)).1).1.width ≤ endpointDistanceWordBudget B
    unfold endpointDistanceWordBudget
    omega
  · change _ + _ + _ + _ + _ + _ + _ + 3 ≤ _
    simp only [Nat.add_assoc, Nat.reduceAdd] at hc
    unfold endpointDistanceBitBudget
    omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryWideActionsWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalUniformLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full wide-action list materializes each grid and each connection
charge. Endpoint representation bounds follow from the interval subtype. -/

namespace EditApproximation
namespace BinaryFraction

theorem endpointActionWithWork_bounds {n M : ℕ} (center : TargetInterval n)
    (states : Fin M → TargetInterval n) (B : ℕ) (hn : Nat.size n + 2 ≤ B) :
    (endpointActionWithWork center states).1.connection.width ≤ connectionWordBudget M B ∧
      (endpointActionWithWork center states).2 ≤ connectionBitBudget M B + 2 * B + 2 * M + 3 := by
  have hlo : (nat center.lo).width ≤ B := (nat_width_le center.lo).trans
    ((Nat.add_le_add_right (Nat.size_le_size (center.ordered.trans center.valid)) 2).trans hn)
  have hhi : (nat center.hi).width ≤ B := (nat_width_le center.hi).trans
    ((Nat.add_le_add_right (Nat.size_le_size center.valid) 2).trans hn)
  have hs : ∀ q ∈ List.ofFn states, Nat.size q.lo + 2 ≤ B ∧ Nat.size q.hi + 2 ≤ B := by
    intro q _
    exact ⟨(Nat.add_le_add_right (Nat.size_le_size (q.ordered.trans q.valid)) 2).trans hn,
      (Nat.add_le_add_right (Nat.size_le_size q.valid) 2).trans hn⟩
  have hw := connectionWithWork_width (nat center.lo) (nat center.hi) (List.ofFn states) B hlo hhi hs
  have hc := connectionWithWork_cost (nat center.lo) (nat center.hi) (List.ofFn states) B hlo hhi hs
  simp only [List.length_ofFn] at hw hc
  constructor
  · exact hw
  · have hlo' := (Nat.size_le_size (center.ordered.trans center.valid)).trans (show Nat.size n ≤ B by omega)
    have hhi' := (Nat.size_le_size center.valid).trans (show Nat.size n ≤ B by omega)
    change (connectionWithWork (nat center.lo) (nat center.hi) (List.ofFn states)).2 +
      Nat.size center.lo + Nat.size center.hi + M + 2 + M + 1 ≤ _
    omega

theorem wideActionsFromRepresentativesWithWork_bounds {nx ny M : ℕ}
    (parent : TargetInterval nx) (representatives : List (ℕ × TargetInterval ny)) (P B : ℕ)
    (hPpos : 0 < P) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny + 2 ≤ B)
    (hM : Nat.size M ≤ B) (hP : Nat.size P ≤ B)
    (hrep : ∀ br ∈ representatives, Nat.size br.1 ≤ B) :
    (wideActionsFromRepresentativesWithWork M parent representatives P).1.length ≤
        representatives.length * (40 * P + 2) ^ (2 * M) ∧
      (∀ action ∈ (wideActionsFromRepresentativesWithWork M parent representatives P).1,
        action.connection.width ≤ connectionWordBudget M B) ∧
      (wideActionsFromRepresentativesWithWork M parent representatives P).2 ≤
        wideActionsBitBudget M P representatives.length B := by
  let V := (40 * P + 2) ^ (2 * M)
  let callback := fun br : ℕ × TargetInterval ny =>
    let grids := wideActionGridWithWork M parent br.2 br.1 P
    let actions := arithmeticMapWithWork (fun states => endpointActionWithWork br.2 states.get) grids.1
    (actions.1, grids.2 + actions.2 + 1)
  have hlen (br : ℕ × TargetInterval ny) : (wideActionGridWithWork M parent br.2 br.1 P).1.length ≤ V := by
    have hh := congrArg List.length (wideActionGridWithWork_value M parent br.2 br.1 P hPpos)
    simp only [List.length_map] at hh
    rw [hh]
    exact wideActionList_length_le M parent br.2 br.1 P hPpos
  have hc (br : ℕ × TargetInterval ny) (hbr : br ∈ representatives) :
      (callback br).2 ≤ wideMaterializationBitBudget M P B +
        V * (connectionBitBudget M B + 2 * B + 2 * M + 6) + 1 := by
    have hg := wideActionGridWithWork_complete_cost M parent br.2 br.1 P B hPpos hnx
      (by omega) hM (hrep br hbr) hP
    have hm := arithmeticMapWithWork_cost
      (fun states : Vector (TargetInterval ny) M => endpointActionWithWork br.2 states.get)
      (wideActionGridWithWork M parent br.2 br.1 P).1
      (connectionBitBudget M B + 2 * B + 2 * M + 3)
      (fun states _ => (endpointActionWithWork_bounds br.2 states.get B hny).2)
    have hm' := hm.trans (Nat.mul_le_mul_right _ (hlen br))
    change (wideActionGridWithWork M parent br.2 br.1 P).2 + _ + 1 ≤ _
    simp only [Nat.add_assoc, Nat.reduceAdd] at hm' ⊢
    omega
  have hl (br : ℕ × TargetInterval ny) : (callback br).1.length ≤ V := by
    simpa only [callback, arithmeticMapWithWork_value, List.length_map] using hlen br
  have hcost := arithmeticFlatMapWithWork_cost callback representatives
    (wideMaterializationBitBudget M P B + V * (connectionBitBudget M B + 2 * B + 2 * M + 6) + 1)
    V hc (fun br _ => hl br)
  have hlength : (representatives.flatMap (fun br => (callback br).1)).length ≤ representatives.length * V :=
    list_flatMap_length_le representatives (fun br => (callback br).1) V (fun br _ => hl br)
  refine ⟨?_, ?_, hcost⟩
  · simpa only [wideActionsFromRepresentativesWithWork, arithmeticFlatMapWithWork_value] using hlength
  · intro action ha
    simp only [wideActionsFromRepresentativesWithWork, arithmeticFlatMapWithWork_value,
      arithmeticMapWithWork_value] at ha
    obtain ⟨br, _, ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨states, _, rfl⟩ := List.mem_map.mp ha
    exact (endpointActionWithWork_bounds br.2 states.get B hny).1

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

theorem localRepresentativesWithWork_scale_bits {n : ℕ} (N P F B : ℕ) (hP : 0 < P)
    (a : BinaryFraction) (initial : TargetInterval n → BinaryFraction) (query : TargetInterval n)
    (hN : Nat.size N ≤ B) (br : ℕ × TargetInterval n)
    (hbr : br ∈ (localRepresentativesWithWork N P F a initial query).1) : Nat.size br.1 ≤ B + 2 := by
  rw [localRepresentativesWithWork_value N P F hP] at hbr
  have hb := (representativeList_conditions a.value (fun r => (initial r).value)
    (localRefinementRepresentatives_subset N P F a.value (fun r => (initial r).value) query br hbr)).1
  obtain ⟨e, he, hscale⟩ := List.mem_map.mp hb
  have hlen : Nat.log 2 N + 1 = max 1 N.bits.length := by
    simpa only [dyadicScales, List.length_map, List.length_range] using dyadicScales_length_bits N
  have her := List.mem_range.mp he
  rw [hlen, Nat.size_eq_bits_len] at her
  rw [← hscale, Nat.size_pow]
  omega

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalWarmupWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalUniformLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The warmup branch constructs its actual local representative/action
lists and evaluates their finite Bellman minimum with counted arithmetic. -/

namespace EditApproximation
namespace BinaryFraction

private theorem wideWork_mono (M P n m B : ℕ) (h : n ≤ m) :
    wideActionsBitBudget M P n B ≤ wideActionsBitBudget M P m B := by
  unfold wideActionsBitBudget
  dsimp only
  exact Nat.mul_le_mul_right _ h

private theorem bellmanWork_mono (M n m B F C : ℕ) (h : n ≤ m) :
    bellmanBitBudget M n B F C ≤ bellmanBitBudget M m B F C := by
  unfold bellmanBitBudget
  gcongr

private theorem endpointDistance_uniform_p0 {n : ℕ} (q r : TargetInterval n) (B : ℕ)
    (hn : Nat.size n + 2 ≤ B) :
    (endpointDistanceWithWork q r).1.width ≤ endpointDistanceWordBudget B ∧
      (endpointDistanceWithWork q r).2 ≤ endpointDistanceBitBudget B :=
  endpointDistanceWithWork_bounds q r B
    ((Nat.add_le_add_right (Nat.size_le_size (q.ordered.trans q.valid)) 2).trans hn)
    ((Nat.add_le_add_right (Nat.size_le_size q.valid) 2).trans hn)
    ((Nat.add_le_add_right (Nat.size_le_size (r.ordered.trans r.valid)) 2).trans hn)
    ((Nat.add_le_add_right (Nat.size_le_size r.valid) 2).trans hn)

private theorem warmupCoefficient_bounds (F B : ℕ) (hB : 10 ≤ B)
    (hF : Nat.size F + 2 ≤ B) :
    (canonicalMulWithWork (nat 128) (nat F)).1.width ≤ 4 * (B + 4) + 2 ∧
      (canonicalMulWithWork (nat 128) (nat F)).2 ≤ 2000 * (B + 5) ^ 2 := by
  have h128 : (nat 128).width ≤ B + 4 :=
    (nat_width_le 128).trans (by change 10 ≤ B + 4; omega)
  have hFw : (nat F).width ≤ B + 4 := (nat_width_le F).trans (by omega)
  exact ⟨canonicalMulWithWork_width _ _ (B + 4) h128 hFw,
    canonicalMulWithWork_cost _ _ (B + 4) h128 hFw⟩

private theorem warmupBellman_bounds {ny M : ℕ} (F B : ℕ)
    (initial : TargetInterval ny → BinaryFraction)
    (child : Fin M × TargetInterval ny → BinaryFraction) (query : TargetInterval ny)
    (actions : List (BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (hB : 10 ≤ B) (hny : Nat.size ny + 2 ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hi : ∀ r, (initial r).width ≤ B) (hc : ∀ s, (child s).width ≤ B)
    (hconn : ∀ action ∈ actions, action.connection.width ≤ connectionWordBudget M (B + 4)) :
    (bellmanWithWork endpointDistanceWithWork (canonicalMulWithWork (nat 128) (nat F)).1
      (initial query) child query actions).1.width ≤ localWarmupWordBudget M B ∧
    (bellmanWithWork endpointDistanceWithWork (canonicalMulWithWork (nat 128) (nat F)).1
      (initial query) child query actions).2 ≤ bellmanBitBudget M actions.length
      (physicalContinuationInputBudget M (B + 4)) (physicalContinuationInputBudget M (B + 4))
        (endpointDistanceBitBudget (B + 4)) := by
  let W := physicalContinuationInputBudget M (B + 4)
  have hBW : B ≤ W := by dsimp only [W, physicalContinuationInputBudget]; omega
  have hL := (warmupCoefficient_bounds F B hB hF).1
  have hWcoefficient : 4 * (B + 4) + 2 ≤ W := by
    dsimp only [W, physicalContinuationInputBudget]; omega
  exact bellmanWithWork_bounds endpointDistanceWithWork _ (initial query) child query actions W W
    (endpointDistanceBitBudget (B + 4)) (hL.trans hWcoefficient) ((hi query).trans hBW)
    (fun action _ => (endpointDistance_uniform_p0 query action.center (B + 4) (by omega)).1.trans
      (by dsimp only [W, physicalContinuationInputBudget]; omega))
    (fun action _ => (endpointDistance_uniform_p0 query action.center (B + 4) (by omega)).2)
    (fun action ha => (hconn action ha).trans (by dsimp only [W, physicalContinuationInputBudget]; omega))
    (fun action _ i => (hc _).trans hBW)

private theorem warmupWide_bounds {nx ny M : ℕ} (parent : TargetInterval nx)
    (reps : List (ℕ × TargetInterval ny)) (P F B : ℕ) (hP : 0 < P)
    (initial : TargetInterval ny → BinaryFraction)
    (child : Fin M × TargetInterval ny → BinaryFraction) (query : TargetInterval ny)
    (hB : 10 ≤ B) (hnx : Nat.size nx + 2 ≤ B) (hny : Nat.size ny + 2 ≤ B)
    (hM : Nat.size M ≤ B) (hPbits : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hrep : ∀ br ∈ reps, Nat.size br.1 ≤ B + 4)
    (hi : ∀ r, (initial r).width ≤ B) (hc : ∀ s, (child s).width ≤ B) :
    (bellmanWithWork endpointDistanceWithWork (canonicalMulWithWork (nat 128) (nat F)).1
      (initial query) child query (wideActionsFromRepresentativesWithWork M parent reps P).1).1.width ≤
        localWarmupWordBudget M B ∧
    (wideActionsFromRepresentativesWithWork M parent reps P).2 +
      (canonicalMulWithWork (nat 128) (nat F)).2 +
      (bellmanWithWork endpointDistanceWithWork (canonicalMulWithWork (nat 128) (nat F)).1
        (initial query) child query (wideActionsFromRepresentativesWithWork M parent reps P).1).2 ≤
      wideActionsBitBudget M P reps.length (B + 4) + 2000 * (B + 5) ^ 2 +
      bellmanBitBudget M (reps.length * (40 * P + 2) ^ (2 * M))
        (physicalContinuationInputBudget M (B + 4)) (physicalContinuationInputBudget M (B + 4))
        (endpointDistanceBitBudget (B + 4)) := by
  have hw := wideActionsFromRepresentativesWithWork_bounds (M := M) parent reps P (B + 4) hP
    (by omega) (by omega) (by omega) (by omega) hrep
  have hb := warmupBellman_bounds F B initial child query _ hB hny hF hi hc hw.2.1
  have hbc := hb.2.trans (bellmanWork_mono M _ _ _ _ _ hw.1)
  exact ⟨hb.1, Nat.add_le_add (Nat.add_le_add hw.2.2 (warmupCoefficient_bounds F B hB hF).2) hbc⟩

attribute [local irreducible] localRepresentativesWithWork wideActionsFromRepresentativesWithWork

theorem localWarmupKernelWithWork_bounds_oai {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F B : ℕ) (hP : 0 < P) (hFpos : 1 ≤ F) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction) (child : Fin M × TargetInterval ny → BinaryFraction)
    (query : TargetInterval ny) (hB : 10 ≤ B) (hN : Nat.size N ≤ B)
    (hnx : Nat.size nx + 2 ≤ B) (hny : Nat.size ny + 2 ≤ B)
    (hM : Nat.size M ≤ B) (hPbits : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B)
    (ha : a.width ≤ B) (hi : ∀ r, (initial r).width ≤ B) (hc : ∀ s, (child s).width ≤ B) :
    (localWarmupKernelWithWork parent N P F a initial child query).1.width ≤ localWarmupWordBudget M B ∧
      (localWarmupKernelWithWork parent N P F a initial child query).2 ≤ localWarmupBitBudget M P F B := by
  let reps := localRepresentativesWithWork N P F a initial query
  have hr := localRepresentativesWithWork_cost N P F B a initial query (by omega) hN hF hFpos
    hPbits hP (by omega) ha hi
  have hrl := localRepresentativesWithWork_length_le N P F B hP hFpos a initial query hN
  have htail := warmupWide_bounds parent reps.1 P F B hP initial child query hB hnx hny hM hPbits hF
    (fun br hbr => (localRepresentativesWithWork_scale_bits N P F B hP a initial query hN br hbr).trans (by omega)) hi hc
  have hwide := wideWork_mono M P _ ((B + 1) * (64 * F * P + 2) ^ 2) (B + 4) hrl
  have hbellman := bellmanWork_mono M _ _ (physicalContinuationInputBudget M (B + 4))
    (physicalContinuationInputBudget M (B + 4)) (endpointDistanceBitBudget (B + 4))
    (Nat.mul_le_mul_right ((40 * P + 2) ^ (2 * M)) hrl)
  refine ⟨htail.1, ?_⟩
  change reps.2 + _ + _ + _ + 3 ≤ _
  change reps.2 ≤ _ at hr
  unfold localWarmupBitBudget
  dsimp only
  simp only [reps] at htail hwide hbellman hr ⊢
  omega

end BinaryFraction
end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.BinaryFraction.localWarmupKernelWithWork_bounds_oai := @OAI.EditApproximation.BinaryFraction.localWarmupKernelWithWork_bounds_oai
