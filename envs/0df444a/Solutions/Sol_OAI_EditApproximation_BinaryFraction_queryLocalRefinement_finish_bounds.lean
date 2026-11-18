-- Prove2me | solution 1 for OAI.EditApproximation.BinaryFraction.queryLocalRefinement_finish_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:30:42.781746+00:00
-- url     : https://prove2.me/submissions/d186b18f-7408-4379-b210-116ffe1775b7

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
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea003
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_queryRefinementFinishWithWork_bounds

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
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
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







theorem neg_value (a : BinaryFraction) : a.neg.value = -a.value := by
  simp [neg, value, neg_div]

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRawOptimizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Complete materialized entropy optimizer on Boolean fraction storage.
Every arithmetic operation invokes the counted Boolean implementation. -/

namespace EditApproximation
namespace BinaryFraction

open Finset



theorem scoredArgmaxWithWork_value {α : Type*} (score : α → BinaryFraction × ℕ) (values : List α) :
    (scoredArgmaxWithWork score values).1 =
      (values.argmax (fun a => (score a).1.value)).map (fun a => (a, (score a).1)) := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
    simp only [scoredArgmaxWithWork, ih, List.argmax_cons]
    cases h : rest.argmax (fun a => (score a).1.value) with
    | none => rfl
    | some best => simp only [Option.map_some, ltWithWork_value]; split_ifs <;> rfl



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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryOnlineInputs
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The actual optimistic linear objective constructed from stored Boolean
fractions, using counted sums, products and divisions. No reduced-rational
conversion is used between the table inputs and the optimizer. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

@[simp] theorem gainWithWork_value {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (s : ℕ) (i : β × σ) :
    (gainWithWork mass table s i).1.value =
      childGain (fun j => (mass j).value) (fun t j => (table t j).value) s i := by
  simp only [gainWithWork, divWithWork_value, neg_value, childGain]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandInputWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source
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
attribute [-instance] _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupKernel
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal group estimates on gathered stored fractions. Each child/scale
comparison is executed, the supplied draw indices are reused, and ordered
selection uses the same tie rule as the mathematical group program. -/

namespace EditApproximation
namespace BinaryFraction

open Finset



@[simp] theorem selectGroupWithWork_value {ι : Type*} (members : List ι) (hne : members ≠ [])
    (estimate : ι → BinaryFraction × ℕ) :
    (selectGroupWithWork members hne estimate).1 =
      selectGroupMember members hne (fun member => (estimate member).1.value) := by
  simp only [selectGroupWithWork, scoredArgmaxWithWork_value, neg_value,
    Option.map_map, Function.comp_def, selectGroupMember]
  congr 1
  cases members.argmax (fun member => -(estimate member).1.value) <;> rfl

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalCells
attribute [-instance] _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalGroupBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded local cell loops on arbitrary initial seeds. -/

namespace EditApproximation

theorem localCellGroupActions_length {α : Type*} {M : ℕ} (source target : List α)
    (parent : TargetInterval source.length) (N P F exponent Q : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial current : Fin M → TargetInterval target.length → ℚ)
    (draw : CellGroupDraws M F Q) (q : TargetInterval target.length)
    (hF : 1 ≤ F) (hw : 0 ≤ parentInitial q) :
    (localCellGroupActions source target parent N P F exponent Q tau a parentInitial
      child initial current draw q).length ≤
      (dyadicQueryWindow N (parentInitial q) a F).length *
        ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 := by
  unfold localCellGroupActions
  apply list_flatMap_length_le
  intro b hb
  have hwindow := of_decide_eq_true (List.mem_filter.mp hb).2
  have hbpos : 1 ≤ b := by
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hb).1
    exact Nat.one_le_two_pow
  exact (List.length_filterMap_le _ _).trans
    (localTargetCells_query_length F b exponent q (parentInitial q) hF hbpos hw hwindow.1)

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryOnlineReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Online objective construction charges every historical table read,
including repeated uses in gain and decrement terms. -/

namespace EditApproximation
namespace BinaryFraction





theorem optimisticTermReadWithWork_cost {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (coefficient : BinaryFraction)
    (s : ℕ) (i : β × σ) (R : ℕ) (hs : (read s i).2 ≤ R) (hs' : (read (s + 1) i).2 ≤ R) :
    (optimisticTermReadWithWork mass read coefficient s i).2 ≤
      (optimisticTermWithWork mass (fun t j => (read t j).1) coefficient s i).2 + 3 * R := by
  simp only [optimisticTermReadWithWork, optimisticTermWithWork, gainReadWithWork,
    decrementReadWithWork, gainWithWork, decrementWithWork]
  omega



theorem onlineLinearReadWithWork_eq_cost {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (eta kappa : BinaryFraction)
    (t : ℕ) (i : β × σ) (R : ℕ) (hr : ∀ s ≤ t + 1, (read s i).2 ≤ R) :
    (onlineLinearReadWithWork mass read eta kappa t i).1 =
      (onlineLinearWithWork mass (fun s j => (read s j).1) eta kappa t i).1 ∧
    (onlineLinearReadWithWork mass read eta kappa t i).2 ≤
      (onlineLinearWithWork mass (fun s j => (read s j).1) eta kappa t i).2 + (3 * t + 1) * R := by
  have ht := vectorMapWithWork_extra t
    (fun s => optimisticTermReadWithWork mass read (coefficientWithWork kappa).1 s.val i)
    (fun s => optimisticTermWithWork mass (fun t j => (read t j).1) (coefficientWithWork kappa).1 s.val i)
    (3 * R) (fun _ => rfl) (fun s => optimisticTermReadWithWork_cost mass read _ s.val i R
      (hr _ (by omega)) (hr _ (by omega)))
  have hcur := hr t (by omega)
  unfold onlineLinearReadWithWork onlineLinearWithWork
  dsimp only
  rw [ht.1]
  refine ⟨rfl, ?_⟩
  simp only [gainReadWithWork, gainWithWork]
  nlinarith only [ht.2, hcur]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandActionReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The actual labelled online action, with charged initial and history reads. -/

namespace EditApproximation
namespace BinaryFraction




theorem countedPreparedActionReadWithWork_eq_cost {M n : ℕ} (mass : Vector BinaryFraction M)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t R : ℕ)
    (hr : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (read s ((listedBandCoordinateVector band).get i)).2 ≤ R) :
    (countedPreparedActionReadWithWork mass read eta kappa band G j t).1 =
      (countedPreparedActionWithWork mass (fun s i => (read s i).1) eta kappa band G j t).1 ∧
    (countedPreparedActionReadWithWork mass read eta kappa band G j t).2 ≤
      (countedPreparedActionWithWork mass (fun s i => (read s i).1) eta kappa band G j t).2 +
        (listedBandCoordinates band).length * ((3 * t + 1) * R) := by
  have hl := vectorMapWithWork_extra (listedBandCoordinates band).length
    (fun i => onlineLinearReadWithWork (fun j => mass.get j) read eta kappa t
      ((listedBandCoordinateVector band).get i))
    (fun i => onlineLinearWithWork (fun j => mass.get j) (fun s k => (read s k).1) eta kappa t
      ((listedBandCoordinateVector band).get i))
    ((3 * t + 1) * R)
    (fun i => (onlineLinearReadWithWork_eq_cost _ read eta kappa t _ R
      (fun s hs => hr s hs i)).1)
    (fun i => (onlineLinearReadWithWork_eq_cost _ read eta kappa t _ R
      (fun s hs => hr s hs i)).2)
  unfold countedPreparedActionReadWithWork countedPreparedActionWithWork
  simp only [coordinateVectorWithWork_value]
  rw [hl.1]
  exact ⟨rfl, by omega⟩



theorem countedBandActionReadWithWork_eq_cost {M n : ℕ} (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t R C : ℕ)
    (hi : ∀ i q, (initial i q).2 ≤ C)
    (hr : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (read s ((listedBandCoordinateVector band).get i)).2 ≤ R) :
    (countedBandActionReadWithWork b initial read eta kappa band G j t).1 =
      (countedBandActionWithWork b (fun i q => (initial i q).1)
        (fun s i => (read s i).1) eta kappa band G j t).1 ∧
    (countedBandActionReadWithWork b initial read eta kappa band G j t).2 ≤
      (countedBandActionWithWork b (fun i q => (initial i q).1)
        (fun s i => (read s i).1) eta kappa band G j t).2 +
        M * (band.length * (C + 3)) +
        (listedBandCoordinates band).length * ((3 * t + 1) * R) := by
  have hm := envelopeVectorReadWithWork_eq_cost b band initial C hi
  have hs := countedPreparedActionReadWithWork_eq_cost
    (envelopeVectorWithWork b band (fun i q => (initial i q).1)).1 read
    eta kappa band G j t R hr
  unfold countedBandActionReadWithWork countedBandActionWithWork
  dsimp only
  rw [hm.1]
  exact ⟨hs.1, by omega⟩



theorem countedSampledOnlineReadWithWork_eq_cost {n M : ℕ} (center : TargetInterval n) (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (G K t R C : ℕ) (integer : Fin (optimizerTriangularMass K))
    (hi : ∀ i q, (initial i q).2 ≤ C)
    (hr : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (read s ((listedBandCoordinateVector band).get i)).2 ≤ R) :
    (countedSampledOnlineReadWithWork center b initial read eta kappa band hne G K t integer).1 =
      (countedSampledOnlineWithWork center b (fun i q => (initial i q).1)
        (fun s i => (read s i).1) eta kappa band hne G K t integer).1 ∧
    (countedSampledOnlineReadWithWork center b initial read eta kappa band hne G K t integer).2 ≤
      (countedSampledOnlineWithWork center b (fun i q => (initial i q).1)
        (fun s i => (read s i).1) eta kappa band hne G K t integer).2 +
        M * (band.length * (C + 3)) +
        (listedBandCoordinates band).length * ((3 * t + 1) * R) := by
  have hs := countedBandActionReadWithWork_eq_cost b initial read eta kappa band G
    (triangularChoiceWithWork K integer).1.val t R C hi hr
  unfold countedSampledOnlineReadWithWork countedSampledOnlineWithWork
  dsimp only
  rw [hs.1]
  exact ⟨rfl, by omega⟩

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCountedGroup
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Group evaluation reads the exact finite sampler indexed by the count
computed from the stored rational scale. Casting indices below is proof
transport only; the emitted natural count is used by the executed loop. -/

namespace EditApproximation
namespace BinaryFraction

theorem groupMemberWithWork_transport {M T : ℕ}
    (scales : Fin T → BinaryFraction) (left right : Fin T → ℕ) (h : ∀ t, left t = right t)
    (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ t, Fin (right t) → Fin M) :
    groupMemberWithWork scales left connection envelope values (fun t j => draw t (Fin.cast (h t) j)) =
      groupMemberWithWork scales right connection envelope values draw := by
  have heq : left = right := funext h
  subst right
  rfl

@[simp] theorem countedGroupMemberWithWork_value {M T : ℕ} (Q b : ℕ) (scales : Fin T → BinaryFraction)
    (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M) :
    (countedGroupMemberWithWork Q b scales connection envelope values draw).1.value =
      groupMemberEstimate (fun t => (scales t).value) (fun t => groupSampleCount M Q b (scales t).value)
        connection.value (fun i => (envelope.get i).value) (fun i => (values.get i).value) draw := by
  unfold countedGroupMemberWithWork
  dsimp only
  rw [groupMemberWithWork_transport]
  exact groupMemberWithWork_value _ _ _ _ _ _

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySampledGroups
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sampled group continuation uses the executed envelopes, rounded
states, exact finite sample counts, and ordered minimizing scan. Its output
is the same physical action as the group program used by the accuracy proof. -/

namespace EditApproximation
namespace BinaryFraction

section Group
variable {α : Type*} (source target : List α) {M T : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ) (hb : 0 < b)
  (tau F : BinaryFraction)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
  (scales : Fin T → BinaryFraction)
  (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)

local notation "Member" => UnskippedBand source target parent b P exponent
  (BinaryFraction.value tau) (BinaryFraction.value F)
  (fun i q => BinaryFraction.value (child i q)) (fun i q => BinaryFraction.value (initial i q))

include hb in
theorem unskippedEstimateWithWork_value (member : Member) :
    (unskippedEstimateWithWork source target parent b P exponent Q tau F child initial current scales draw member).1.value =
      unskippedGroupEstimate (fun t => (scales t).value)
        (fun t => groupSampleCount M Q b (scales t).value)
        (fun i q => (current i q).value) member draw := by
  have hround : (roundedBandWithWork exponent b member.actions member.nonempty initial).1.get =
      member.rounded := roundedBandWithWork_value exponent b member.actions member.nonempty initial hb
  have hmass (i : Fin M) : ((envelopeVectorWithWork b member.actions initial).1.get i).value =
      member.envelope i := envelopeVectorWithWork_value b member.actions initial hb i
  simp only [unskippedEstimateWithWork, countedGroupMemberWithWork_value,
    endpointConnectionWithWork_value, vectorMapWithWork_value, hround, hmass, unskippedGroupEstimate]

include hb in
theorem chooseBinaryUnskippedWithWork_value (members : List Member) (hne : members ≠ []) :
    (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).1 = selectGroupMember members hne (fun member =>
        unskippedGroupEstimate (fun t => (scales t).value)
          (fun t => groupSampleCount M Q b (scales t).value)
          (fun i q => (current i q).value) member draw) := by
  simp only [chooseBinaryUnskippedWithWork, selectGroupWithWork_value,
    unskippedEstimateWithWork_value source target parent b P exponent Q hb tau F child initial current scales draw]

include hb in
theorem sampledGroupActionWithWork_value (members : List Member) (hne : members ≠ []) :
    (sampledGroupActionWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).1.decode =
      (selectGroupMember members hne (fun member =>
        unskippedGroupEstimate (fun t => (scales t).value)
          (fun t => groupSampleCount M Q b (scales t).value)
          (fun i q => (current i q).value) member draw)).rationalAction := by
  let selected : Member := (chooseBinaryUnskippedWithWork source target parent b P exponent Q
    tau F child initial current scales draw members hne).1
  have hround := roundedBandWithWork_value exponent b selected.actions selected.nonempty initial hb
  have haction : (endpointActionWithWork selected.center
      (roundedBandWithWork exponent b selected.actions selected.nonempty initial).1.get).1.decode =
      selected.rationalAction := by
    exact (endpointActionWithWork_decode _ _).trans (congrArg
      (fun states : Fin M → TargetInterval target.length =>
        (⟨selected.center, endpointActionConnection selected.center states, fun i => (i, states i)⟩ :
          PhysicalRationalAction M target.length)) hround)
  exact haction.trans (congrArg UnskippedBand.rationalAction
    (chooseBinaryUnskippedWithWork_value source target parent b P exponent Q hb tau F
      child initial current scales draw members hne))

end Group
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryDyadicSampledGroups
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The generated binary scale list is reindexed into the finite
draw domain. Only proof transport is used: the accepted draw count is the
same natural computed by `groupSampleCountWithWork`. -/

namespace EditApproximation
namespace BinaryFraction



theorem unskippedEstimate_scale_transport {α : Type*} {source target : List α} {M T : ℕ}
    {parent : TargetInterval source.length} {b P exponent Q : ℕ} {tau F : ℚ}
    {child initial : Fin M → TargetInterval target.length → ℚ}
    (left right : Fin T → ℚ) (h : left = right)
    (current : Fin M → TargetInterval target.length → ℚ)
    (member : UnskippedBand source target parent b P exponent tau F child initial)
    (draw : ∀ t, Fin (groupSampleCount M Q b (right t)) → Fin M) :
    unskippedGroupEstimate left (fun t => groupSampleCount M Q b (left t)) current member
      (fun t j => draw t (Fin.cast (congrArg (groupSampleCount M Q b) (congrFun h t)) j)) =
      unskippedGroupEstimate right (fun t => groupSampleCount M Q b (right t)) current member draw := by
  cases h
  rfl

section Physical
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ)
  (tau F : BinaryFraction)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
  (raw : List BinaryFraction) (hraw : raw.map value = groupDyadicScales M b F.value)
  (draw : ∀ t : Fin (groupDyadicScales M b F.value).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F.value t)) → Fin M)

local notation "Member" => UnskippedBand source target parent b P exponent
  (BinaryFraction.value tau) (BinaryFraction.value F)
  (fun i q => BinaryFraction.value (child i q)) (fun i q => BinaryFraction.value (initial i q))

theorem dyadicSampledGroupActionWithWork_value (members : List Member) (hne : members ≠ [])
    (hb : 0 < b) :
    (dyadicSampledGroupActionWithWork source target parent b P exponent Q tau F child initial current
      raw hraw draw members hne).1.decode =
      (chooseUnskippedGroup Q (fun i q => (current i q).value) members hne draw).rationalAction := by
  unfold dyadicSampledGroupActionWithWork
  rw [sampledGroupActionWithWork_value source target parent b P exponent Q hb]
  unfold chooseUnskippedGroup dyadicUnskippedGroupEstimate
  congr 2
  funext member
  exact unskippedEstimate_scale_transport _ _
    (funext (indexedGroupScales_value raw M b F.value hraw)) _ member draw

end Physical
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCellGroupKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One complete whole-cell group: enumerate its eligible centers, execute
every band guard, estimate all surviving members with the original finite
draws, and select the same ordered minimum. -/

namespace EditApproximation
namespace BinaryFraction

theorem cellReferenceAction_transport {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (tau a f g : ℚ) (h : f = g)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial current : Fin M → TargetInterval target.length → ℚ)
    (cell : ℕ × ℕ) (draw : cellScaleDraw M b Q f) :
    cellReferenceAction source target parent b P F exponent Q tau a f parentInitial child initial current cell draw =
      cellReferenceAction source target parent b P F exponent Q tau a g parentInitial child initial current cell
        (Eq.mp (congrArg (cellScaleDraw M b Q) h) draw) := by
  cases h
  rfl

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Group estimates and the ordered minimizing scan retain finite-table
lookup costs, using Fin-indexed source arrays. -/

namespace EditApproximation
namespace BinaryFraction

theorem scoredArgmaxWithWork_extra {α : Type*} (read plain : α → BinaryFraction × ℕ)
    (extra : α → ℕ) (xs : List α)
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 + extra x) :
    (scoredArgmaxWithWork read xs).1 = (scoredArgmaxWithWork plain xs).1 ∧
    (scoredArgmaxWithWork read xs).2 ≤
      (scoredArgmaxWithWork plain xs).2 + (xs.map extra).sum := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [scoredArgmaxWithWork, List.map_nil, List.sum_nil,
      Nat.add_zero, le_refl]⟩
  | cons x xs ih =>
    have hx := hv x List.mem_cons_self
    have hcx := hc x List.mem_cons_self
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    simp only [scoredArgmaxWithWork, ht.1, hx, List.map_cons, List.sum_cons]
    cases (scoredArgmaxWithWork plain xs).1 with
    | none => exact ⟨rfl, by dsimp only; omega⟩
    | some best => exact ⟨rfl, by dsimp only; omega⟩

theorem selectGroupWithWork_extra {α : Type*} (read plain : α → BinaryFraction × ℕ)
    (extra : α → ℕ) (xs : List α) (hne : xs ≠ [])
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 + extra x) :
    (selectGroupWithWork xs hne read).1 = (selectGroupWithWork xs hne plain).1 ∧
    (selectGroupWithWork xs hne read).2 ≤
      (selectGroupWithWork xs hne plain).2 + (xs.map extra).sum := by
  have h := scoredArgmaxWithWork_extra
    (fun x => ((read x).1.neg, (read x).2 + 1))
    (fun x => ((plain x).1.neg, (plain x).2 + 1)) extra xs
    (fun x hx => by rw [hv x hx]) (fun x hx => by have := hc x hx; omega)
  unfold selectGroupWithWork
  dsimp only
  rw [h.1]
  exact ⟨rfl, by omega⟩

section Group
variable {α : Type*} (source target : List α) {M T : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ)
  (tau F : BinaryFraction)
  (child : Fin M → TargetInterval target.length → BinaryFraction)
  (initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (scales : Fin T → BinaryFraction)
  (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)

local notation "Member" => UnskippedBand source target parent b P exponent
  (BinaryFraction.value tau) (BinaryFraction.value F)
  (fun i q => BinaryFraction.value (child i q))
  (fun i q => BinaryFraction.value (Prod.fst (initial i q)))

theorem unskippedEstimateReadWithWork_eq_cost (member : Member) (R C : ℕ)
    (hi : ∀ i q, (initial i q).2 ≤ C) (hr : ∀ i q, (current i q).2 ≤ R) :
    (unskippedEstimateReadWithWork source target parent b P exponent Q tau F child initial current
      scales draw member).1 =
      (unskippedEstimateWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw member).1 ∧
    (unskippedEstimateReadWithWork source target parent b P exponent Q tau F child initial current
      scales draw member).2 ≤
      (unskippedEstimateWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw member).2 +
      M * (member.actions.length * (C + 3)) + M * (member.actions.length * (C + 3)) + M * R := by
  have hm := envelopeVectorReadWithWork_eq_cost b member.actions initial C hi
  have hp := roundedBandReadWithWork_eq_cost exponent b member.actions member.nonempty initial C hi
  have hv := vectorMapWithWork_extra M
    (fun i => current i ((roundedBandWithWork exponent b member.actions member.nonempty
      (fun j q => (initial j q).1)).1.get i))
    (fun i => ((current i ((roundedBandWithWork exponent b member.actions member.nonempty
      (fun j q => (initial j q).1)).1.get i)).1, 1)) R (fun _ => rfl)
    (fun i => by have := hr i ((roundedBandWithWork exponent b member.actions member.nonempty
      (fun j q => (initial j q).1)).1.get i); omega)
  unfold unskippedEstimateReadWithWork unskippedEstimateWithWork
  dsimp only
  rw [hm.1, hp.1, hv.1]
  exact ⟨rfl, by omega⟩

theorem chooseUnskippedReadWithWork_eq_cost (members : List Member) (hne : members ≠ []) (R C : ℕ)
    (hi : ∀ i q, (initial i q).2 ≤ C) (hr : ∀ i q, (current i q).2 ≤ R) :
    (chooseUnskippedReadWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).1 =
      (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).1 ∧
    (chooseUnskippedReadWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).2 ≤
      (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).2 +
      (members.map fun member => M * (member.actions.length * (C + 3)) +
        M * (member.actions.length * (C + 3)) + M * R).sum := by
  exact selectGroupWithWork_extra _ _ _ members hne
    (fun member _ => (unskippedEstimateReadWithWork_eq_cost source target parent b P exponent Q
      tau F child initial current scales draw member R C hi hr).1)
    (fun member _ => by
      simpa only [Nat.add_assoc] using
        (unskippedEstimateReadWithWork_eq_cost source target parent b P exponent Q
          tau F child initial current scales draw member R C hi hr).2)

end Group
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupActionReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected group action uses the same minimizing member and rounded
endpoints, while charging both the initial and current-table readers. -/

namespace EditApproximation
namespace BinaryFraction

section Group
variable {α : Type*} (source target : List α) {M T : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ)
  (tau F : BinaryFraction)
  (child : Fin M → TargetInterval target.length → BinaryFraction)
  (initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (scales : Fin T → BinaryFraction)
  (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)

local notation "Member" => UnskippedBand source target parent b P exponent
  (BinaryFraction.value tau) (BinaryFraction.value F)
  (fun i q => BinaryFraction.value (child i q))
  (fun i q => BinaryFraction.value (Prod.fst (initial i q)))

theorem sampledGroupActionReadWithWork_eq_cost (members : List Member) (hne : members ≠ []) (R C : ℕ)
    (hi : ∀ i q, (initial i q).2 ≤ C) (hr : ∀ i q, (current i q).2 ≤ R) :
    (sampledGroupActionReadWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).1 =
      (sampledGroupActionWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).1 ∧
    (sampledGroupActionReadWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).2 ≤
      (sampledGroupActionWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).2 +
      (members.map fun member => M * (member.actions.length * (C + 3)) +
        M * (member.actions.length * (C + 3)) + M * R).sum +
      M * (((chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).1.actions).length *
        (C + 3)) := by
  have hs := chooseUnskippedReadWithWork_eq_cost source target parent b P exponent Q tau F
    child initial current scales draw members hne R C hi hr
  have hp := roundedBandReadWithWork_eq_cost exponent b
    (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child
      (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).1.actions
    (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child
      (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).1.nonempty initial C hi
  unfold sampledGroupActionReadWithWork sampledGroupActionWithWork
  dsimp only
  simp only [hs.1, hp.1]
  exact ⟨trivial, by omega⟩

end Group

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedCellGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Whole-cell selection with the prepared-grid band constructor. -/

namespace EditApproximation
namespace BinaryFraction

section Cell
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (hb : 0 < b)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
  (raw : List BinaryFraction)
  (hraw : raw.map value = groupDyadicScales M b (nat F).value)
  (draw : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → Fin M)

theorem preparedCellGroupWithWork_reference (cell : ℕ × ℕ) (hP : 0 < P) :
    ((preparedCellGroupWithWork source target parent b P F exponent Q hb tau a parentInitial child initial current
      raw hraw draw hP cell).1.map BinaryBellmanAction.decode) =
      cellReferenceAction source target parent b P F exponent Q tau.value a.value (nat F).value
        (fun q => (parentInitial q).value) (fun i q => (child i q).value)
        (fun i q => (initial i q).value) (fun i q => (current i q).value) cell draw := by
  have hcenters := cellCentersWithWork_value P F b a (inversePowerTwo exponent) parentInitial cell hP
  simp only [inversePowerTwo_value] at hcenters
  have hmembers : (filterMapWithWork
      (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau (nat F) child initial)
      (cellCentersWithWork P F b a (inversePowerTwo exponent) parentInitial cell).1).1 =
      unskippedBandList source target parent b P exponent tau.value (nat F).value
        (fun i q => (child i q).value) (fun i q => (initial i q).value)
        (cellRepresentativeStates target.length P F b a.value
          (fun q => (parentInitial q).value) ((2 : ℚ) ^ (-(exponent : ℤ))) cell) := by
    simp only [filterMapWithWork_value, preparedUnskippedCandidateWithWork_value, hcenters, unskippedBandList]
  unfold preparedCellGroupWithWork
  dsimp only
  split_ifs with hempty
  · have hnil := hempty
    rw [hmembers] at hnil
    simp only [Option.map_none, cellReferenceAction, dite_eq_left hnil]
  · rw [Option.map_some, dyadicSampledGroupActionWithWork_value source target parent b P exponent Q
      tau (nat F) child initial current raw hraw draw _ hempty hb]
    have hnonempty := hempty
    rw [hmembers] at hnonempty
    simp only [hmembers, cellReferenceAction, dite_eq_right hnonempty]

/-- The rational cell-group program at the exact natural parameter.
Transport preserves its values and changes only proof indices. -/
theorem preparedCellGroupWithWork_value (cell : ℕ × ℕ) (hP : 0 < P) :
    ((preparedCellGroupWithWork source target parent b P F exponent Q hb tau a parentInitial child initial current
      raw hraw draw hP cell).1.map BinaryBellmanAction.decode) =
      chooseCellGroupAction source target parent b P F exponent Q tau.value a.value
        (fun q => (parentInitial q).value) (fun i q => (child i q).value)
        (fun i q => (initial i q).value) (fun i q => (current i q).value) cell
        (Eq.mp (congrArg (cellScaleDraw M b Q) (nat_value F)) draw) := by
  exact (preparedCellGroupWithWork_reference source target parent b P F exponent Q hb tau a parentInitial
    child initial current raw hraw draw cell hP).trans
      (cellReferenceAction_transport source target parent b P F exponent Q tau.value a.value _ _
        (nat_value F) _ _ _ _ cell draw)

end Cell
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryUnskippedReads
attribute [-instance] _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The accepted-band record is built from the reader-aware tests.
Only proof fields are erased; numerical tests and reads remain charged. -/

namespace EditApproximation
namespace BinaryFraction

theorem preparedUnskippedReadWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau F : BinaryFraction)
    (read initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (R C : ℕ) (hr : ∀ i q, (read i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ C)
    (center : TargetInterval target.length) :
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau F read initial R C hr hi center).1 =
      (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau F
        (fun i q => (read i q).1) (fun i q => (initial i q).1) center).1 := by
  have hband := (preparedRepresentativeReadWithWork_eq_cost parent center (parent.hi - parent.lo)
    b P tau (inversePowerTwo exponent) read R hr).1
  unfold preparedUnskippedReadWithWork preparedUnskippedCandidateWithWork
  dsimp only
  simp only [hband]
  split_ifs with hempty hguard
  · rfl
  · rfl
  · rename_i hplain
    have hg := (unskippedGuardReadWithWork_eq_cost parent center b exponent F _ ((wideActionGridWithWork M parent center b P).1.map Vector.get) hempty initial C hi).1
    exact False.elim (hplain (hg.symm.trans hguard))
  · rename_i hplain
    have hg := (unskippedGuardReadWithWork_eq_cost parent center b exponent F _ ((wideActionGridWithWork M parent center b P).1.map Vector.get) hempty initial C hi).1
    exact False.elim (hguard (hg.trans hplain))
  · rfl


theorem preparedUnskippedReadWithWork_cost {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau F : BinaryFraction)
    (read initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (R C : ℕ) (hr : ∀ i q, (read i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ C)
    (center : TargetInterval target.length) :
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau F read initial R C hr hi center).2 ≤
      (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau F
        (fun i q => (read i q).1) (fun i q => (initial i q).1) center).2 +
      representativeReadOverhead M (wideActionGridWithWork M parent center b P).1.length R +
      M * ((preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
        tau (inversePowerTwo exponent) (fun i q => (read i q).1)).1.length * (C + 3)) +
      M * ((preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
        tau (inversePowerTwo exponent) (fun i q => (read i q).1)).1.length * (C + 3)) := by
  have hband := preparedRepresentativeReadWithWork_eq_cost parent center (parent.hi - parent.lo)
    b P tau (inversePowerTwo exponent) read R hr
  unfold preparedUnskippedReadWithWork preparedUnskippedCandidateWithWork
  dsimp only
  simp only [hband.1]
  by_cases hempty : (preparedRepresentativeWithWork parent center (parent.hi - parent.lo)
      b P tau (inversePowerTwo exponent) (fun i q => (read i q).1)).1 = []
  · simp only [dite_eq_left hempty]
    omega
  · simp only [dite_eq_right hempty]
    have hg := unskippedGuardReadWithWork_eq_cost parent center b exponent F
      (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
        tau (inversePowerTwo exponent) (fun i q => (read i q).1)).1
      ((wideActionGridWithWork M parent center b P).1.map Vector.get) hempty initial C hi
    simp only [hg.1]
    split_ifs <;> omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCellReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Reader-aware whole-cell construction. Every eligibility test reads its
initial word, and every accepted band and selected action uses the counted
reader kernels. -/

namespace EditApproximation

namespace BinaryFraction



theorem cellCentersReadWithWork_eq_cost {n : ℕ} (P F b : ℕ) (a theta : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction × ℕ) (cell : ℕ × ℕ)
    (R : ℕ) (hr : ∀ r, (initial r).2 ≤ R) :
    (cellCentersReadWithWork P F b a theta initial cell).1 =
      (cellCentersWithWork P F b a theta (fun r => (initial r).1) cell).1 ∧
    (cellCentersReadWithWork P F b a theta initial cell).2 ≤
      (cellCentersWithWork P F b a theta (fun r => (initial r).1) cell).2 * (R + 1) := by
  have hs := filterWithWork_add_read
    (fun r => centerEligibilityWithWork b F a (initial r).1) (fun r => (initial r).2)
    (cellStatesWithWork n (bitWordValue (seedGridSpacingWithWork b P).1)
      (canonicalMulWithWork theta (nat b)).1 cell).1 R (fun r _ => hr r)
  unfold cellCentersReadWithWork cellCentersWithWork
  dsimp only
  have he : (fun r => let word := initial r; let tested := centerEligibilityWithWork b F a word.1;
      (tested.1, word.2 + tested.2)) =
      (fun r => ((centerEligibilityWithWork b F a (initial r).1).1,
        (centerEligibilityWithWork b F a (initial r).1).2 + (initial r).2)) := by
    funext r
    simp only [Nat.add_comm]
  rw [he, hs.1]
  exact ⟨rfl, by nlinarith only [hs.2]⟩

section Cell
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (hb : 0 < b) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R C : ℕ) (hr : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ C)
  (raw : List BinaryFraction) (hraw : raw.map value = groupDyadicScales M b (nat F).value)
  (draw : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → Fin M)

theorem preparedCellGroupReadWithWork_eq (cell : ℕ × ℕ) (Rp Rc : ℕ)
    (hp : ∀ r, (parentInitial r).2 ≤ Rp) (hc : ∀ i q, (current i q).2 ≤ Rc) :
    (preparedCellGroupReadWithWork source target parent b P F exponent Q hb hP tau a
      parentInitial child initial current R C hr hi raw hraw draw cell).1 =
    (preparedCellGroupWithWork source target parent b P F exponent Q hb tau a
      (fun r => (parentInitial r).1) (fun i q => (child i q).1)
      (fun i q => (initial i q).1) (fun i q => (current i q).1) raw hraw draw hP cell).1 := by
  have hcenters := (cellCentersReadWithWork_eq_cost P F b a (inversePowerTwo exponent)
    parentInitial cell Rp hp).1
  have hm : (filterMapWithWork
      (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
        child initial R C hr hi)
      (cellCentersWithWork P F b a (inversePowerTwo exponent) (fun r => (parentInitial r).1) cell).1).1 =
    (filterMapWithWork
      (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau (nat F)
        (fun i q => (child i q).1) (fun i q => (initial i q).1))
      (cellCentersWithWork P F b a (inversePowerTwo exponent) (fun r => (parentInitial r).1) cell).1).1 := by
    simp only [filterMapWithWork_value, preparedUnskippedReadWithWork_value]
  unfold preparedCellGroupReadWithWork preparedCellGroupWithWork
  dsimp only
  simp only [hcenters, hm]
  split_ifs with hempty
  · rfl
  · apply congrArg some
    exact (sampledGroupActionReadWithWork_eq_cost source target parent b P exponent Q tau (nat F)
      (fun i q => (child i q).1) initial current _ _ _ hempty Rc C hi hc).1

end Cell
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupSourcePort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Exact finite-count source reads inside a sampled group estimator.
A source read is executed only in the sampled branch; an exact scale
uses the complete child array and makes no random-source lookup. -/

namespace EditApproximation.BinaryFraction



theorem groupScaleSourceWithWork_value {M : ℕ} (k : ℕ) (h : BinaryFraction)
    (envelope values : Vector BinaryFraction M) (draw : Fin k → Fin M × ℕ) :
    (groupScaleSourceWithWork k h envelope values draw).1 =
      (groupScaleWithWork k h envelope values (fun i => (draw i).1)).1 := by
  unfold groupScaleSourceWithWork groupScaleWithWork
  split_ifs <;> simp only [arithmeticMapWithWork_value]

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupMemberSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

namespace BinaryFraction



theorem groupMemberSourceWithWork_value {M T : ℕ} (scales : Fin T → BinaryFraction)
    (count : Fin T → ℕ) (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ s : Fin T, Fin (count s) → Fin M × ℕ) :
    (groupMemberSourceWithWork scales count connection envelope values draw).1 =
      (groupMemberWithWork scales count connection envelope values (fun s i => (draw s i).1)).1 := by
  simp only [groupMemberSourceWithWork, groupMemberWithWork, arithmeticMapWithWork_value,
    groupScaleSourceWithWork_value]

theorem countedGroupMemberSourceWithWork_value {M T : ℕ} (Q b : ℕ)
    (scales : Fin T → BinaryFraction) (connection : BinaryFraction)
    (envelope values : Vector BinaryFraction M)
    (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M × ℕ) :
    (countedGroupMemberSourceWithWork Q b scales connection envelope values draw).1 =
      (countedGroupMemberWithWork Q b scales connection envelope values (fun t i => (draw t i).1)).1 := by
  let counts := vectorMapWithWork T fun t => groupSampleCountWithWork M Q b (scales t)
  let count := fun t => bitWordValue (counts.1.get t)
  have heq : ∀ t, count t = groupSampleCount M Q b (scales t).value := by
    intro t
    simp only [count, counts, vectorMapWithWork_value, groupSampleCountWithWork_value]
  exact groupMemberSourceWithWork_value scales count connection envelope values
    (fun t j => draw t (Fin.cast (heq t) j))

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySampledSourcePort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Table-reader and random-source costs are retained together through
member estimation, tie-broken selection, and rounded action return. -/

namespace EditApproximation.BinaryFraction

section Group
variable {α : Type*} (source target : List α) {M T : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ)
  (tau F : BinaryFraction)
  (child : Fin M → TargetInterval target.length → BinaryFraction)
  (initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (scales : Fin T → BinaryFraction)
  (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M × ℕ)

local notation "Member" => UnskippedBand source target parent b P exponent (value tau) (value F)
  (fun i q => value (child i q)) (fun i q => value (Prod.fst (initial i q)))

theorem unskippedEstimateSourceWithWork_value (member : Member) :
    (unskippedEstimateSourceWithWork source target parent b P exponent Q tau F child initial current
      scales draw member).1 =
      (unskippedEstimateReadWithWork source target parent b P exponent Q tau F child initial current
        scales (fun s i => (draw s i).1) member).1 := by
  exact countedGroupMemberSourceWithWork_value Q b scales _ _ _ draw

theorem chooseUnskippedSourceWithWork_value (members : List Member) (hne : members ≠ []) :
    (chooseUnskippedSourceWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).1 =
      (chooseUnskippedReadWithWork source target parent b P exponent Q tau F child initial current
        scales (fun s i => (draw s i).1) members hne).1 := by
  simp only [chooseUnskippedSourceWithWork, chooseUnskippedReadWithWork, selectGroupWithWork_value]
  congr 1
  funext member
  rw [unskippedEstimateSourceWithWork_value]


theorem sampledGroupActionSourceWithWork_value (members : List Member) (hne : members ≠ []) :
    (sampledGroupActionSourceWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).1 =
      (sampledGroupActionReadWithWork source target parent b P exponent Q tau F child initial current
        scales (fun s i => (draw s i).1) members hne).1 := by
  let finish := fun selected : Member =>
    let rounded := roundedBandReadWithWork exponent b selected.actions selected.nonempty initial
    (endpointActionWithWork selected.center rounded.1.get).1
  change finish (chooseUnskippedSourceWithWork source target parent b P exponent Q tau F
      child initial current scales draw members hne).1 =
      finish (chooseUnskippedReadWithWork source target parent b P exponent Q tau F
        child initial current scales (fun s i => (draw s i).1) members hne).1
  exact congrArg finish (chooseUnskippedSourceWithWork_value source target parent b P exponent Q
    tau F child initial current scales draw members hne)


end Group
end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCellSourcePort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

section Cell
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (hb : 0 < b) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R C : ℕ) (hr : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ C)
  (raw : List BinaryFraction) (hraw : raw.map value = groupDyadicScales M b (nat F).value)
  (draw : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → Fin M × ℕ)

theorem preparedCellGroupSourceWithWork_value (cell : ℕ × ℕ) :
    (preparedCellGroupSourceWithWork source target parent b P F exponent Q hb hP tau a
      parentInitial child initial current R C hr hi raw hraw draw cell).1 =
      (preparedCellGroupReadWithWork source target parent b P F exponent Q hb hP tau a
        parentInitial child initial current R C hr hi raw hraw (fun t i => (draw t i).1) cell).1 := by
  unfold preparedCellGroupSourceWithWork preparedCellGroupReadWithWork
  dsimp only
  split_ifs with hempty
  · rfl
  · apply congrArg some
    exact sampledGroupActionSourceWithWork_value source target parent b P exponent Q tau (nat F)
      (fun i q => (child i q).1) initial current (indexedGroupScales raw M b (nat F).value hraw)
      (fun t j => draw t (Fin.cast (congrArg (groupSampleCount M Q b)
        (indexedGroupScales_value raw M b (nat F).value hraw t)) j)) _ hempty

end Cell
end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGatheredValues
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.countedGroupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Finite stored-word tables for gathered earlier values. The lookup scan
and the construction of every gathered warmup mean are explicit. -/

namespace EditApproximation
namespace BinaryFraction



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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedOnlineReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prepared online candidate executes its band reads, guard reads,
and historical reads. The accepted source integer and counted coordinate
representation are exactly the original ones. -/

namespace EditApproximation
namespace BinaryFraction

private theorem preparedOnlineReadCore_compare {n M : ℕ} {Action : Type*} (H integer : ℕ)
    (band plain : List (Fin M → TargetInterval n) × ℕ) (guard plainGuard : Bool × ℕ)
    (sample plainSample : (xs : List (Fin M → TargetInterval n)) → xs ≠ [] → (G : ℕ) →
      Fin (optimizerTriangularMass (G ^ 80)) → Action × ℕ)
    (B C E : ℕ) (hb : band.1 = plain.1) (hbc : band.2 ≤ plain.2 + B)
    (hg : guard.1 = plainGuard.1) (hgc : guard.2 ≤ plainGuard.2 + C)
    (hs : ∀ hne G draw, (sample plain.1 hne G draw).1 = (plainSample plain.1 hne G draw).1 ∧
      (sample plain.1 hne G draw).2 ≤ (plainSample plain.1 hne G draw).2 + E) :
    (preparedOnlineReadCore H integer band guard sample).1 =
      (preparedOnlineReadCore H integer plain plainGuard plainSample).1 ∧
    (preparedOnlineReadCore H integer band guard sample).2 ≤
      (preparedOnlineReadCore H integer plain plainGuard plainSample).2 + (B + C + E) := by
  rcases band with ⟨xs, cost⟩
  rcases plain with ⟨ys, plainCost⟩
  dsimp only at hb hbc hs ⊢
  subst ys
  unfold preparedOnlineReadCore
  dsimp only
  simp only [hg]
  split_ifs with he ha
  · exact ⟨rfl, by omega⟩
  · have hG : 0 < (onlineIndexSetupWithWork H xs).1 := by
      rw [onlineIndexSetupWithWork_value]
      omega
    have hsample := hs he (onlineIndexSetupWithWork H xs).1
      (reduceOnlineIntegerWithWork ((onlineIndexSetupWithWork H xs).1 ^ 80)
        (pow_pos hG _) integer).1
    exact ⟨congrArg some hsample.1, by omega⟩
  · exact ⟨rfl, by omega⟩

theorem preparedOnlineReadWithWork_eq_cost {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau eta kappa : BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
    (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
    (t : ℕ) (center : TargetInterval target.length) (integer : ℕ)
    (ht : ∀ s ≤ t + 1, ∀ i, (table s i).2 ≤ R) :
    (preparedOnlineReadWithWork source target parent P F exponent H b hb hP tau eta kappa
      child initial table R hc hi t center integer).1 =
      (preparedOnlineWithWork source target parent P F exponent H b hb hP tau eta kappa
        (fun i q => (child i q).1) (fun i q => (initial i q).1)
        (fun s i => (table s i).1) t center integer).1 ∧
    (preparedOnlineReadWithWork source target parent P F exponent H b hb hP tau eta kappa
      child initial table R hc hi t center integer).2 ≤
      (preparedOnlineWithWork source target parent P F exponent H b hb hP tau eta kappa
        (fun i q => (child i q).1) (fun i q => (initial i q).1)
        (fun s i => (table s i).1) t center integer).2 +
      preparedOnlineReadExtra M parent center b P exponent R t tau (fun i q => (child i q).1) := by
  have hband := preparedRepresentativeReadWithWork_eq_cost parent center (parent.hi - parent.lo)
    b P tau (inversePowerTwo exponent) child R hc
  have hguard := preparedUnskippedReadWithWork_value source target parent b P exponent hb hP
    tau (nat F) child initial R R hc hi center
  have hguardCost := preparedUnskippedReadWithWork_cost source target parent b P exponent hb hP
    tau (nat F) child initial R R hc hi center
  have h := preparedOnlineReadCore_compare H integer
    (preparedRepresentativeReadWithWork parent center (parent.hi - parent.lo) b P tau
      (inversePowerTwo exponent) child)
    (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P tau
      (inversePowerTwo exponent) (fun i q => (child i q).1))
    ((preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
      child initial R R hc hi center).1.isSome,
      (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
        child initial R R hc hi center).2)
    ((preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau (nat F)
      (fun i q => (child i q).1) (fun i q => (initial i q).1) center).1.isSome,
      (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau (nat F)
        (fun i q => (child i q).1) (fun i q => (initial i q).1) center).2)
    (fun xs hxs G draw => countedSampledOnlineReadWithWork center b initial table eta kappa
      xs hxs G (G ^ 80) t draw)
    (fun xs hxs G draw => countedSampledOnlineWithWork center b
      (fun i q => (initial i q).1) (fun s i => (table s i).1) eta kappa xs hxs G (G ^ 80) t draw)
    (representativeReadOverhead M (wideActionGridWithWork M parent center b P).1.length R)
    (representativeReadOverhead M (wideActionGridWithWork M parent center b P).1.length R +
      2 * (M * ((preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P tau
        (inversePowerTwo exponent) (fun i q => (child i q).1)).1.length * (R + 3))))
    (M * ((preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P tau
        (inversePowerTwo exponent) (fun i q => (child i q).1)).1.length * (R + 3)) +
      (listedBandCoordinates (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P tau
        (inversePowerTwo exponent) (fun i q => (child i q).1)).1).length * ((3 * t + 1) * R))
    hband.1 hband.2 (congrArg Option.isSome hguard) (by omega)
    (fun hne G draw => by
      simpa only [Nat.add_assoc] using countedSampledOnlineReadWithWork_eq_cost center b initial table eta kappa
        _ hne G (G ^ 80) t R R draw hi (fun s hs i => ht s hs _))
  refine ⟨h.1, ?_⟩
  convert h.2 using 1 <;> first
  | rfl
  | (dsimp only [preparedOnlineReadExtra, preparedOnlineWithWork, preparedOnlineReadCore]; ring)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalOnlineSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Online candidate selection charges the finite source-buffer decoder
at the point where its integer is consumed. Ineligible centers do not
read a random coordinate. -/

namespace EditApproximation.BinaryFraction
section Local
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent H : ℕ) (hP : 0 < P)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
  (t : ℕ) (integer : ℕ → TargetInterval target.length → ℕ × ℕ)

theorem preparedLocalOnlineScaleSourceWithWork_value (e : ℕ) (query : TargetInterval target.length) :
    (preparedLocalOnlineScaleSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query).1 =
      (preparedLocalOnlineScaleReadWithWork source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t (fun b q => (integer b q).1) e query).1 := by
  unfold preparedLocalOnlineScaleSourceWithWork preparedLocalOnlineScaleReadWithWork
  dsimp only
  split_ifs <;> rfl

theorem preparedLocalOnlineActionsSourceWithWork_value (N : ℕ) (query : TargetInterval target.length) :
    (preparedLocalOnlineActionsSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer N query).1 =
      (preparedLocalOnlineActionsReadWithWork source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t (fun b q => (integer b q).1) N query).1 := by
  simp only [preparedLocalOnlineActionsSourceWithWork, preparedLocalOnlineActionsReadWithWork,
    filterMapWithWork_value, preparedLocalOnlineScaleSourceWithWork_value]

end Local
end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedComputedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cell kernel constructs its rational scales from the dyadic
parameter exponents. -/

namespace EditApproximation
namespace BinaryFraction

theorem preparedComputedCellGroupWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F exponent Q eM eb eF : ℕ)
    (hM : M = 2 ^ eM) (hb : b = 2 ^ eb) (hF : F = 2 ^ eF)
    (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : cellScaleDraw M b Q (nat F).value) (cell : ℕ × ℕ) (hP : 0 < P) :
    ((preparedComputedCellGroupWithWork source target parent b P F exponent Q eM eb eF hM hb hF hP tau a
      parentInitial child initial current draw cell).1.map BinaryBellmanAction.decode) =
      chooseCellGroupAction source target parent b P F exponent Q tau.value a.value
        (fun q => (parentInitial q).value) (fun i q => (child i q).value)
        (fun i q => (initial i q).value) (fun i q => (current i q).value) cell
        (Eq.mp (congrArg (cellScaleDraw M b Q) (nat_value F)) draw) := by
  have h := preparedCellGroupWithWork_value source target parent b P F exponent Q
    (by rw [hb]; exact Nat.two_pow_pos eb) tau a parentInitial child initial current
    (groupScalesWithWork eM eb eF).1 (computedGroupScales_value M b F eM eb eF hM hb hF)
    draw cell hP
  simpa only [preparedComputedCellGroupWithWork] using h

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedLocalGroups
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Whole-cell query groups with fully constructed endpoint grids. -/

namespace EditApproximation
namespace BinaryFraction

private theorem prepared_cellDraw_roundtrip (M b Q : ℕ) (f g : ℚ) (h : f = g)
    (draw : cellScaleDraw M b Q g) :
    Eq.mp (congrArg (cellScaleDraw M b Q) h)
      (Eq.mpr (congrArg (cellScaleDraw M b Q) h) draw) = draw := by
  cases h
  rfl

theorem preparedLocalGroupScaleWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent Q eM eF eb : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P) (tau a : BinaryFraction)
    (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length) :
    ((preparedLocalGroupScaleWithWork source target parent P F exponent Q eM eF eb hM hF hP tau a
      parentInitial child initial current draw query).1.map BinaryBellmanAction.decode) =
      (localTargetCells (((2 : ℚ) ^ (-(exponent : ℤ))) * (2 ^ eb : ℕ))
        ⌈(parentInitial query).value⌉₊ query).filterMap (fun cell =>
        chooseCellGroupAction source target parent (2 ^ eb) P F exponent Q tau.value a.value
          (fun r => (parentInitial r).value) (fun i r => (child i r).value)
          (fun i r => (initial i r).value) (fun i r => (current i r).value) cell (draw (2 ^ eb) cell)) := by
  simp only [preparedLocalGroupScaleWithWork, filterMapWithWork_value, List.map_filterMap,
    targetCellsWithWork_value, canonicalMulWithWork_value, inversePowerTwo_value, nat_value,
    naturalCeilingWithWork_value]
  apply List.filterMap_congr
  intro cell _
  have hv := preparedComputedCellGroupWithWork_value source target parent (2 ^ eb) P F exponent Q eM eb eF
      hM rfl hF tau a parentInitial child initial current
      (Eq.mpr (congrArg (cellScaleDraw M (2 ^ eb) Q) (nat_value F)) (draw (2 ^ eb) cell)) cell hP
  rw [prepared_cellDraw_roundtrip M (2 ^ eb) Q (nat F).value (F : ℚ) (nat_value F)
    (draw (2 ^ eb) cell)] at hv
  exact hv

private theorem flatMap_filter_condition_p1 {α β : Type*} (p : α → Bool) (f : α → List β)
    (xs : List α) :
    xs.flatMap (fun x => if p x then f x else []) = (xs.filter p).flatMap f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.filter_cons]
    cases p x <;> simp only [Bool.false_eq_true, ↓reduceIte, List.flatMap_cons,
      List.nil_append, ih]

theorem preparedLocalCellGroupsWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q eM eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P) (tau a : BinaryFraction)
    (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length) :
    ((preparedLocalCellGroupsWithWork source target parent N P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current draw query).1.map BinaryBellmanAction.decode) =
      localCellGroupActions source target parent N P F exponent Q tau.value a.value
        (fun r => (parentInitial r).value) (fun i r => (child i r).value)
        (fun i r => (initial i r).value) (fun i r => (current i r).value) draw query := by
  let predicate := fun b : ℕ => decide ((parentInitial query).value / (16 * (F : ℚ)) ≤ b ∧
    (b : ℚ) ≤ 8 * a.value * (parentInitial query).value)
  let values := fun b : ℕ => (localTargetCells (((2 : ℚ) ^ (-(exponent : ℤ))) * b)
    ⌈(parentInitial query).value⌉₊ query).filterMap (fun cell =>
      chooseCellGroupAction source target parent b P F exponent Q tau.value a.value
        (fun r => (parentInitial r).value) (fun i r => (child i r).value)
        (fun i r => (initial i r).value) (fun i r => (current i r).value) cell (draw b cell))
  have hscale : (List.range (max 1 N.bits.length)).map (fun eb => 2 ^ eb) = dyadicScales N := by
    simpa only [dyadicScalesWithWork, arithmeticMapWithWork_value, powerTwoWord_value] using
      dyadicScalesWithWork_value N
  have hguard (eb : ℕ) : (refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query)).1 =
      predicate (2 ^ eb) := Bool.eq_iff_iff.mpr (by
        simp only [refinementScaleGuardWithWork_value, predicate, decide_eq_true_eq])
  unfold preparedLocalCellGroupsWithWork
  simp only [arithmeticFlatMapWithWork_value, List.map_flatMap]
  trans (List.range (max 1 N.bits.length)).flatMap
    (fun eb => if predicate (2 ^ eb) then values (2 ^ eb) else [])
  · apply List.flatMap_congr
    intro eb _
    by_cases hg : (refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query)).1 = true
    · have hp : predicate (2 ^ eb) = true := (hguard eb) ▸ hg
      simp only [ite_eq_left hg, ite_eq_left hp]
      exact preparedLocalGroupScaleWithWork_value source target parent P F exponent Q eM eF eb hM hF hP
        tau a parentInitial child initial current draw query
    · have hp : predicate (2 ^ eb) ≠ true := by simpa only [← hguard eb] using hg
      simp only [ite_eq_right hg, ite_eq_right hp, List.map_nil]
  · calc
      _ = ((List.range (max 1 N.bits.length)).map (fun eb => 2 ^ eb)).flatMap
          (fun b => if predicate b then values b else []) :=
        (List.flatMap_map _ _ _).symm
      _ = (((List.range (max 1 N.bits.length)).map (fun eb => 2 ^ eb)).filter predicate).flatMap
          values := flatMap_filter_condition_p1 _ _ _
      _ = _ := by rw [hscale]; rfl

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalReadValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Value preservation of local data readers does not require a chosen
work cap for arbitrary answer tables. Finite bounds used below exist only
inside these proofs and are never constructed by the algorithm. -/

namespace EditApproximation.BinaryFraction

private theorem finite_work_bound {ι : Type*} [Fintype ι] (work : ι → ℕ) :
    ∃ R, ∀ i, work i ≤ R := by
  classical
  exact ⟨∑ i, work i, fun i => Finset.single_le_sum (f := work) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)⟩

section Group
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ)
  (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)

theorem preparedComputedCellReadWithWork_value_only (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : cellScaleDraw M b Q (nat F).value) (cell : ℕ × ℕ) :
    (preparedComputedCellReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb hb draw cell).1 =
    (preparedComputedCellGroupWithWork source target parent b P F exponent Q eM eb eF hM hb hF hP
      tau a (fun r => (parentInitial r).1) (fun i q => (child i q).1)
      (fun i q => (initial i q).1) (fun i q => (current i q).1) draw cell).1 := by
  classical
  obtain ⟨Rp, hp⟩ := finite_work_bound (fun r => (parentInitial r).2)
  obtain ⟨Rc, hcur⟩ := finite_work_bound (fun iq : Fin M × TargetInterval target.length =>
    (current iq.1 iq.2).2)
  have h := preparedCellGroupReadWithWork_eq source target parent b P F exponent Q
    (by rw [hb]; exact Nat.two_pow_pos eb) hP tau a parentInitial child initial current
    R R hc hi (groupScalesWithWork eM eb eF).1
    (computedGroupScales_value M b F eM eb eF hM hb hF) draw cell Rp Rc hp
    (fun i q => hcur (i, q))
  simpa only [preparedComputedCellReadWithWork, preparedComputedCellGroupWithWork] using h

theorem preparedLocalGroupScaleReadWithWork_value_only (eb : ℕ)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length) :
    (preparedLocalGroupScaleReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi eb draw query).1 =
    (preparedLocalGroupScaleWithWork source target parent P F exponent Q eM eF eb hM hF hP tau a
      (fun r => (parentInitial r).1) (fun i q => (child i q).1)
      (fun i q => (initial i q).1) (fun i q => (current i q).1) draw query).1 := by
  simp only [preparedLocalGroupScaleReadWithWork, preparedLocalGroupScaleWithWork,
    filterMapWithWork_value]
  apply List.filterMap_congr
  intro cell _
  have h := preparedComputedCellReadWithWork_value_only source target parent P F exponent Q eM eF
    hM hF hP tau a parentInitial child initial current R hc hi (2 ^ eb) eb rfl
    (Eq.mpr (congrArg (cellScaleDraw M (2 ^ eb) Q) (nat_value F)) (draw (2 ^ eb) cell)) cell
  simpa only using h

theorem preparedLocalCellGroupsReadWithWork_value_only (N : ℕ)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length) :
    (preparedLocalCellGroupsReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi N draw query).1 =
    (preparedLocalCellGroupsWithWork source target parent N P F exponent Q eM eF hM hF hP tau a
      (fun r => (parentInitial r).1) (fun i q => (child i q).1)
      (fun i q => (initial i q).1) (fun i q => (current i q).1) draw query).1 := by
  simp only [preparedLocalCellGroupsReadWithWork, preparedLocalCellGroupsWithWork,
    arithmeticFlatMapWithWork_value]
  apply List.flatMap_congr
  intro eb _
  split_ifs
  · have h := preparedLocalGroupScaleReadWithWork_value_only source target parent P F exponent Q eM eF
      hM hF hP tau a parentInitial child initial current R hc hi eb draw query
    simpa only using h
  · rfl
end Group

section Online
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent H : ℕ) (hP : 0 < P)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
  (t : ℕ) (integer : ℕ → TargetInterval target.length → ℕ)

private theorem preparedOnlineReadWithWork_cap_irrel (b : ℕ) (hb : 0 < b)
    (R' : ℕ) (hc' : ∀ i q, (child i q).2 ≤ R') (hi' : ∀ i q, (initial i q).2 ≤ R')
    (center : TargetInterval target.length) (sample : ℕ) :
    preparedOnlineReadWithWork source target parent P F exponent H b hb hP tau eta kappa
      child initial table R hc hi t center sample =
    preparedOnlineReadWithWork source target parent P F exponent H b hb hP tau eta kappa
      child initial table R' hc' hi' t center sample := by
  rfl

theorem preparedOnlineReadWithWork_value_only (b : ℕ) (hb : 0 < b)
    (center : TargetInterval target.length) (sample : ℕ) :
    (preparedOnlineReadWithWork source target parent P F exponent H b hb hP tau eta kappa
      child initial table R hc hi t center sample).1 =
    (preparedOnlineWithWork source target parent P F exponent H b hb hP tau eta kappa
      (fun i q => (child i q).1) (fun i q => (initial i q).1)
      (fun s i => (table s i).1) t center sample).1 := by
  classical
  obtain ⟨S, hs⟩ := finite_work_bound (fun si : Fin (t + 2) × (Fin M × TargetInterval target.length) =>
    (table si.1.val si.2).2)
  let R' := max R S
  have hc' : ∀ i q, (child i q).2 ≤ R' := fun i q => (hc i q).trans (Nat.le_max_left _ _)
  have hi' : ∀ i q, (initial i q).2 ≤ R' := fun i q => (hi i q).trans (Nat.le_max_left _ _)
  rw [preparedOnlineReadWithWork_cap_irrel source target parent P F exponent H hP
    tau eta kappa child initial table R hc hi t b hb R' hc' hi' center sample]
  exact (preparedOnlineReadWithWork_eq_cost source target parent P F exponent H b hb hP
    tau eta kappa child initial table R' hc' hi' t center sample (fun s hst iq =>
      (hs (⟨s, by omega⟩, iq)).trans (Nat.le_max_right R S))).1

theorem preparedLocalOnlineScaleReadWithWork_value_only (e : ℕ) (query : TargetInterval target.length) :
    (preparedLocalOnlineScaleReadWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query).1 =
    (preparedLocalOnlineScaleWithWork source target parent P F exponent H e hP tau a eta kappa
      (fun r => (parentInitial r).1) (fun i q => (child i q).1) (fun i q => (initial i q).1)
      (fun s i => (table s i).1) t integer query).1 := by
  unfold preparedLocalOnlineScaleReadWithWork preparedLocalOnlineScaleWithWork
  dsimp only
  split_ifs
  · exact preparedOnlineReadWithWork_value_only source target parent P F exponent H hP
      tau eta kappa child initial table R hc hi t (2 ^ e) (Nat.two_pow_pos e) _ _
  · rfl

theorem preparedLocalOnlineActionsReadWithWork_value_only (N : ℕ) (query : TargetInterval target.length) :
    (preparedLocalOnlineActionsReadWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer N query).1 =
    (preparedLocalOnlineActionsWithWork source target parent N P F exponent H hP tau a eta kappa
      (fun r => (parentInitial r).1) (fun i q => (child i q).1) (fun i q => (initial i q).1)
      (fun s i => (table s i).1) t integer query).1 := by
  simp only [preparedLocalOnlineActionsReadWithWork, preparedLocalOnlineActionsWithWork,
    filterMapWithWork_value]
  apply List.filterMap_congr
  intro e _
  exact preparedLocalOnlineScaleReadWithWork_value_only source target parent P F exponent H hP
    tau a eta kappa parentInitial child initial table R hc hi t integer e query
end Online
end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalSourceValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact local source-port values for arbitrary gathered answer lists.
No cost bound on unqueried coordinates enters these identities. -/

namespace EditApproximation

private theorem sourceDraw_project_cast (M b Q : ℕ) (f g : ℚ) (h : f = g)
    (draw : cellScaleReadDraw M b Q g) :
    (fun t i => ((Eq.mpr (congrArg (cellScaleReadDraw M b Q) h) draw) t i).1) =
      Eq.mpr (congrArg (BinaryFraction.cellScaleDraw M b Q) h) (fun t i => (draw t i).1) := by
  cases h
  rfl

namespace BinaryFraction
section Group
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ)
  (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)

theorem preparedComputedCellSourceWithWork_value (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : cellScaleReadDraw M b Q (nat F).value) (cell : ℕ × ℕ) :
    (preparedComputedCellSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb hb draw cell).1 =
      (preparedComputedCellReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi b eb hb (fun t i => (draw t i).1) cell).1 := by
  have h := preparedCellGroupSourceWithWork_value source target parent b P F exponent Q
    (by rw [hb]; exact Nat.two_pow_pos eb) hP tau a parentInitial child initial current R R hc hi
    (groupScalesWithWork eM eb eF).1 (computedGroupScales_value M b F eM eb eF hM hb hF) draw cell
  simpa only [preparedComputedCellSourceWithWork, preparedComputedCellReadWithWork] using h

private theorem computedCellSource_cast_value (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : cellScaleReadDraw M b Q F) (cell : ℕ × ℕ) :
    (preparedComputedCellSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb hb
      (Eq.mpr (congrArg (cellScaleReadDraw M b Q) (nat_value F)) draw) cell).1 =
    (preparedComputedCellReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb hb
      (Eq.mpr (congrArg (cellScaleDraw M b Q) (nat_value F)) (fun t i => (draw t i).1)) cell).1 := by
  have h := preparedComputedCellSourceWithWork_value source target parent P F exponent Q eM eF
    hM hF hP tau a parentInitial child initial current R hc hi b eb hb
    (Eq.mpr (congrArg (cellScaleReadDraw M b Q) (nat_value F)) draw) cell
  rw [sourceDraw_project_cast M b Q _ _ (nat_value F) draw] at h
  exact h

theorem preparedLocalGroupScaleSourceWithWork_value (eb : ℕ)
    (draw : CellGroupReadDraws M F Q) (query : TargetInterval target.length) :
    (preparedLocalGroupScaleSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi eb draw query).1 =
      (preparedLocalGroupScaleReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi eb (fun b cell t i => (draw b cell t i).1) query).1 := by
  simp only [preparedLocalGroupScaleSourceWithWork, preparedLocalGroupScaleReadWithWork,
    filterMapWithWork_value]
  apply List.filterMap_congr
  intro cell _
  have h := computedCellSource_cast_value source target parent P F exponent Q eM eF hM hF hP tau a
    parentInitial child initial current R hc hi (2 ^ eb) eb rfl (draw (2 ^ eb) cell) cell
  simpa only using h

theorem preparedLocalCellGroupsSourceWithWork_value (N : ℕ)
    (draw : CellGroupReadDraws M F Q) (query : TargetInterval target.length) :
    (preparedLocalCellGroupsSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi N draw query).1 =
      (preparedLocalCellGroupsReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi N (fun b cell t i => (draw b cell t i).1) query).1 := by
  simp only [preparedLocalCellGroupsSourceWithWork, preparedLocalCellGroupsReadWithWork,
    arithmeticFlatMapWithWork_value]
  apply List.flatMap_congr
  intro eb _
  split_ifs
  · have h := preparedLocalGroupScaleSourceWithWork_value source target parent P F exponent Q eM eF
      hM hF hP tau a parentInitial child initial current R hc hi eb draw query
    simpa only using h
  · rfl

theorem preparedLocalCellGroupsSourceWithWork_semantic_value (N : ℕ)
    (draw : CellGroupReadDraws M F Q) (query : TargetInterval target.length) :
    (preparedLocalCellGroupsSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi N draw query).1 =
      (preparedLocalCellGroupsWithWork source target parent N P F exponent Q eM eF hM hF hP tau a
        (fun r => (parentInitial r).1) (fun i r => (child i r).1)
        (fun i r => (initial i r).1) (fun i r => (current i r).1)
        (fun b cell t i => (draw b cell t i).1) query).1 :=
  (preparedLocalCellGroupsSourceWithWork_value source target parent P F exponent Q eM eF hM hF hP tau a
    parentInitial child initial current R hc hi N draw query).trans
  (preparedLocalCellGroupsReadWithWork_value_only source target parent P F exponent Q eM eF hM hF hP tau a
    parentInitial child initial current R hc hi N (fun b cell t i => (draw b cell t i).1) query)
end Group

section Online
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent H : ℕ) (hP : 0 < P)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
  (t : ℕ) (integer : ℕ → TargetInterval target.length → ℕ × ℕ)

theorem preparedLocalOnlineActionsSourceWithWork_semantic_value (N : ℕ)
    (query : TargetInterval target.length) :
    (preparedLocalOnlineActionsSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer N query).1 =
      (preparedLocalOnlineActionsWithWork source target parent N P F exponent H hP tau a eta kappa
        (fun r => (parentInitial r).1) (fun i q => (child i q).1) (fun i q => (initial i q).1)
        (fun s i => (table s i).1) t (fun b q => (integer b q).1) query).1 :=
  (preparedLocalOnlineActionsSourceWithWork_value source target parent P F exponent H hP tau a eta kappa
    parentInitial child initial table R hc hi t integer N query).trans
  (preparedLocalOnlineActionsReadWithWork_value_only source target parent P F exponent H hP tau a eta kappa
    parentInitial child initial table R hc hi t (fun b q => (integer b q).1) N query)
end Online

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryWideActionsWork
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

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedActionStorage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every emitted group/online action carries a bounded stored connection.
This is a property of the literal constructors on every draw, without a
successful-seed event or an assumed geometric bound. -/

namespace EditApproximation
namespace BinaryFraction

private theorem optionalBranch_property {A : Type*} (p : Prop) [Decidable p]
    (emptyCost : ℕ) (selected : ¬p → A × ℕ) (selectedCost : ¬p → ℕ)
    (property : A → Prop) (hselected : ∀ h, property (selected h).1) (action : A)
    (ha : (if h : p then (none, emptyCost) else
      (some (selected h).1, selectedCost h)).1 = some action) : property action := by
  by_cases h : p
  · have hnone : (none : Option A) = some action := by
      simpa only [dite_eq_left h] using ha
    cases hnone
  · have hsome : some (selected h).1 = some action := by
      simpa only [dite_eq_right h] using ha
    exact (Option.some.inj hsome) ▸ hselected h

private theorem filterMapWithWork_property {A C : Type*}
    (callback : C → Option A × ℕ) (inputs : List C) (property : A → Prop)
    (hcallback : ∀ input action, (callback input).1 = some action → property action)
    (action : A) (ha : action ∈ (filterMapWithWork callback inputs).1) : property action := by
  rw [filterMapWithWork_value] at ha
  obtain ⟨input, _, hsome⟩ := List.mem_filterMap.mp ha
  exact hcallback input action hsome

private theorem arithmeticFlatMapWithWork_property {A C : Type*}
    (callback : C → List A × ℕ) (inputs : List C) (property : A → Prop)
    (hcallback : ∀ input action, action ∈ (callback input).1 → property action)
    (action : A) (ha : action ∈ (arithmeticFlatMapWithWork callback inputs).1) : property action := by
  rw [arithmeticFlatMapWithWork_value] at ha
  obtain ⟨input, _, hmem⟩ := List.mem_flatMap.mp ha
  exact hcallback input action hmem

private theorem conditionalList_property {A : Type*} (p : Prop) [Decidable p]
    (selected : List A × ℕ) (selectedCost emptyCost : ℕ) (property : A → Prop)
    (hselected : ∀ action ∈ selected.1, property action) (action : A)
    (ha : action ∈ (if p then (selected.1, selectedCost) else ([], emptyCost)).1) :
    property action := by
  by_cases h : p
  · have hmem : action ∈ selected.1 := by simpa only [ite_eq_left h] using ha
    exact hselected action hmem
  · have hmem : action ∈ ([] : List A) := by simpa only [ite_eq_right h] using ha
    exact False.elim (List.not_mem_nil hmem)

section Group
variable {α : Type*} (source target : List α) {M T : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ)
  (tau F : BinaryFraction)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
  (scales : Fin T → BinaryFraction)
  (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)
  (members : List (UnskippedBand source target parent b P exponent tau.value F.value
    (fun i q => (child i q).value) (fun i q => (initial i q).value))) (hne : members ≠ [])

theorem sampledGroupActionWithWork_connection (B : ℕ) (hn : Nat.size target.length + 2 ≤ B) :
    (sampledGroupActionWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).1.connection.width ≤ connectionWordBudget M B := by
  unfold sampledGroupActionWithWork
  exact (endpointActionWithWork_bounds _ _ B hn).1

end Group

section Cell
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (hb : 0 < b)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
  (raw : List BinaryFraction)
  (hraw : raw.map value = groupDyadicScales M b (nat F).value)
  (draw : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → Fin M)
  (hP : 0 < P) (cell : ℕ × ℕ)

theorem preparedCellGroupWithWork_connection
    (action : BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M)
    (ha : (preparedCellGroupWithWork source target parent b P F exponent Q hb tau a parentInitial
      child initial current raw hraw draw hP cell).1 = some action)
    (B : ℕ) (hn : Nat.size target.length + 2 ≤ B) :
    action.connection.width ≤ connectionWordBudget M B := by
  let centers := cellCentersWithWork P F b a (inversePowerTwo exponent) parentInitial cell
  let members := filterMapWithWork
    (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau (nat F) child initial)
    centers.1
  let selected := fun hne : members.1 ≠ [] =>
    dyadicSampledGroupActionWithWork source target parent b P exponent Q tau (nat F)
      child initial current raw hraw draw members.1 hne
  have hconnection (hne : members.1 ≠ []) :
      (selected hne).1.connection.width ≤ connectionWordBudget M B := by
    have hh := sampledGroupActionWithWork_connection source target parent b P exponent Q tau (nat F)
      child initial current (indexedGroupScales raw M b (nat F).value hraw)
      (fun t j => draw t (Fin.cast (congrArg (groupSampleCount M Q b)
        (indexedGroupScales_value raw M b (nat F).value hraw t)) j)) members.1 hne B hn
    simpa only [selected, dyadicSampledGroupActionWithWork] using hh
  have habranch : (if h : members.1 = [] then (none, centers.2 + members.2 + 1) else
      (some (selected h).1, centers.2 + members.2 + (selected h).2 + 2)).1 = some action := by
    simpa only [preparedCellGroupWithWork, centers, members, selected] using ha
  exact optionalBranch_property (members.1 = []) (centers.2 + members.2 + 1) selected
    (fun hne => centers.2 + members.2 + (selected hne).2 + 2)
    (fun action => action.connection.width ≤ connectionWordBudget M B) hconnection action habranch

end Cell

theorem preparedComputedCellGroupWithWork_connection {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F exponent Q eM eb eF : ℕ)
    (hM : M = 2 ^ eM) (hb : b = 2 ^ eb) (hF : F = 2 ^ eF) (hP : 0 < P)
    (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : cellScaleDraw M b Q (nat F).value) (cell : ℕ × ℕ)
    (action : BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M)
    (ha : (preparedComputedCellGroupWithWork source target parent b P F exponent Q eM eb eF
      hM hb hF hP tau a parentInitial child initial current draw cell).1 = some action)
    (B : ℕ) (hn : Nat.size target.length + 2 ≤ B) :
    action.connection.width ≤ connectionWordBudget M B := by
  have hcell : (preparedCellGroupWithWork source target parent b P F exponent Q
      (by rw [hb]; exact Nat.two_pow_pos eb) tau a parentInitial child initial current
      (groupScalesWithWork eM eb eF).1 (computedGroupScales_value M b F eM eb eF hM hb hF)
      draw hP cell).1 = some action := by
    simpa only [preparedComputedCellGroupWithWork] using ha
  exact preparedCellGroupWithWork_connection source target parent b P F exponent Q
    (by rw [hb]; exact Nat.two_pow_pos eb) tau a parentInitial child initial current
    (groupScalesWithWork eM eb eF).1 (computedGroupScales_value M b F eM eb eF hM hb hF)
    draw hP cell action hcell B hn

theorem preparedLocalGroupScaleWithWork_connection {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent Q eM eF eb : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P)
    (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length)
    (B : ℕ) (hn : Nat.size target.length + 2 ≤ B)
    (action : BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M)
    (ha : action ∈ (preparedLocalGroupScaleWithWork source target parent P F exponent Q eM eF eb
      hM hF hP tau a parentInitial child initial current draw query).1) :
    action.connection.width ≤ connectionWordBudget M B := by
  let cellDraw := fun cell : ℕ × ℕ =>
    Eq.mpr (congrArg (cellScaleDraw M (2 ^ eb) Q) (nat_value F)) (draw (2 ^ eb) cell)
  let callback := fun cell : ℕ × ℕ =>
    preparedComputedCellGroupWithWork source target parent (2 ^ eb) P F exponent Q eM eb eF
      hM rfl hF hP tau a parentInitial child initial current (cellDraw cell) cell
  let cells := (targetCellsWithWork
    (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
    (bitWordValue (naturalCeilingWithWork (parentInitial query)).1) query).1
  have hcallback (cell : ℕ × ℕ)
      (result : BinaryBellmanAction (TargetInterval target.length)
        (Fin M × TargetInterval target.length) M)
      (hresult : (callback cell).1 = some result) :
      result.connection.width ≤ connectionWordBudget M B := by
    have hcell : (preparedComputedCellGroupWithWork source target parent (2 ^ eb) P F exponent Q eM eb eF
        hM rfl hF hP tau a parentInitial child initial current (cellDraw cell) cell).1 = some result := by
      simpa only [callback] using hresult
    have hh := preparedComputedCellGroupWithWork_connection source target parent (2 ^ eb) P F exponent Q eM eb eF
      hM rfl hF hP tau a parentInitial child initial current (cellDraw cell) cell result hcell B hn
    exact hh
  have hfiltered : action ∈ (filterMapWithWork callback cells).1 := by
    simpa only [preparedLocalGroupScaleWithWork, callback, cells, cellDraw] using ha
  exact filterMapWithWork_property callback cells
    (fun result => result.connection.width ≤ connectionWordBudget M B) hcallback action hfiltered

theorem preparedLocalCellGroupsWithWork_connection {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q eM eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P)
    (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length)
    (B : ℕ) (hn : Nat.size target.length + 2 ≤ B)
    (action : BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M)
    (ha : action ∈ (preparedLocalCellGroupsWithWork source target parent N P F exponent Q eM eF
      hM hF hP tau a parentInitial child initial current draw query).1) :
    action.connection.width ≤ connectionWordBudget M B := by
  let callback := fun eb : ℕ =>
    let guard := refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query)
    if guard.1 then
      let selected := preparedLocalGroupScaleWithWork source target parent P F exponent Q eM eF eb
        hM hF hP tau a parentInitial child initial current draw query
      (selected.1, guard.2 + selected.2 + eb + 4)
    else ([], guard.2 + eb + 4)
  have hcallback (eb : ℕ)
      (result : BinaryBellmanAction (TargetInterval target.length)
        (Fin M × TargetInterval target.length) M)
      (hresult : result ∈ (callback eb).1) :
      result.connection.width ≤ connectionWordBudget M B := by
    let guard := refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query)
    let selected := preparedLocalGroupScaleWithWork source target parent P F exponent Q eM eF eb
      hM hF hP tau a parentInitial child initial current draw query
    have hguarded : result ∈ (if guard.1 = true then
        (selected.1, guard.2 + selected.2 + eb + 4) else ([], guard.2 + eb + 4)).1 := by
      simpa only [callback, guard, selected] using hresult
    exact conditionalList_property (guard.1 = true) selected
      (guard.2 + selected.2 + eb + 4) (guard.2 + eb + 4)
      (fun result => result.connection.width ≤ connectionWordBudget M B)
      (fun result hmem => preparedLocalGroupScaleWithWork_connection source target parent P F exponent Q
        eM eF eb hM hF hP tau a parentInitial child initial current draw query B hn result hmem)
      result hguarded
  have hflat : action ∈ (arithmeticFlatMapWithWork callback (List.range (max 1 N.bits.length))).1 := by
    simpa only [preparedLocalCellGroupsWithWork, callback] using ha
  exact arithmeticFlatMapWithWork_property callback (List.range (max 1 N.bits.length))
    (fun result => result.connection.width ≤ connectionWordBudget M B) hcallback action hflat

theorem preparedOnlineWithWork_connection {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau eta kappa : BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction)
    (t : ℕ) (center : TargetInterval target.length) (integer : ℕ)
    (action : BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M)
    (ha : (preparedOnlineWithWork source target parent P F exponent H b hb hP tau eta kappa child initial
      table t center integer).1 = some action) : action.connection = zero := by
  unfold preparedOnlineWithWork at ha
  dsimp only at ha
  split_ifs at ha with hempty hactive
  cases ha
  rfl

theorem preparedLocalOnlineActionsWithWork_connection {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H : ℕ) (hP : 0 < P)
    (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (query : TargetInterval target.length)
    (action : BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M)
    (ha : action ∈ (preparedLocalOnlineActionsWithWork source target parent N P F exponent H hP tau a
      eta kappa parentInitial child initial table t integer query).1) : action.connection = zero := by
  simp only [preparedLocalOnlineActionsWithWork, filterMapWithWork_value] at ha
  obtain ⟨eb, _, hmem⟩ := List.mem_filterMap.mp ha
  unfold preparedLocalOnlineScaleWithWork at hmem
  dsimp only at hmem
  split_ifs at hmem with heligible
  exact preparedOnlineWithWork_connection source target parent P F exponent H (2 ^ eb)
    (Nat.two_pow_pos _) hP tau eta kappa child initial table t _ _ action hmem

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedListBounds
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

theorem queryExponentsWithWork_length_le (N F B : ℕ) (a w : BinaryFraction)
    (hN : Nat.size N ≤ B) : (queryExponentsWithWork N F a w).1.length ≤ B + 1 := by
  change (filterWithWork _ (List.range (max 1 N.bits.length))).1.length ≤ _
  rw [filterWithWork_value]
  apply (List.length_filter_le _ _).trans
  rw [List.length_range, Nat.size_eq_bits_len]
  omega

theorem preparedLocalCellGroupsWithWork_length_le {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q eM eF B : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P) (tau a : BinaryFraction)
    (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length)
    (hN : Nat.size N ≤ B) (hw : 0 ≤ (parentInitial query).value) :
    (preparedLocalCellGroupsWithWork source target parent N P F exponent Q eM eF hM hF hP
      tau a parentInitial child initial current draw query).1.length ≤
      (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 := by
  have hv := congrArg List.length (preparedLocalCellGroupsWithWork_value source target parent
    N P F exponent Q eM eF hM hF hP tau a parentInitial child initial current draw query)
  rw [List.length_map] at hv
  rw [hv]
  apply (localCellGroupActions_length source target parent N P F exponent Q tau.value a.value
    (fun r => (parentInitial r).value) (fun i r => (child i r).value)
    (fun i r => (initial i r).value) (fun i r => (current i r).value) draw query
    (by rw [hF]; exact Nat.one_le_two_pow) hw).trans
  apply Nat.mul_le_mul_right
  apply (List.length_filter_le _ _).trans
  rw [dyadicScales_length_bits, Nat.size_eq_bits_len]
  omega

theorem preparedLocalOnlineActionsWithWork_length_le {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H B : ℕ) (hP : 0 < P)
    (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (query : TargetInterval target.length)
    (hN : Nat.size N ≤ B) :
    (preparedLocalOnlineActionsWithWork source target parent N P F exponent H hP tau a eta kappa
      parentInitial child initial table t integer query).1.length ≤ B + 1 := by
  change (filterMapWithWork _ (queryExponentsWithWork N F a (parentInitial query)).1).1.length ≤ _
  rw [filterMapWithWork_value]
  exact (List.length_filterMap_le _ _).trans (queryExponentsWithWork_length_le N F B a _ hN)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GatheredLocalStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The current-index part of a local step can be evaluated in two
stages: gather the shared sampled inputs, select the whole-cell actions,
then gather their actual costs and the online action costs. -/

namespace EditApproximation

open Finset

theorem orderedInputs_length {ι : Type*} [DecidableEq ι] (encode : ι → ℕ)
    (hinjective : Function.Injective encode) (inputs : Finset ι) :
    (orderedInputs encode hinjective inputs).length = inputs.card := by
  let _ : LinearOrder ι := LinearOrder.lift' encode hinjective
  exact Finset.length_sort (r := (· ≤ ·))

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





theorem queryEraseLoopWithWork_value {α : Type*} [BEq α] [LawfulBEq α]
    (equal : α → α → Bool × ℕ) (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (xs seen : List α) :
    (queryEraseLoopWithWork equal xs seen).1 = List.eraseDupsBy.loop (· == ·) xs seen := by
  induction xs generalizing seen with
  | nil => rfl
  | cons a xs ih =>
    have ht : (memberByWithWork equal a seen).1 = seen.any (a == ·) := by
      apply Bool.eq_iff_iff.mpr
      simp only [memberByWithWork_value equal heq, List.any_eq_true, beq_iff_eq]
      exact ⟨fun h => ⟨a, h, rfl⟩, fun ⟨b, hb, hab⟩ => hab ▸ hb⟩
    simp only [queryEraseLoopWithWork, ht, ih, List.eraseDupsBy.loop]
    cases seen.any (a == ·) <;> rfl

@[simp] theorem queryEraseWithWork_value {α : Type*} [BEq α] [LawfulBEq α]
    (equal : α → α → Bool × ℕ) (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (xs : List α) : (queryEraseWithWork equal xs).1 = xs.eraseDups :=
  queryEraseLoopWithWork_value equal heq xs []

theorem queryEraseLoopWithWork_nodup {α : Type*}
    (equal : α → α → Bool × ℕ) (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (xs seen : List α) (hs : seen.Nodup) :
    (queryEraseLoopWithWork equal xs seen).1.Nodup := by
  induction xs generalizing seen with
  | nil => simpa only [queryEraseLoopWithWork, List.nodup_reverse] using hs
  | cons a xs ih =>
    change (queryEraseLoopWithWork equal xs
      (if (memberByWithWork equal a seen).1 then seen else a :: seen)).1.Nodup
    by_cases h : (memberByWithWork equal a seen).1 = true
    · rw [ite_eq_left h]
      exact ih seen hs
    · rw [ite_eq_right h]
      apply ih
      exact List.nodup_cons.mpr ⟨fun ha => h ((memberByWithWork_value equal heq a seen).mpr ha), hs⟩

theorem queryEraseWithWork_nodup {α : Type*}
    (equal : α → α → Bool × ℕ) (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (xs : List α) : (queryEraseWithWork equal xs).1.Nodup :=
  queryEraseLoopWithWork_nodup equal heq xs [] (by simp)

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryOrderedInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Counted insertion sorting for the distinct-key lists. The numerical
encoding determines exactly the order used by the reference query. -/

namespace EditApproximation





theorem queryInsertWithWork_value {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (le : α → α → Bool × ℕ) (hle : ∀ a b, (le a b).1 = decide (r a b))
    (a : α) (xs : List α) :
    (queryInsertWithWork le a xs).1 = List.orderedInsert r a xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [queryInsertWithWork, hle, List.orderedInsert_cons, decide_eq_true_eq]
    split <;> simp only [ih]

theorem querySortWithWork_value {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (le : α → α → Bool × ℕ) (hle : ∀ a b, (le a b).1 = decide (r a b)) (xs : List α) :
    (querySortWithWork le xs).1 = xs.insertionSort r := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [querySortWithWork, queryInsertWithWork_value r le hle, ih, List.insertionSort_cons]

theorem queryInsertWithWork_cost {α : Type*} (le : α → α → Bool × ℕ)
    (C : ℕ) (hC : ∀ a b, (le a b).2 ≤ C) (a : α) (xs : List α) :
    (queryInsertWithWork le a xs).2 ≤ (xs.length + 1) * (C + 2) := by
  induction xs with
  | nil => simp only [queryInsertWithWork, List.length_nil]; omega
  | cons b xs ih =>
    have h := hC a b
    simp only [queryInsertWithWork, List.length_cons]
    split <;> dsimp only
    · nlinarith only [h, Nat.zero_le xs.length, Nat.zero_le C]
    · nlinarith only [h, ih]

theorem querySortWithWork_cost {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (le : α → α → Bool × ℕ) (hle : ∀ a b, (le a b).1 = decide (r a b))
    (C : ℕ) (hC : ∀ a b, (le a b).2 ≤ C) (xs : List α) :
    (querySortWithWork le xs).2 ≤ (xs.length + 1) ^ 2 * (C + 3) := by
  induction xs with
  | nil => simp only [querySortWithWork, List.length_nil]; omega
  | cons a xs ih =>
    have hi := queryInsertWithWork_cost le C hC a (querySortWithWork le xs).1
    have hl : (querySortWithWork le xs).1.length = xs.length := by
      rw [querySortWithWork_value r le hle, List.length_insertionSort]
    rw [hl] at hi
    change (querySortWithWork le xs).2 + _ + 1 ≤ _
    simp only [List.length_cons]
    nlinarith only [ih, hi, Nat.zero_le xs.length, Nat.zero_le C]



theorem queryOrderedInputsWithWork_value {α : Type*} [DecidableEq α]
    (encode : α → ℕ) (hinjective : Function.Injective encode)
    (equal le : α → α → Bool × ℕ)
    (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (hle : ∀ a b, (le a b).1 = decide (encode a ≤ encode b)) (xs : List α) :
    (queryOrderedInputsWithWork equal le xs).1 = orderedInputs encode hinjective xs.toFinset := by
  let : LinearOrder α := LinearOrder.lift' encode hinjective
  have hle' : ∀ a b, (le a b).1 = decide (a ≤ b) := hle
  rw [queryOrderedInputsWithWork, querySortWithWork_value (· ≤ ·) le hle',
    queryEraseWithWork_value equal heq]
  have hd := queryEraseWithWork_nodup equal heq xs
  rw [queryEraseWithWork_value equal heq] at hd
  have hn : (xs.eraseDups.insertionSort (· ≤ ·)).Nodup :=
    (List.perm_insertionSort (· ≤ ·) xs.eraseDups).nodup_iff.mpr hd
  have hs := (List.toFinset_sort (r := (· ≤ ·)) hn).mpr
    (List.pairwise_insertionSort (· ≤ ·) xs.eraseDups)
  have hf : (xs.eraseDups.insertionSort (· ≤ ·)).toFinset = xs.toFinset := by
    ext x
    simp only [List.mem_toFinset, List.mem_insertionSort, List.mem_eraseDups]
  rw [hf] at hs
  exact hs.symm

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInputCodes
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Boolean arithmetic for the existing child/history key encodings.
The sorting comparison charges both encodings and the word comparison. -/

namespace EditApproximation



theorem queryEncodedLEWithWork_value {α : Type*} (code : α → ℕ × ℕ) (a b : α) :
    (queryEncodedLEWithWork code a b).1 = decide ((code a).1 ≤ (code b).1) := by
  apply Bool.eq_iff_iff.mpr
  simp only [queryEncodedLEWithWork, wordLEWithWork_value, bitWordValue_bits, decide_eq_true_eq]



@[simp] theorem queryOrderedChildInputsWithWork_value {M n : ℕ}
    (inputs : List (Fin M × TargetInterval n)) :
    (queryOrderedChildInputsWithWork inputs).1 =
      orderedInputs childInputCode (childInputCode_injective M n) inputs.toFinset := by
  apply queryOrderedInputsWithWork_value childInputCode (childInputCode_injective M n)
    _ _ coordinateEqualWithWork_value
  intro a b
  simp only [queryEncodedLEWithWork_value, queryChildCodeWithWork_value]



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

theorem queryOrderedInputsWithWork_cost {α : Type*}
    (encode : α → ℕ) (equal le : α → α → Bool × ℕ)
    (hle : ∀ a b, (le a b).1 = decide (encode a ≤ encode b))
    (C D : ℕ) (hequal : ∀ a b, (equal a b).2 ≤ C) (horder : ∀ a b, (le a b).2 ≤ D)
    (xs : List α) :
    (queryOrderedInputsWithWork equal le xs).2 ≤
      (xs.length + 1) ^ 2 * (C + D + 8) := by
  have he := queryEraseWithWork_cost equal C hequal xs
  have hs := querySortWithWork_cost (fun a b => encode a ≤ encode b) le hle D horder
    (queryEraseWithWork equal xs).1
  have hl := queryEraseWithWork_length equal xs
  have hp : ((queryEraseWithWork equal xs).1.length + 1) ^ 2 ≤ (xs.length + 1) ^ 2 := by
    gcongr
  have hb := hs.trans (Nat.mul_le_mul_right (D + 3) hp)
  change (queryEraseWithWork equal xs).2 + _ + 1 ≤ _
  nlinarith only [he, hb, Nat.zero_le C, Nat.zero_le D, Nat.zero_le xs.length]

theorem queryEncodedLEWithWork_cost {α : Type*} (code : α → ℕ × ℕ)
    (a b : α) (C B : ℕ) (ha : (code a).2 ≤ C) (hb : (code b).2 ≤ C)
    (hva : Nat.size (code a).1 ≤ B) (hvb : Nat.size (code b).1 ≤ B) :
    (queryEncodedLEWithWork code a b).2 ≤ 2 * C + 10 * B + 5 := by
  have hc := wordLEWithWork_cost (code a).1.bits (code b).1.bits
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len] at hc
  change _ + _ + _ + _ + _ + 3 ≤ _
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryCodeBounds
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Key encoding uses only a fixed number of natural-word operations.
Its word sizes and Boolean work are polynomial in the coordinate widths. -/

namespace EditApproximation

theorem queryNaturalAdd_size (a b : ℕ) : Nat.size (a + b) ≤ Nat.size a + Nat.size b + 1 := by
  have h := bitAddWithWork_length a.bits b.bits false
  have hs := Nat.size_le.mpr (bitWordValue_lt_pow_length (binaryNaturalAddWithWork a b).1)
  rw [binaryNaturalAddWithWork_value] at hs
  simp only [binaryNaturalAddWithWork] at hs
  simp only [Nat.size_eq_bits_len] at h
  omega

theorem queryNaturalMul_size (a b : ℕ) : Nat.size (a * b) ≤ 2 * Nat.size a + Nat.size b + 1 := by
  have h := bitMulWithWork_length a.bits b.bits
  have hs := Nat.size_le.mpr (bitWordValue_lt_pow_length (binaryNaturalMulWithWork a b).1)
  rw [binaryNaturalMulWithWork_value] at hs
  simp only [binaryNaturalMulWithWork] at hs
  simp only [Nat.size_eq_bits_len] at h
  omega

theorem queryNaturalAdd_cost (a b K : ℕ) (ha : Nat.size a ≤ K) (hb : Nat.size b ≤ K) :
    (binaryNaturalAddWithWork a b).2 ≤ 18 * K + 1 := by
  have h := binaryNaturalAddWithWork_cost a b
  omega

theorem queryNaturalMul_cost (a b K : ℕ) (ha : Nat.size a ≤ K) (hb : Nat.size b ≤ K) :
    (binaryNaturalMulWithWork a b).2 ≤ 20 * (K + 1) * (2 * K + 1) := by
  apply (binaryNaturalMulWithWork_cost a b).trans
  gcongr
  omega

theorem queryChildCodeWithWork_bounds {M n : ℕ} (input : Fin M × TargetInterval n)
    (B : ℕ) (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    Nat.size (queryChildCodeWithWork input).1 ≤ 8 * (B + 1) ∧
      (queryChildCodeWithWork input).2 ≤ 100000 * (B + 1) ^ 2 := by
  have hi : Nat.size input.1.val ≤ B := (Nat.size_le_size input.1.isLt.le).trans hM
  have hl : Nat.size input.2.lo ≤ B :=
    (Nat.size_le_size (input.2.ordered.trans input.2.valid)).trans hn
  have hh : Nat.size input.2.hi ≤ B := (Nat.size_le_size input.2.valid).trans hn
  have hw : Nat.size (n + 1) ≤ B + 2 := by
    have h := queryNaturalAdd_size n 1
    norm_num only [Nat.size_one] at h
    omega
  have hhigh : Nat.size ((n + 1) * input.2.hi) ≤ 3 * B + 5 := by
    have h := queryNaturalMul_size (n + 1) input.2.hi
    omega
  have hcoord : Nat.size (input.2.lo + (n + 1) * input.2.hi) ≤ 4 * B + 6 := by
    have h := queryNaturalAdd_size input.2.lo ((n + 1) * input.2.hi)
    omega
  have hscaled : Nat.size (M * (input.2.lo + (n + 1) * input.2.hi)) ≤ 6 * B + 7 := by
    have h := queryNaturalMul_size M (input.2.lo + (n + 1) * input.2.hi)
    omega
  have hout : Nat.size (input.1.val + M * (input.2.lo + (n + 1) * input.2.hi)) ≤ 7 * B + 8 := by
    have h := queryNaturalAdd_size input.1.val (M * (input.2.lo + (n + 1) * input.2.hi))
    omega
  constructor
  · rw [queryChildCodeWithWork_value]
    exact hout.trans (by omega)
  · let K := 8 * (B + 1)
    have h1 : Nat.size 1 ≤ K := by norm_num only [Nat.size_one]; dsimp [K]; omega
    have hN : Nat.size n ≤ K := by dsimp [K]; omega
    have hW : Nat.size (n + 1) ≤ K := by dsimp [K]; omega
    have hI : Nat.size input.1.val ≤ K := by dsimp [K]; omega
    have hL : Nat.size input.2.lo ≤ K := by dsimp [K]; omega
    have hH : Nat.size input.2.hi ≤ K := by dsimp [K]; omega
    have hM' : Nat.size M ≤ K := by dsimp [K]; omega
    have hHigh : Nat.size ((n + 1) * input.2.hi) ≤ K := by dsimp [K]; omega
    have hCoord : Nat.size (input.2.lo + (n + 1) * input.2.hi) ≤ K := by dsimp [K]; omega
    have hScaled : Nat.size (M * (input.2.lo + (n + 1) * input.2.hi)) ≤ K := by dsimp [K]; omega
    have c1 := queryNaturalAdd_cost n 1 K hN h1
    have c2 := queryNaturalMul_cost (n + 1) input.2.hi K hW hH
    have c3 := queryNaturalAdd_cost input.2.lo ((n + 1) * input.2.hi) K hL hHigh
    have c4 := queryNaturalMul_cost M (input.2.lo + (n + 1) * input.2.hi) K hM' hCoord
    have c5 := queryNaturalAdd_cost input.1.val (M * (input.2.lo + (n + 1) * input.2.hi)) K hI hScaled
    simp only [queryChildCodeWithWork, binaryNaturalAddWithWork_value, binaryNaturalMulWithWork_value]
    dsimp only [K] at c1 c2 c3 c4 c5
    nlinarith only [c1, c2, c3, c4, c5, Nat.zero_le B]

theorem queryChildOrderWithWork_cost {M n : ℕ} (a b : Fin M × TargetInterval n)
    (B : ℕ) (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    (queryEncodedLEWithWork queryChildCodeWithWork a b).2 ≤ 201000 * (B + 1) ^ 2 := by
  have ha := queryChildCodeWithWork_bounds a B hM hn
  have hb := queryChildCodeWithWork_bounds b B hM hn
  have h := queryEncodedLEWithWork_cost queryChildCodeWithWork a b
    (100000 * (B + 1) ^ 2) (8 * (B + 1)) ha.2 hb.2 ha.1 hb.1
  nlinarith only [h, Nat.zero_le B]

theorem queryOrderedChildInputsWithWork_cost {M n : ℕ} (inputs : List (Fin M × TargetInterval n))
    (B : ℕ) (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    (queryOrderedChildInputsWithWork inputs).2 ≤
      (inputs.length + 1) ^ 2 * (202000 * (B + 1) ^ 2) := by
  have h := queryOrderedInputsWithWork_cost childInputCode coordinateEqualWithWork
    (queryEncodedLEWithWork queryChildCodeWithWork)
    (fun a b => by simp only [queryEncodedLEWithWork_value, queryChildCodeWithWork_value])
    (24 * B + 8) (201000 * (B + 1) ^ 2)
    (fun a b => coordinateEqualWithWork_cost a b B hM hn)
    (fun a b => queryChildOrderWithWork_cost a b B hM hn) inputs
  apply h.trans
  gcongr
  nlinarith only [Nat.zero_le B]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInitialSupport
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOrderedChildInputsWithWork_value _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Executed Boolean construction of the first adaptive refinement lists.
Their values are the original lists, including ordering and repetitions. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem queryRawCentersWithWork_value {n : ℕ} (N P F : ℕ) (hP : 0 < P)
    (a value : BinaryFraction) (q : TargetInterval n) :
    (queryRawCentersWithWork N P F a value q).1 =
      rawRefinementCenters N P F a.value value.value q := by
  have hg (b : ℕ) : (gridStateBoxWithWork n (seedGridSpacing b P)
      ⌈value.value⌉₊ q.lo q.hi).1 = localTargetStates n (seedGridSpacing b P) ⌈value.value⌉₊ q := by
    rw [gridStateBoxWithWork_value _ _ _ _ _ (by unfold seedGridSpacing; omega)]
    rfl
  simp only [queryRawCentersWithWork, queryEraseWithWork_value _ queryIntervalEqualWithWork_value,
    arithmeticFlatMapWithWork_value, seedGridSpacingWithWork_value _ _ hP,
    naturalCeilingWithWork_value, hg, queryScalesWithWork_value, rawRefinementCenters]



@[simp] theorem queryInitialSupportWithWork_value {n : ℕ} (N P F exponent : ℕ) (hP : 0 < P)
    (a value : BinaryFraction) (q : TargetInterval n) :
    (queryInitialSupportWithWork N P F exponent hP a value q).1 =
      refinementInitialSupport N P F exponent a.value value.value q := by
  simp only [queryInitialSupportWithWork, queryRawCentersWithWork_value _ _ _ hP,
    arithmeticFlatMapWithWork_value, arithmeticMapWithWork_value, cellStatesWithWork_value,
    seedGridSpacingWithWork_value _ _ hP, canonicalMulWithWork_value, inversePowerTwo_value,
    nat_value, queryGroupKeysWithWork_value, queryOnlineKeysWithWork_value,
    localOnlineSourceKeys, List.map_map, refinementInitialSupport]
  rfl

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryRepresentatives
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOrderedChildInputsWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Counted representative and child-coordinate lists for adaptive band
data gathers. All initial-table lookups are included in the work counter. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem queryWideInputsWithWork_value {nx ny : ℕ} (M : ℕ)
    (parent : TargetInterval nx) (P : ℕ) (hP : 0 < P)
    (representatives : List (ℕ × TargetInterval ny)) :
    (queryWideInputsWithWork M parent P representatives).1 = wideWarmupInputs parent P representatives := by
  simp only [queryWideInputsWithWork, queryEraseWithWork_value _ coordinateEqualWithWork_value,
    arithmeticFlatMapWithWork_value, arithmeticMapWithWork_value,
    wideChildGridWithWork_value _ _ _ _ _ hP, wideWarmupInputs]



end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryActionInputCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds for the final adaptive child gather.  The temporary list and
its sorting work depend on emitted actions, rather than the full table. -/

namespace EditApproximation

theorem queryActionInputsWithWork_bounds {Parent Child : Type*} {M : ℕ}
    (actions : List (BinaryBellmanAction Parent Child M)) :
    (queryActionInputsWithWork actions).1.length = actions.length * M ∧
    (queryActionInputsWithWork actions).2 ≤ actions.length * (5 * M + 3) + M + 1 := by
  let run := fun action : BinaryBellmanAction Parent Child M =>
    arithmeticMapWithWork (fun i : Fin M => (action.childState i, 1)) (List.finRange M)
  have hlen (action : BinaryBellmanAction Parent Child M) : (run action).1.length = M := by
    simp only [run, arithmeticMapWithWork_value, List.length_map, List.length_finRange]
  have hc (action : BinaryBellmanAction Parent Child M) : (run action).2 ≤ 4 * M := by
    have h := arithmeticMapWithWork_cost (fun i : Fin M => (action.childState i, 1))
      (List.finRange M) 1 (fun _ _ => le_rfl)
    simpa only [List.length_finRange, Nat.reduceAdd, Nat.mul_comm] using h
  constructor
  · simp only [queryActionInputsWithWork, arithmeticFlatMapWithWork_value, List.length_flatMap,
      arithmeticMapWithWork_value, List.length_map, List.length_finRange, List.map_const',
      List.sum_replicate, smul_eq_mul]
  · have h := arithmeticFlatMapWithWork_cost run actions (4 * M) M
      (fun action _ => hc action) (fun action _ => (hlen action).le)
    change (arithmeticFlatMapWithWork run actions).2 + M + 1 ≤ _
    have heq : 4 * M + M + 3 = 5 * M + 3 := by omega
    rw [heq] at h
    omega

theorem queryOrderedChildInputsWithWork_length {M n : ℕ} (inputs : List (Fin M × TargetInterval n)) :
    (queryOrderedChildInputsWithWork inputs).1.length ≤ inputs.length := by
  rw [queryOrderedChildInputsWithWork_value, orderedInputs_length]
  exact List.toFinset_card_le inputs

theorem queryNeededInputsWithWork_bounds {n M : ℕ}
    (selected online : List (BinaryBellmanAction (TargetInterval n) (Fin M × TargetInterval n) M))
    (B : ℕ) (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    (queryNeededInputsWithWork selected online).1.length ≤ (selected.length + online.length) * M ∧
    (queryNeededInputsWithWork selected online).2 ≤
      queryNeededInputsBitBudget (selected.length + online.length) M B := by
  let first := queryActionInputsWithWork selected
  let second := queryActionInputsWithWork online
  have hf := queryActionInputsWithWork_bounds selected
  have hs := queryActionInputsWithWork_bounds online
  have hl : (first.1 ++ second.1).length = (selected.length + online.length) * M := by
    rw [List.length_append, hf.1, hs.1, Nat.add_mul]
  have hsort := queryOrderedChildInputsWithWork_cost (first.1 ++ second.1) B hM hn
  rw [hl] at hsort
  constructor
  · exact (queryOrderedChildInputsWithWork_length (first.1 ++ second.1)).trans_eq hl
  · change first.2 + second.2 + first.1.length +
      (queryOrderedChildInputsWithWork (first.1 ++ second.1)).2 + 2 ≤ _
    have hfc : first.2 ≤ selected.length * (5 * M + 3) + M + 1 := hf.2
    have hsc : second.2 ≤ online.length * (5 * M + 3) + M + 1 := hs.2
    unfold queryNeededInputsBitBudget
    rw [Nat.add_mul]
    have hfl : first.1.length ≤ (selected.length + online.length) * M := by
      rw [hf.1, Nat.add_mul]
      omega
    omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryDataBuffers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Counted local data buffers for the adaptive gathers. Bounds depend on
stored keys and the requested key, not on an unbounded ambient key type. -/

namespace EditApproximation
namespace BinaryFraction

theorem gatheredWordLookupWithWork_cost_on {κ : Type*}
    (equal : κ → κ → Bool × ℕ) (C : ℕ) (keys : List κ)
    (values : List BinaryFraction) (query : κ)
    (hC : ∀ key ∈ keys, (equal query key).2 ≤ C) :
    (gatheredWordLookupWithWork equal keys values query).2 ≤
      1 + keys.length * (C + 1) := by
  induction keys generalizing values with
  | nil => simp only [gatheredWordLookupWithWork, List.length_nil, Nat.zero_mul, Nat.add_zero, le_rfl]
  | cons key keys ih =>
    have hc := hC key List.mem_cons_self
    have ht := ih (values.drop 1) (fun k hk => hC k (List.mem_cons_of_mem _ hk))
    cases values with
    | nil => simp only [gatheredWordLookupWithWork]; omega
    | cons value values =>
      simp only [List.drop_succ_cons, List.drop_zero] at ht
      simp only [gatheredWordLookupWithWork]
      split_ifs <;> simp only [List.length_cons, Nat.add_mul, Nat.one_mul] <;> omega



theorem queryHistoryReadWithWork_cost {M n : ℕ}
    (keys : List (Fin M × ℕ × TargetInterval n)) (values : List BinaryFraction)
    (s : ℕ) (input : Fin M × TargetInterval n) (B : ℕ)
    (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) (hs : Nat.size s ≤ B)
    (ht : ∀ key ∈ keys, Nat.size key.2.1 ≤ B) :
    (queryHistoryReadWithWork keys values s input).2 ≤
      1 + keys.length * (32 * B + 12) := by
  apply gatheredWordLookupWithWork_cost_on queryHistoryEqualWithWork (32 * B + 11)
  intro key hk
  have hc := coordinateEqualWithWork_cost input (key.1, key.2.2) B hM hn
  have he := naturalEqualWithWork_cost s key.2.1 B hs (ht key hk)
  change (coordinateEqualWithWork input (key.1, key.2.2)).2 +
    (naturalEqualWithWork s key.2.1).2 + 1 ≤ _
  omega

theorem queryHistoryReadWithWork_width {M n : ℕ}
    (keys : List (Fin M × ℕ × TargetInterval n)) (values : List BinaryFraction)
    (s : ℕ) (input : Fin M × TargetInterval n) (B : ℕ)
    (hB : 2 ≤ B) (hv : ∀ v ∈ values, v.width ≤ B) :
    (queryHistoryReadWithWork keys values s input).1.width ≤ B :=
  gatheredWordLookupWithWork_width _ keys values _ B hB hv

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySelectorGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction
section Selectors
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)

theorem queryGroupSelectWithWork_geometry (draw : CountedCellGroupDraws M F Q)
    (keys : List (Fin M × TargetInterval target.length)) (words : List BinaryFraction)
    (q : TargetInterval target.length) (B : ℕ) (hN : Nat.size N ≤ B)
    (hn : Nat.size target.length + 2 ≤ B) (hw : 0 ≤ (parentInitial q).1.value) :
    let selected := queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF
      tau a parentInitial child initial R hc hi draw keys words q
    selected.1.length ≤ (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 ∧
    ∀ action ∈ selected.1, action.connection.width ≤ connectionWordBudget M B := by
  have hv := preparedLocalCellGroupsSourceWithWork_semantic_value source target parent P F exponent Q
    eM eF hM hF hP tau a parentInitial child initial (queryChildReadWithWork keys words) R hc hi N draw q
  have hl := preparedLocalCellGroupsWithWork_length_le source target parent N P F exponent Q eM eF B
    hM hF hP tau a (fun r => (parentInitial r).1) (fun i r => (child i r).1)
    (fun i r => (initial i r).1) (fun i r => (queryChildReadWithWork keys words i r).1)
    (fun b cell scale sample => (draw b cell scale sample).1) q hN hw
  have hc' := preparedLocalCellGroupsWithWork_connection source target parent N P F exponent Q eM eF
    hM hF hP tau a (fun r => (parentInitial r).1) (fun i r => (child i r).1)
    (fun i r => (initial i r).1) (fun i r => (queryChildReadWithWork keys words i r).1)
    (fun b cell scale sample => (draw b cell scale sample).1) q B hn
  simpa only [queryGroupSelectWithWork, hv] using And.intro hl hc'

theorem queryOnlineSelectWithWork_geometry (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
    (keys : List (Fin M × ℕ × TargetInterval target.length)) (words : List BinaryFraction)
    (q : TargetInterval target.length) (B : ℕ) (hN : Nat.size N ≤ B) :
    let selected := queryOnlineSelectWithWork source target parent N P F exponent H hP tau a eta kappa
      parentInitial child initial R hc hi t integer keys words q
    selected.1.length ≤ B + 1 ∧ ∀ action ∈ selected.1, action.connection = zero := by
  have hv := preparedLocalOnlineActionsSourceWithWork_semantic_value source target parent P F exponent H
    hP tau a eta kappa parentInitial child initial (queryHistoryReadWithWork keys words) R hc hi
    (t - 1) integer N q
  have hl := preparedLocalOnlineActionsWithWork_length_le source target parent N P F exponent H B hP
    tau a eta kappa (fun r => (parentInitial r).1) (fun i r => (child i r).1)
    (fun i r => (initial i r).1) (fun s input => (queryHistoryReadWithWork keys words s input).1)
    (t - 1) (fun b r => (integer b r).1) q hN
  have hc' := preparedLocalOnlineActionsWithWork_connection source target parent N P F exponent H hP
    tau a eta kappa (fun r => (parentInitial r).1) (fun i r => (child i r).1)
    (fun i r => (initial i r).1) (fun s input => (queryHistoryReadWithWork keys words s input).1)
    (t - 1) (fun b r => (integer b r).1) q
  simpa only [queryOnlineSelectWithWork, hv] using And.intro hl hc'

end Selectors
end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalFinishCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The executed refinement tail, with its actual selected actions and
its final deduplicated current-input buffer. -/

namespace EditApproximation.BinaryFraction

section Finish
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (draw : CountedCellGroupDraws M F Q)
  (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
  (earlierKeys : List (Fin M × ℕ × TargetInterval target.length)) (earlierWords : List BinaryFraction)
  (sharedKeys : List (Fin M × TargetInterval target.length)) (sharedWords currentWords : List BinaryFraction)
  (q : TargetInterval target.length)

theorem queryLocalRefinement_finish_bounds_oai (B Rp earlierCount : ℕ)
    (hB : 10 ≤ B) (hN : Nat.size N ≤ B) (hnx : Nat.size source.length ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hMb : Nat.size M ≤ B) (hPb : Nat.size P ≤ B)
    (hFb : Nat.size F + 2 ≤ B) (ht : Nat.size t ≤ B) (ha : a.width ≤ B) (hd : delta.width ≤ B)
    (hpw : ∀ r, (parentInitial r).1.width ≤ B) (hpr : ∀ r, (parentInitial r).2 ≤ Rp)
    (hpn : 0 ≤ (parentInitial q).1.value)
    (hew : ∀ w ∈ earlierWords, w.width ≤ B) (hcw : ∀ w ∈ currentWords, w.width ≤ B)
    (het : ∀ key ∈ earlierKeys, Nat.size key.2.1 ≤ B) (hel : earlierKeys.length ≤ earlierCount) :
    let groups := (queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF
      tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q).1
    let online := (queryOnlineSelectWithWork source target parent N P F exponent H hP tau a eta kappa
      parentInitial child initial R hc hi t integer earlierKeys earlierWords q).1
    let keys := (queryNeededInputsWithWork groups online).1
    let G := (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
    let lookup := queryFinishReadBudget M B Rp earlierCount G (B + 1)
    (queryRefinementFinishWithWork parent N P F a delta parentInitial t earlierKeys earlierWords
      groups online keys currentWords q).1.width ≤ preparedKernelWordBudget M B ∧
    (queryRefinementFinishWithWork parent N P F a delta parentInitial t earlierKeys earlierWords
      groups online keys currentWords q).2 ≤ queryRefinementFinishBitBudget M P F B lookup G (B + 1) := by
  let groups := (queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF
    tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q).1
  let online := (queryOnlineSelectWithWork source target parent N P F exponent H hP tau a eta kappa
    parentInitial child initial R hc hi t integer earlierKeys earlierWords q).1
  let keys := (queryNeededInputsWithWork groups online).1
  let G := (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  let lookup := queryFinishReadBudget M B Rp earlierCount G (B + 1)
  have hg := queryGroupSelectWithWork_geometry source target parent N P F exponent Q eM eF hP hM hF
    tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q B hN hny hpn
  have hgc := (queryGroupSelectWithWork_geometry source target parent N P F exponent Q eM eF hP hM hF
    tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q (B + 4)
    (by omega) (by omega) hpn).2
  have ho := queryOnlineSelectWithWork_geometry source target parent N P F exponent H hP tau a eta kappa
    parentInitial child initial R hc hi t integer earlierKeys earlierWords q B hN
  have hk := (queryNeededInputsWithWork_bounds groups online B hMb (by omega)).1
  have hkl : keys.length ≤ (G + (B + 1)) * M := by
    exact hk.trans (Nat.mul_le_mul_right M (Nat.add_le_add hg.1 ho.1))
  apply queryRefinementFinishWithWork_bounds parent N P F B lookup G (B + 1) a delta parentInitial t
    earlierKeys earlierWords groups online keys currentWords q hB hP
    (by rw [hF]; exact Nat.one_le_two_pow) hN hnx hny hMb hPb hFb ha hd hpw
  · intro r
    have hr := hpr r
    dsimp only [lookup, queryFinishReadBudget]
    omega
  · intro input
    exact queryHistoryReadWithWork_width earlierKeys earlierWords (t - 1) input B (by omega) hew
  · intro input
    have hr := queryHistoryReadWithWork_cost earlierKeys earlierWords (t - 1) input B hMb (by omega)
      ((Nat.size_le_size (Nat.sub_le t 1)).trans ht) het
    have hm := Nat.mul_le_mul_right (32 * B + 12) hel
    dsimp only [lookup, queryFinishReadBudget]
    omega
  · intro i r
    exact gatheredWordLookupWithWork_width _ keys currentWords (i, r) B (by omega) hcw
  · intro i r
    have hr := queryChildReadWithWork_cost keys currentWords i r B hMb (by omega)
    have hm := Nat.mul_le_mul_right (24 * B + 9) hkl
    dsimp only [lookup, queryFinishReadBudget]
    omega
  · exact hgc
  · intro action haction
    rw [ho.2 action haction]
    change 1 ≤ connectionWordBudget M (B + 4)
    unfold connectionWordBudget bandMassTotalStorageBudget
    omega
  · exact hg.1
  · exact ho.1

end Finish
end EditApproximation.BinaryFraction

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.BinaryFraction.queryLocalRefinement_finish_bounds_oai.{u_1} := @OAI.EditApproximation.BinaryFraction.queryLocalRefinement_finish_bounds_oai.{u_1}
