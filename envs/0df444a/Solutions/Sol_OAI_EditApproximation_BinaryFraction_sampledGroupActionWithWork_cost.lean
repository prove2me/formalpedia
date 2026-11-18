-- Prove2me | solution 1 for OAI.EditApproximation.BinaryFraction.sampledGroupActionWithWork_cost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:30:44.163719+00:00
-- url     : https://prove2.me/submissions/d2ea39a6-5641-41ce-9be4-1fe12b1000f4

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_07
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_OAIQ361V3Ea000
import Definitions.Def_OAIQ361V3Ea001
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_unskippedEstimateWithWork_bounds

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryMaximizerWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counted stored-score maximization for Boolean fraction coordinates. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

theorem scoredArgmaxWithWork_score_width {α : Type*} (score : α → BinaryFraction × ℕ)
    (values : List α) (W : ℕ) (hw : ∀ a ∈ values, (score a).1.width ≤ W)
    (best : α × BinaryFraction) (hbest : (scoredArgmaxWithWork score values).1 = some best) :
    best.2.width ≤ W := by
  rw [scoredArgmaxWithWork_value] at hbest
  cases h : values.argmax (fun a => (score a).1.value) with
  | none => simp only [h, Option.map_none] at hbest; contradiction
  | some a =>
    have ha : a ∈ values := List.argmax_mem (by rw [h]; simp)
    simp only [h, Option.map_some, Option.some.injEq] at hbest
    rw [← hbest]
    exact hw a ha

theorem scoredArgmaxWithWork_cost {α : Type*} (score : α → BinaryFraction × ℕ)
    (values : List α) (C W : ℕ) (hc : ∀ a ∈ values, (score a).2 ≤ C)
    (hw : ∀ a ∈ values, (score a).1.width ≤ W) :
    (scoredArgmaxWithWork score values).2 ≤ values.length * (C + 1000 * (W + 1) ^ 2 + 2) := by
  induction values with
  | nil => simp [scoredArgmaxWithWork]
  | cons a rest ih =>
    have ht := ih (fun b hb => hc b (List.mem_cons_of_mem _ hb))
      (fun b hb => hw b (List.mem_cons_of_mem _ hb))
    have ha := hc a List.mem_cons_self
    have haw := hw a List.mem_cons_self
    cases hbest : (scoredArgmaxWithWork score rest).1 with
    | none =>
      simp only [scoredArgmaxWithWork, hbest, List.length_cons]
      nlinarith only [ht, ha]
    | some best =>
      have hbw := scoredArgmaxWithWork_score_width score rest W
        (fun b hb => hw b (List.mem_cons_of_mem _ hb)) best hbest
      have hcmp := ltWithWork_cost (score a).1 best.2 W haw hbw
      simp only [scoredArgmaxWithWork, hbest, List.length_cons]
      nlinarith only [ht, ha, hcmp]

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



theorem doubleFraction_width (a : BinaryFraction) : (doubleFraction a).width ≤ a.width + 1 := by
  unfold doubleFraction width
  simp only [List.length_cons]
  omega



theorem dyadicScanWithWork_width (a candidate : BinaryFraction) (n : ℕ) :
    (dyadicScanWithWork a candidate n).1.width ≤ candidate.width + n := by
  induction n generalizing candidate with
  | zero => simp [dyadicScanWithWork]
  | succ n ih =>
    unfold dyadicScanWithWork
    dsimp only
    split_ifs
    · exact (ih _).trans (by have h := doubleFraction_width candidate; omega)
    · change candidate.width ≤ candidate.width + (n + 1)
      omega

theorem dyadicScanWithWork_cost (a candidate : BinaryFraction) (n W : ℕ)
    (ha : a.width ≤ W) (hc : candidate.width + n ≤ W) :
    (dyadicScanWithWork a candidate n).2 ≤ 1 + n * (1000 * (W + 1) ^ 2 + 2) := by
  induction n generalizing candidate with
  | zero => simp [dyadicScanWithWork]
  | succ n ih =>
    have hcmp := ltWithWork_cost candidate a W (by omega) ha
    have hdouble := doubleFraction_width candidate
    have hnext := ih (doubleFraction candidate) (by omega)
    unfold dyadicScanWithWork
    dsimp only
    split_ifs
    · rw [Nat.add_mul, Nat.one_mul]
      omega
    · have hp : 1000 * (W + 1) ^ 2 + 2 ≤ (n + 1) * (1000 * (W + 1) ^ 2 + 2) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega

theorem dyadicCeilingWithWork_width (a : BinaryFraction) :
    (dyadicCeilingWithWork a).1.width ≤ 3 * a.width + 1 := by
  have h := dyadicScanWithWork_width a (inversePowerTwo a.width) (2 * a.width)
  rw [inversePowerTwo_width] at h
  exact h.trans (by omega)

theorem dyadicCeilingWithWork_cost (a : BinaryFraction) :
    (dyadicCeilingWithWork a).2 ≤
      1 + 2 * a.width * (1000 * (3 * a.width + 2) ^ 2 + 2) + 3 * a.width + 5 := by
  have h := dyadicScanWithWork_cost a (inversePowerTwo a.width) (2 * a.width) (3 * a.width + 1)
    (by omega) (by rw [inversePowerTwo_width]; omega)
  rw [show 3 * a.width + 1 + 1 = 3 * a.width + 2 by omega] at h
  exact Nat.add_le_add_right (Nat.add_le_add_right h (3 * a.width)) 5


theorem dyadicCeilingWithWork_cost_le (a : BinaryFraction) (B : ℕ) (hB : a.width ≤ B) :
    (dyadicCeilingWithWork a).2 ≤
      1 + 2 * B * (1000 * (3 * B + 2) ^ 2 + 2) + 3 * B + 5 := by
  have h := dyadicCeilingWithWork_cost a
  have hs := Nat.pow_le_pow_left (show 3 * a.width + 2 ≤ 3 * B + 2 by omega) 2
  have hp := Nat.mul_le_mul (show 2 * a.width ≤ 2 * B by omega)
    (show 1000 * (3 * a.width + 2) ^ 2 + 2 ≤ 1000 * (3 * B + 2) ^ 2 + 2 by omega)
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandEnvelope
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source
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



theorem maxWithWork_width (a b : BinaryFraction) :
    (maxWithWork a b).1.width ≤ max a.width b.width := by
  unfold maxWithWork
  dsimp only
  split_ifs
  · exact le_max_right _ _
  · exact le_max_left _ _

theorem maxWithWork_cost (a b : BinaryFraction) (B : ℕ) (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (maxWithWork a b).2 ≤ 1000 * (B + 1) ^ 2 + 1 :=
  Nat.add_le_add_right (ltWithWork_cost a b B ha hb) 1



theorem maximumWithWork_width (fallback : BinaryFraction) (values : List BinaryFraction)
    (B : ℕ) (hf : fallback.width ≤ B) (hvalues : ∀ a ∈ values, a.width ≤ B) :
    (maximumWithWork fallback values).1.width ≤ B := by
  induction values with
  | nil => exact hf
  | cons head rest ih =>
    exact (maxWithWork_width head (maximumWithWork fallback rest).1).trans
      (max_le (hvalues head List.mem_cons_self) (ih (fun a ha => hvalues a (List.mem_cons_of_mem _ ha))))

theorem maximumWithWork_cost (fallback : BinaryFraction) (values : List BinaryFraction)
    (B : ℕ) (hf : fallback.width ≤ B) (hvalues : ∀ a ∈ values, a.width ≤ B) :
    (maximumWithWork fallback values).2 ≤ 1 + values.length * (1000 * (B + 1) ^ 2 + 2) := by
  induction values with
  | nil => simp [maximumWithWork]
  | cons head rest ih =>
    have htail := ih (fun a ha => hvalues a (List.mem_cons_of_mem _ ha))
    have hw := maximumWithWork_width fallback rest B hf (fun a ha => hvalues a (List.mem_cons_of_mem _ ha))
    have hc := maxWithWork_cost head (maximumWithWork fallback rest).1 B
      (hvalues head List.mem_cons_self) hw
    change (maximumWithWork fallback rest).2 + (maxWithWork head (maximumWithWork fallback rest).1).2 + 1 ≤ _
    simp only [List.length_cons]
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem bandEnvelopeWithWork_width {M ny : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → BinaryFraction) (i : Fin M)
    (B : ℕ) (hbits : ∀ action ∈ band, (initial i (action i)).width ≤ B) :
    (bandEnvelopeWithWork b band initial i).1.width ≤ 3 * bandEnvelopeWordBudget b M B + 1 := by
  let W := bandEnvelopeWordBudget b M B
  have hfloor := divWithWork_self_width (nat b) (nat M)
  rw [divWithWork_representation, nat_representation, nat_representation] at hfloor
  have hf := UnreducedRational.storageBits_div (UnreducedRational.nat b) (UnreducedRational.nat M)
  simp only [UnreducedRational.storageBits_nat] at hf
  have hfW : (divWithWork (nat b) (nat M)).1.width ≤ W := by
    dsimp only [W, bandEnvelopeWordBudget]
    omega
  have hmW := maximumWithWork_width zero (band.map fun action => initial i (action i)) W
    (by change 1 ≤ W; dsimp only [W, bandEnvelopeWordBudget]; omega)
    (by intro a ha; obtain ⟨action, haction, rfl⟩ := List.mem_map.mp ha
        exact (hbits action haction).trans (by dsimp only [W, bandEnvelopeWordBudget]; omega))
  have hin := (maxWithWork_width (divWithWork (nat b) (nat M)).1
    (maximumWithWork zero (band.map fun action => initial i (action i))).1).trans (max_le hfW hmW)
  have h := dyadicCeilingWithWork_width (maxWithWork (divWithWork (nat b) (nat M)).1
    (maximumWithWork zero (band.map fun action => initial i (action i))).1).1
  change (dyadicCeilingWithWork _).1.width ≤ _
  omega


theorem bandEnvelopeWithWork_cost {M ny : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → BinaryFraction) (i : Fin M)
    (B : ℕ) (hbits : ∀ action ∈ band, (initial i (action i)).width ≤ B) :
    (bandEnvelopeWithWork b band initial i).2 ≤ bandEnvelopeBitBudget b M band.length B := by
  let W := bandEnvelopeWordBudget b M B
  let floor := (divWithWork (nat b) (nat M)).1
  let maximum := (maximumWithWork zero (band.map fun action => initial i (action i))).1
  let input := (maxWithWork floor maximum).1
  have hfloor := divWithWork_self_width (nat b) (nat M)
  rw [divWithWork_representation, nat_representation, nat_representation] at hfloor
  have hf := UnreducedRational.storageBits_div (UnreducedRational.nat b) (UnreducedRational.nat M)
  simp only [UnreducedRational.storageBits_nat] at hf
  have hfW : floor.width ≤ W := by
    dsimp only [W, bandEnvelopeWordBudget]
    change floor.width ≤ _ at hfloor
    omega
  have hmW : maximum.width ≤ W := maximumWithWork_width zero
    (band.map fun action => initial i (action i)) W
    (by change 1 ≤ W; dsimp only [W, bandEnvelopeWordBudget]; omega)
    (by intro a ha; obtain ⟨action, haction, rfl⟩ := List.mem_map.mp ha
        exact (hbits action haction).trans (by dsimp only [W, bandEnvelopeWordBudget]; omega))
  have hiW : input.width ≤ W := (maxWithWork_width floor maximum).trans (max_le hfW hmW)
  have hfc := divWithWork_cost (nat b) (nat M) (Nat.size b + Nat.size M + 4)
    ((nat_width_le b).trans (by omega)) ((nat_width_le M).trans (by omega))
  rw [show Nat.size b + Nat.size M + 4 + 2 = Nat.size b + Nat.size M + 6 by omega] at hfc
  have hmc := maximumWithWork_cost zero (band.map fun action => initial i (action i)) W
    (by change 1 ≤ W; dsimp only [W, bandEnvelopeWordBudget]; omega)
    (by intro a ha; obtain ⟨action, haction, rfl⟩ := List.mem_map.mp ha
        exact (hbits action haction).trans (by dsimp only [W, bandEnvelopeWordBudget]; omega))
  simp only [List.length_map] at hmc
  have hic := maxWithWork_cost floor maximum W hfW hmW
  have hdc := dyadicCeilingWithWork_cost_le input W hiW
  change (divWithWork (nat b) (nat M)).2 +
    (maximumWithWork zero (band.map fun action => initial i (action i))).2 +
    (maxWithWork floor maximum).2 + (dyadicCeilingWithWork input).2 + band.length + 4 ≤ _
  change _ ≤ 2100 * (Nat.size b + Nat.size M + 6) ^ 2 +
    (1 + band.length * (1000 * (W + 1) ^ 2 + 2)) + (1000 * (W + 1) ^ 2 + 1) +
    (1 + 2 * W * (1000 * (3 * W + 2) ^ 2 + 2) + 3 * W + 5) + band.length + 4
  omega

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

theorem selectGroupWithWork_cost {ι : Type*} (members : List ι) (hne : members ≠ [])
    (estimate : ι → BinaryFraction × ℕ) (C W : ℕ)
    (hc : ∀ member ∈ members, (estimate member).2 ≤ C)
    (hw : ∀ member ∈ members, (estimate member).1.width ≤ W) :
    (selectGroupWithWork members hne estimate).2 ≤
      members.length * (C + 1000 * (W + 1) ^ 2 + 3) + 1 := by
  have h := scoredArgmaxWithWork_cost (fun member => ((estimate member).1.neg, (estimate member).2 + 1))
    members (C + 1) W (by intro member hm; have := hc member hm; omega)
    (by intro member hm; simpa only [neg_width] using hw member hm)
  change _ + 1 ≤ _
  have heq : (C + 1) + 1000 * (W + 1) ^ 2 + 2 = C + 1000 * (W + 1) ^ 2 + 3 := by omega
  rw [heq] at h
  exact Nat.add_le_add_right h 1

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

namespace BinaryFraction

theorem roundedSpacingWithWork_bounds (theta envelope : BinaryFraction) (B : ℕ)
    (ht : theta.width ≤ B) (he : envelope.width ≤ B) :
    (roundedSpacingWithWork theta envelope).1.length ≤ roundedSpacingWordBudget B ∧
      (roundedSpacingWithWork theta envelope).2 ≤ roundedSpacingBitBudget B := by
  have hp := canonicalMulWithWork_width theta envelope B ht he
  have hpc := canonicalMulWithWork_cost theta envelope B ht he
  have hm := (maxWithWork_width one (canonicalMulWithWork theta envelope).1).trans
    (show max one.width (canonicalMulWithWork theta envelope).1.width ≤ 4 * B + 2 by
      change max 1 _ ≤ _
      omega)
  have hmc := maxWithWork_cost one (canonicalMulWithWork theta envelope).1 (4 * B + 2)
    (by change 1 ≤ _; omega) hp
  have hc := naturalCeilingWithWork_length (maxWithWork one (canonicalMulWithWork theta envelope).1).1
  have hcc := naturalCeilingWithWork_cost (maxWithWork one (canonicalMulWithWork theta envelope).1).1
  have hsquare := Nat.pow_le_pow_left (show
    (maxWithWork one (canonicalMulWithWork theta envelope).1).1.width + 1 ≤ 4 * B + 3 by omega) 2
  constructor
  · change (naturalCeilingWithWork (maxWithWork one (canonicalMulWithWork theta envelope).1).1).1.length ≤ _
    unfold roundedSpacingWordBudget
    omega
  · change (canonicalMulWithWork theta envelope).2 +
      (maxWithWork one (canonicalMulWithWork theta envelope).1).2 +
      (naturalCeilingWithWork (maxWithWork one (canonicalMulWithWork theta envelope).1).1).2 + 2 ≤ _
    unfold roundedSpacingBitBudget
    nlinarith only [hpc, hmc, hcc, hsquare]

theorem roundedBandWithWork_cost {ny M : ℕ} (thetaExponent b : ℕ)
    (band : List (Fin M → TargetInterval ny)) (hne : band ≠ [])
    (initial : Fin M → TargetInterval ny → BinaryFraction) (B : ℕ)
    (hny : Nat.size ny ≤ B)
    (hi : ∀ action ∈ band, ∀ i, (initial i (action i)).width ≤ B) :
    (roundedBandWithWork thetaExponent b band hne initial).2 ≤
      roundedBandBitBudget thetaExponent b M band.length B := by
  let W := roundedBandInputBudget thetaExponent b M B
  have hW : B ≤ W := by dsimp only [W, roundedBandInputBudget]; omega
  have ht : (inversePowerTwo thetaExponent).width ≤ W := by
    rw [inversePowerTwo_width]
    dsimp only [W, roundedBandInputBudget]
    omega
  have hcell (i : Fin M) :
      (let envelope := bandEnvelopeWithWork b band initial i
       let spacing := roundedSpacingWithWork (inversePowerTwo thetaExponent) envelope.1
       let rounded := roundStateWithWork (bitWordValue spacing.1)
         (roundedSpacingWithWork_pos _ _) (band.head hne i)
       (rounded.1, envelope.2 + spacing.2 + rounded.2 + thetaExponent + 3)).2 ≤
      bandEnvelopeBitBudget b M band.length B + roundedSpacingBitBudget W +
        500 * (roundedSpacingWordBudget W + B + 1) ^ 2 + thetaExponent + 5 := by
    let envelope := bandEnvelopeWithWork b band initial i
    let spacing := roundedSpacingWithWork (inversePowerTwo thetaExponent) envelope.1
    have hew := bandEnvelopeWithWork_width b band initial i B (fun a ha => hi a ha i)
    have hec := bandEnvelopeWithWork_cost b band initial i B (fun a ha => hi a ha i)
    have heW : envelope.1.width ≤ W := hew.trans (by
      dsimp only [W, roundedBandInputBudget]; omega)
    have hs := roundedSpacingWithWork_bounds (inversePowerTwo thetaExponent) envelope.1 W ht heW
    have hss : Nat.size (bitWordValue spacing.1) ≤ roundedSpacingWordBudget W :=
      (Nat.size_le.mpr (bitWordValue_lt_pow_length spacing.1)).trans hs.1
    have hr := roundStateWithWork_cost (bitWordValue spacing.1)
      (roundedSpacingWithWork_pos _ _) (band.head hne i) (roundedSpacingWordBudget W + B)
      (by omega) (hny.trans (by omega))
    change envelope.2 + spacing.2 + (roundStateWithWork (bitWordValue spacing.1)
      (roundedSpacingWithWork_pos (inversePowerTwo thetaExponent) envelope.1)
      (band.head hne i)).2 + thetaExponent + 3 ≤ _
    change envelope.2 ≤ _ at hec
    have hsc : spacing.2 ≤ roundedSpacingBitBudget W := hs.2
    omega
  have hmap := vectorMapWithWork_cost_le M _ _ hcell
  change (vectorMapWithWork M _).2 ≤ _
  unfold roundedBandBitBudget
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hmap

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySelectedGroupWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete group selection cost, including every sampled member estimate
and reconstruction of the selected rounded action. -/

namespace EditApproximation
namespace BinaryFraction

private theorem roundedBandBitBudget_mono_vertices (e b M v w B : ℕ) (h : v ≤ w) :
    roundedBandBitBudget e b M v B ≤ roundedBandBitBudget e b M w B := by
  unfold roundedBandBitBudget bandEnvelopeBitBudget
  dsimp only
  gcongr

private theorem sampledMemberBitBudget_mono_vertices (M T e b v w B : ℕ) (h : v ≤ w) :
    sampledMemberBitBudget M T e b v B ≤ sampledMemberBitBudget M T e b w B := by
  have hr := roundedBandBitBudget_mono_vertices e b M v w B h
  unfold sampledMemberBitBudget bandEnvelopeBitBudget
  dsimp only
  gcongr

theorem sampledGroupActionWithWork_cost_oai {α : Type*} (source target : List α) {M T : ℕ}
    (parent : TargetInterval source.length) (b P exponent Q : ℕ) (tau F : BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (scales : Fin T → BinaryFraction)
    (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)
    (members : List (UnskippedBand source target parent b P exponent tau.value F.value
      (fun i q => (child i q).value) (fun i q => (initial i q).value))) (hne : members ≠ [])
    (V B : ℕ) (hM : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B)
    (hb : Nat.size b + 2 ≤ B) (hny : Nat.size target.length + 2 ≤ B)
    (hs : ∀ t, (scales t).width ≤ B)
    (hV : ∀ member ∈ members, member.actions.length ≤ V)
    (hi : ∀ member ∈ members, ∀ action ∈ member.actions, ∀ i, (initial i (action i)).width ≤ B)
    (hv : ∀ i q, (current i q).width ≤ B) :
    (sampledGroupActionWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).2 ≤ selectedGroupBitBudget M T exponent b members.length V B := by
  let estimate := unskippedEstimateWithWork source target parent b P exponent Q tau F
    child initial current scales draw
  have he (member) (hm : member ∈ members) := unskippedEstimateWithWork_bounds source target parent b P exponent Q
    tau F child initial current scales draw member B hM hQ hb hny hs (hi member hm) hv
  have hselection := selectGroupWithWork_cost members hne estimate
    (sampledMemberBitBudget M T exponent b V B) (sampledMemberWordBudget M T b B)
    (fun member hm => (he member hm).2.trans (sampledMemberBitBudget_mono_vertices _ _ _ _ _ _ _ (hV member hm)))
    (fun member hm => (he member hm).1)
  let selected := (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F
    child initial current scales draw members hne).1
  have hselected : selected ∈ members := by
    rw [show selected = selectGroupMember members hne (fun member => (estimate member).1.value) from
      selectGroupWithWork_value members hne estimate]
    exact (selectGroupMember_spec members hne _).1
  have hrounded := (roundedBandWithWork_cost exponent b selected.actions selected.nonempty initial B
    (by omega) (hi selected hselected)).trans
      (roundedBandBitBudget_mono_vertices _ _ _ _ _ _ (hV selected hselected))
  let states := (roundedBandWithWork exponent b selected.actions selected.nonempty initial).1.get
  have hcenterlo : Nat.size selected.center.lo + 2 ≤ B :=
    (Nat.add_le_add_right (Nat.size_le_size (selected.center.ordered.trans selected.center.valid)) 2).trans hny
  have hcenterhi : Nat.size selected.center.hi + 2 ≤ B :=
    (Nat.add_le_add_right (Nat.size_le_size selected.center.valid) 2).trans hny
  have hstates : ∀ s ∈ List.ofFn states, Nat.size s.lo + 2 ≤ B ∧ Nat.size s.hi + 2 ≤ B := by
    intro s _
    exact ⟨(Nat.add_le_add_right (Nat.size_le_size (s.ordered.trans s.valid)) 2).trans hny,
      (Nat.add_le_add_right (Nat.size_le_size s.valid) 2).trans hny⟩
  have hconnection := connectionWithWork_cost (nat selected.center.lo) (nat selected.center.hi)
    (List.ofFn states) B ((nat_width_le _).trans hcenterlo)
      ((nat_width_le _).trans hcenterhi) hstates
  simp only [List.length_ofFn] at hconnection
  have haction : (endpointActionWithWork selected.center states).2 ≤
      connectionBitBudget M B + 2 * B + 2 * M + 3 := by
    change (connectionWithWork (nat selected.center.lo) (nat selected.center.hi) (List.ofFn states)).2 +
      Nat.size selected.center.lo + Nat.size selected.center.hi + M + 2 + M + 1 ≤ _
    omega
  change (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child initial current
    scales draw members hne).2 +
    (roundedBandWithWork exponent b selected.actions selected.nonempty initial).2 +
    (endpointActionWithWork selected.center states).2 + 3 ≤ _
  change (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child initial current
    scales draw members hne).2 ≤ _ at hselection
  unfold selectedGroupBitBudget
  omega

end BinaryFraction
end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.BinaryFraction.sampledGroupActionWithWork_cost_oai.{u_1} := @OAI.EditApproximation.BinaryFraction.sampledGroupActionWithWork_cost_oai.{u_1}
