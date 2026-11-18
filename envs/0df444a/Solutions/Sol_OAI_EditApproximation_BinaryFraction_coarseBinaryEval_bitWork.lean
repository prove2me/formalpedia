-- Prove2me | solution 1 for OAI.EditApproximation.BinaryFraction.coarseBinaryEval_bitWork
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:25:42.180252+00:00
-- url     : https://prove2.me/submissions/976ee136-4a6c-405d-95ce-87d4524922a0

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
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_coarseBinaryChildren_bounds

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





theorem canonicalizeWithWork_width_le_storageBits (a : BinaryFraction) :
    (canonicalizeWithWork a).1.width ≤ a.representation.storageBits := by
  rw [canonicalizeWithWork_width]
  unfold UnreducedRational.storageBits
  exact max_le (by omega) (by omega)

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

end UnreducedRational
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




end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryFixedDenominator
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
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

theorem raw_den_dvd_scaled_num (a : BinaryFraction) (D : ℕ) (hD : a.value.den ∣ D) :
    bitWordValue a.denominator ∣ bitWordValue a.numerator.bits * D := by
  have hd : (a.representation.den : ℤ) ≠ 0 := by exact_mod_cast a.representation.den_pos.ne'
  obtain ⟨c, hn, hd'⟩ := Rat.num_den_mk (q := a.value) (n := a.representation.num)
    (d := (a.representation.den : ℤ)) hd (by
      rw [Rat.divInt_eq_div, Int.cast_natCast]
      exact (representation_value a).symm)
  obtain ⟨k, hk⟩ := hD
  have hi : (a.representation.den : ℤ) ∣ a.representation.num * (D : ℤ) := by
    refine ⟨a.value.num * k, ?_⟩
    rw [hn, hd', hk, Nat.cast_mul]
    ring
  have habs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hi)
  have hnum : a.representation.num.natAbs = bitWordValue a.numerator.bits := by
    cases h : a.numerator.negative <;> simp [representation, SignedBinary.value, signedMagnitude, h]
  change bitWordValue a.denominator ∣ (a.representation.num * (D : ℤ)).natAbs at habs
  simpa only [Int.natAbs_mul, Int.natAbs_natCast, hnum] using habs



theorem fixedDenominatorWithWork_value (a : BinaryFraction) (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) (hD : a.value.den ∣ bitWordValue denominator) :
    (fixedDenominatorWithWork a denominator hden).1.value = a.value := by
  let product := bitMulWithWork a.numerator.bits denominator
  let quotient := bitDivModWithWork a.denominator product.1
  have hdvd := raw_den_dvd_scaled_num a (bitWordValue denominator) hD
  have h := bitDivModWithWork_value a.denominator product.1 a.denominator_pos
  have hm : bitWordValue product.1 = bitWordValue a.numerator.bits * bitWordValue denominator :=
    bitMulWithWork_value _ _
  have hmod : bitWordValue quotient.2.1 = 0 := by
    have hz : bitWordValue product.1 % bitWordValue a.denominator = 0 := by
      rw [hm]
      exact Nat.mod_eq_zero_of_dvd hdvd
    rw [h.1, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add] at hz
    simp only [Nat.mod_mod] at hz
    exact (Nat.mod_eq_of_lt h.2).symm.trans hz
  have hq : bitWordValue a.denominator * bitWordValue quotient.1 =
      bitWordValue a.numerator.bits * bitWordValue denominator := by
    have heq := h.1
    change bitWordValue product.1 = bitWordValue a.denominator * bitWordValue quotient.1 + bitWordValue quotient.2.1 at heq
    rw [hmod, Nat.add_zero] at heq
    exact heq.symm.trans hm
  let raw : BinaryFraction := ⟨⟨a.numerator.negative, quotient.1⟩, denominator, hden⟩
  have hc : (canonicalizeWithWork raw).1.value = raw.value := by
    rw [← representation_value, canonicalizeWithWork_representation, representation_value]
  change (canonicalizeWithWork raw).1.value = a.value
  rw [hc]
  have hdQ : (bitWordValue a.denominator : ℚ) ≠ 0 := by exact_mod_cast a.denominator_pos.ne'
  have hDQ : (bitWordValue denominator : ℚ) ≠ 0 := by exact_mod_cast hden.ne'
  have hqQ : (bitWordValue a.denominator : ℚ) * bitWordValue quotient.1 =
      (bitWordValue a.numerator.bits : ℚ) * bitWordValue denominator := by exact_mod_cast hq
  cases hs : a.numerator.negative <;>
    simp only [raw, value, SignedBinary.value, signedMagnitude, hs, Bool.false_eq_true,
      ↓reduceIte, Int.cast_natCast, Int.cast_neg] <;>
    apply (div_eq_div_iff hDQ hdQ).mpr <;> nlinarith only [hqQ]

theorem fixedDenominatorWithWork_den (a : BinaryFraction) (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) :
    (fixedDenominatorWithWork a denominator hden).1.representation.den = bitWordValue denominator := by
  unfold fixedDenominatorWithWork
  dsimp only
  rw [canonicalizeWithWork_representation]
  rfl

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseEstimator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The concrete pruned coarse estimator

The random labels are a finite complete tree of integers in `1,...,B`.
Every execution below uses rational arithmetic and literal finite minima;
pruned arrays are represented by the zero function. Accuracy events are
kept separate from this executable definition.
-/

namespace EditApproximation

open Finset

universe u

/- All threshold labels, including labels below nodes which may be pruned. -/


/-- Section 3's pruned rational recurrence. All labels are supplied
beforehand; execution exposes a label only when its parent is expanded. -/


theorem coarseChildThreshold_nonneg {B : ℕ} {Q allowance : ℚ} (draw : Fin B)
    (hQ : 0 ≤ Q) (ha : 0 ≤ allowance) : 0 ≤ coarseChildThreshold B Q allowance draw := by
  unfold coarseChildThreshold
  positivity

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarsePrecision
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
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

theorem coarse_rat_mul_nat_den_dvd (x : ℚ) (n common : ℕ)
    (hx : x.den ∣ common) : (x * n).den ∣ common := by
  have h := Rat.mul_den_dvd x (n : ℚ)
  simp only [Rat.den_natCast, mul_one] at h
  exact h.trans hx

theorem coarse_rat_div_nat_den_dvd (x : ℚ) (n common : ℕ)
    (hn : 0 < n) (hx : x.den ∣ common) : (x / n).den ∣ common * n := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [div_eq_mul_inv]
  have h := Rat.mul_den_dvd x ((n : ℚ)⁻¹)
  simp only [Rat.den_inv_of_ne_zero hnq, Rat.num_natCast, Int.natAbs_natCast] at h
  exact h.trans (Nat.mul_dvd_mul hx (dvd_refl n))

theorem coarseChildThreshold_le_scale {B : ℕ} (draw : Fin B)
    (Q allowance : ℚ) (hQ : 0 < Q) (ha : 0 ≤ allowance) :
    coarseChildThreshold B Q allowance draw ≤ allowance / Q := by
  have hB : (0 : ℚ) < B := by exact_mod_cast Nat.zero_lt_of_lt draw.isLt
  have hlabel : (draw.val + 1 : ℕ) ≤ B := by omega
  have hlabelQ : ((draw.val + 1 : ℕ) : ℚ) ≤ B := by exact_mod_cast hlabel
  unfold coarseChildThreshold
  apply (div_le_iff₀ (mul_pos hB hQ)).2
  calc
    _ ≤ allowance * B := mul_le_mul_of_nonneg_left hlabelQ ha
    _ = _ := by field_simp

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

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseThresholdArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Boolean threshold arithmetic on the fixed denominator of one coarse
execution. Quotients use actual long division when compressed to that grid. -/

namespace EditApproximation
namespace BinaryFraction



 theorem coarseDivideWithWork_value (a divisor : BinaryFraction)
    (hden : (a.value / divisor.value).den ∣ bitWordValue a.denominator) :
    (coarseDivideWithWork a divisor).1.value = a.value / divisor.value := by
  unfold coarseDivideWithWork
  dsimp only
  rw [fixedDenominatorWithWork_value, divWithWork_value]
  simpa only [divWithWork_value] using hden

 theorem coarseDivideWithWork_den (a divisor : BinaryFraction) :
    (coarseDivideWithWork a divisor).1.representation.den = a.representation.den := by
  exact fixedDenominatorWithWork_den _ _ _

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

 theorem coarseCompact_divide (a b : BinaryFraction) :
    CoarseCompact (coarseDivideWithWork a b).1 := by
  unfold coarseDivideWithWork fixedDenominatorWithWork
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

 theorem coarseGridCell_mono (two a : BinaryFraction) (V W D A : ℕ)
    (h : CoarseGridCell two a V D A) (hle : V ≤ W) : CoarseGridCell two a W D A := by
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1.trans (by exact_mod_cast hle), h.2.2.2.2⟩

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

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseGridInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

/-- One descended allowance acquires only one factor of the fixed root
base in its denominator. This includes the literal sampled child label. -/
 theorem coarseChildAllowance_grid (B q L j : ℕ) (allowance : ℚ) (draw : Fin B)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (ha : allowance.den ∣ (L * B * q) ^ j) :
    ((1 / (L : ℚ)) * coarseChildThreshold B q allowance draw).den ∣
      (L * B * q) ^ (j + 1) := by
  have ht : (coarseChildThreshold B q allowance draw).den ∣
      (L * B * q) ^ j * (B * q) := by
    simpa only [coarseChildThreshold, Nat.cast_mul] using
      coarse_rat_div_nat_den_dvd (allowance * ((draw.val + 1 : ℕ) : ℚ)) (B * q) ((L * B * q) ^ j)
        (Nat.mul_pos hB hq) (coarse_rat_mul_nat_den_dvd allowance (draw.val + 1) _ ha)
  have heq : (1 / (L : ℚ)) * coarseChildThreshold B q allowance draw =
      coarseChildThreshold B q allowance draw / L := by ring
  rw [heq]
  convert coarse_rat_div_nat_den_dvd _ L _ hL ht using 1
  all_goals try with_reducible_and_instances rfl
  rw [pow_succ]
  ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseGridTransfers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

 theorem coarseScale_root_grid (B q L j d : ℕ) (allowance : ℚ) (hq : 0 < q)
    (ha : allowance.den ∣ (L * B * q) ^ j) :
    (allowance / q).den ∣ coarseCommonDenominator 1 q L B (j + d) := by
  apply (coarse_rat_div_nat_den_dvd allowance q _ hq ha).trans
  refine ⟨(L * B * q) ^ d, ?_⟩
  simp only [coarseCommonDenominator, one_mul, pow_add]
  ring

 theorem coarseThreshold_root_grid (B q L j d : ℕ) (allowance : ℚ) (draw : Fin B)
    (hB : 0 < B) (hq : 0 < q)
    (ha : allowance.den ∣ (L * B * q) ^ j) :
    (coarseChildThreshold B q allowance draw).den ∣
      coarseCommonDenominator 1 q L B (j + (d + 1)) := by
  have ht : (coarseChildThreshold B q allowance draw).den ∣ (L * B * q) ^ j * (B * q) := by
    simpa only [coarseChildThreshold, Nat.cast_mul] using
      coarse_rat_div_nat_den_dvd (allowance * ((draw.val + 1 : ℕ) : ℚ)) (B * q) ((L * B * q) ^ j)
        (Nat.mul_pos hB hq) (coarse_rat_mul_nat_den_dvd allowance (draw.val + 1) _ ha)
  apply ht.trans
  refine ⟨q * L * (L * B * q) ^ d, ?_⟩
  simp only [coarseCommonDenominator, one_mul, pow_add, pow_succ]
  ring

 theorem coarseChildAllowance_root_grid (B q L j d : ℕ) (allowance : ℚ) (draw : Fin B)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (ha : allowance.den ∣ (L * B * q) ^ j) :
    ((1 / (L : ℚ)) * coarseChildThreshold B q allowance draw).den ∣
      coarseCommonDenominator 1 q L B (j + (d + 1)) := by
  apply (coarseChildAllowance_grid B q L j allowance draw hB hq hL ha).trans
  refine ⟨q * (L * B * q) ^ d, ?_⟩
  simp only [coarseCommonDenominator, one_mul, pow_add, pow_succ]
  ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseThresholdStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Literal threshold numerator multiplication and denominator division.
The fixed-denominator quotient retains a root's common array grid. -/


private theorem coarseMultiply_nat_den (a : BinaryFraction) (n : ℕ) :
    (canonicalMulWithWork a (nat n)).1.representation.den = a.representation.den := by
  rw [canonicalMulWithWork_representation, nat_representation]
  simp only [UnreducedRational.mul, UnreducedRational.nat, mul_one]

 theorem coarseChildThresholdWithWork_value (B q : ℕ) (allowance : BinaryFraction) (draw : Fin B)
    (hgrid : (coarseChildThreshold B q allowance.value draw).den ∣ allowance.representation.den) :
    (coarseChildThresholdWithWork B q allowance draw).1.value =
      coarseChildThreshold B q allowance.value draw := by
  unfold coarseChildThresholdWithWork
  dsimp only
  rw [coarseDivideWithWork_value]
  · simp only [canonicalMulWithWork_value, nat_value, coarseChildThreshold, Nat.cast_add,
      Nat.cast_one]
  · change Rat.den ((canonicalMulWithWork allowance (nat (draw.val + 1))).1.value /
      (canonicalMulWithWork (nat B) (nat q)).1.value) ∣
        (canonicalMulWithWork allowance (nat (draw.val + 1))).1.representation.den
    rw [coarseMultiply_nat_den]
    simpa only [canonicalMulWithWork_value, nat_value,
      coarseChildThreshold, Nat.cast_add, Nat.cast_one] using hgrid

/-- Local allowance division uses the same Boolean division and
compression primitive as threshold construction. -/


 theorem coarseChildAllowanceWithWork_value (L : ℕ) (threshold : BinaryFraction)
    (hgrid : (threshold.value / L).den ∣ threshold.representation.den) :
    (coarseChildAllowanceWithWork L threshold).1.value = threshold.value / L := by
  have hd : (threshold.value / (nat L).value).den ∣ bitWordValue threshold.denominator := by
    change (threshold.value / (nat L).value).den ∣ threshold.representation.den
    simpa only [nat_value] using hgrid
  simpa only [coarseChildAllowanceWithWork, nat_value] using
    coarseDivideWithWork_value threshold (nat L) hd

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseBinaryWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

 theorem coarseChildrenSpan_eq {B d : ℕ} {α : Type*}
    (children : List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d)) :
    coarseChildrenSpan children = (children.map (fun data => data.1.word)).flatten.length := by
  induction children with
  | nil => rfl
  | cons data rest ih =>
    simp only [coarseChildrenSpan, List.map_cons, List.flatten_cons, List.length_append, ih]

 theorem coarseChildrenSpan_ofFn {B d : ℕ} {α : Type*}
    (children : Fin B → CoarseSourceTree B α d) (draws : Fin B → Fin B)
    (below : Fin B → CoarseThresholdDraws B d) :
    coarseChildrenSpan (List.ofFn fun i => (children i, draws i, below i)) =
      (CoarseSourceTree.branch children).word.length := by
  rw [coarseChildrenSpan_eq]
  simp only [List.map_ofFn, Function.comp_def, CoarseSourceTree.word]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseScalarBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

 theorem coarseDivideWithWork_den_length (a b : BinaryFraction) :
    (coarseDivideWithWork a b).1.denominator.length = Nat.size a.representation.den := by
  change (trimBitWordWithWork a.denominator).1.length = _
  exact trimBitWordWithWork_length a.denominator

 theorem coarseDivideWithWork_bounds (two a b : BinaryFraction) (V D A : ℕ)
    (hden : a.representation.den = two.representation.den)
    (hd : Nat.size two.representation.den ≤ D)
    (hgrid : (a.value / b.value).den ∣ a.representation.den)
    (hn : 0 ≤ a.value / b.value) (hv : a.value / b.value ≤ V)
    (hA : Nat.size V + 2 * D + 1 ≤ A) :
    CoarseGridCell two (coarseDivideWithWork a b).1 V D A := by
  have hd' : Nat.size a.representation.den ≤ D := by simpa only [hden] using hd
  have hval := coarseDivideWithWork_value a b hgrid
  refine ⟨(coarseDivideWithWork_den a b).trans hden,
    (coarseDivideWithWork_den_length a b).trans_le hd', ?_, ?_, ?_⟩
  · rw [hval]; exact hn
  · rw [hval]; exact hv
  · apply (coarseCompact_width _ V D (coarseCompact_divide a b) ?_ ?_).trans hA
    · rw [hval, abs_of_nonneg hn]; exact hv
    · rw [coarseDivideWithWork_den]; exact hd'

 theorem coarseChildThresholdWithWork_bounds (two allowance : BinaryFraction)
    (B q V D A : ℕ) (draw : Fin B) (hq : 0 < q)
    (ha : CoarseGridCell two allowance V D A)
    (hd : Nat.size two.representation.den ≤ D)
    (hgrid : (coarseChildThreshold B q allowance.value draw).den ∣ allowance.representation.den)
    (hA : Nat.size V + 2 * D + 1 ≤ A) :
    CoarseGridCell two (coarseChildThresholdWithWork B q allowance draw).1 V D A := by
  let num := (canonicalMulWithWork allowance (nat (draw.val + 1))).1
  let den := (canonicalMulWithWork (nat B) (nat q)).1
  have hn : num.representation.den = allowance.representation.den := by
    change (canonicalMulWithWork allowance (nat (draw.val + 1))).1.representation.den = _
    rw [canonicalMulWithWork_representation, nat_representation]
    simp only [UnreducedRational.mul, UnreducedRational.nat, mul_one]
  have hv : num.value / den.value = coarseChildThreshold B q allowance.value draw := by
    simp only [num, den, canonicalMulWithWork_value, nat_value, coarseChildThreshold]
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have hu := (coarseChildThreshold_le_scale draw (q : ℚ) allowance.value hq' ha.2.2.1).trans
    ((div_le_self ha.2.2.1 (by exact_mod_cast hq)).trans ha.2.2.2.1)
  change CoarseGridCell two (coarseDivideWithWork num den).1 V D A
  exact coarseDivideWithWork_bounds two num den V D A (hn.trans ha.1) hd
    (by rw [hv, hn]; exact hgrid)
    (by rw [hv]; exact coarseChildThreshold_nonneg draw hq'.le ha.2.2.1)
    (by rw [hv]; exact hu) hA

 theorem coarseChildAllowanceWithWork_bounds (two threshold : BinaryFraction)
    (L V D A : ℕ) (hL : 0 < L) (ht : CoarseGridCell two threshold V D A)
    (hd : Nat.size two.representation.den ≤ D)
    (hgrid : (threshold.value / L).den ∣ threshold.representation.den)
    (hA : Nat.size V + 2 * D + 1 ≤ A) :
    CoarseGridCell two (coarseChildAllowanceWithWork L threshold).1 V D A := by
  change CoarseGridCell two (coarseDivideWithWork threshold (nat L)).1 V D A
  apply coarseDivideWithWork_bounds two threshold (nat L) V D A ht.1 hd
  · simpa only [nat_value] using hgrid
  · rw [nat_value]; exact div_nonneg ht.2.2.1 (by positivity)
  · rw [nat_value]
    exact (div_le_self ht.2.2.1 (by exact_mod_cast hL)).trans ht.2.2.2.1
  · exact hA

end BinaryFraction
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

 theorem coarseLevelMagnitude_pos (N k B d : ℕ) : 0 < coarseLevelMagnitude N k B d := by
  unfold coarseLevelMagnitude
  positivity

 theorem coarseLevelMagnitude_ge (N k B d : ℕ) : k ≤ coarseLevelMagnitude N k B d := by
  have hp : 1 ≤ (2 * B + 2) ^ (d + 1) := by
    have hz : 0 < (2 * B + 2) ^ (d + 1) := by positivity
    omega
  unfold coarseLevelMagnitude
  nlinarith

 theorem coarseLevelMagnitude_mono (N k B d e : ℕ) (h : d ≤ e) :
    coarseLevelMagnitude N k B d ≤ coarseLevelMagnitude N k B e := by
  unfold coarseLevelMagnitude
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_right (by omega) (by omega)

 theorem coarseLevelMagnitude_succ (N k B d : ℕ) :
    B * (coarseLevelMagnitude N k B d + k) + 2 ≤ coarseLevelMagnitude N k B (d + 1) := by
  have hk := coarseLevelMagnitude_ge N k B d
  have hp := coarseLevelMagnitude_pos N k B d
  have heq : coarseLevelMagnitude N k B (d + 1) =
      coarseLevelMagnitude N k B d * (2 * B + 2) := by
    unfold coarseLevelMagnitude
    rw [show d + 1 + 1 = (d + 1) + 1 by omega, pow_succ]
    ring
  rw [heq]
  nlinarith

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseBinaryBitWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Actual Boolean work of the complete pruning-stopped evaluator. The
hypotheses bound input registers and the common grid, not execution cost. -/
 theorem coarseBinaryEval_bitWork_oai {B d : ℕ} {α : Type*} [DecidableEq α]
    (k q L N R D A : ℕ) (frame : List (Option α)) (two : BinaryFraction)
    (tree : CoarseSourceTree B α d) (draws : CoarseThresholdDraws B d)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (htwo : two.value = 2)
    (htw : two.width ≤ A) (hd : Nat.size two.representation.den ≤ D)
    (hroot : two.representation.den = coarseCommonDenominator 1 q L B R)
    (hBbits : Nat.size B + 2 ≤ A) (hqbits : Nat.size q + 2 ≤ A)
    (hLbits : Nat.size L + 2 ≤ A) (hNbits : Nat.size N + 2 ≤ A)
    (hbound : Nat.size (coarseLevelMagnitude N k B R + 2) + 2 * D + 1 ≤ A)
    (j : ℕ) (hdepth : j + d = R) (allowance : BinaryFraction) (start : ℕ)
    (ha : CoarseGridCell two allowance k D A)
    (hpath : allowance.value.den ∣ (L * B * q) ^ j)
    (hstart : start + tree.word.length ≤ N) :
    CoarseBinaryBox two (2 * k + 1) (coarseLevelMagnitude N k B d) D A
      (coarseBinaryEval k q L frame two tree draws allowance start).1 ∧
    (coarseBinaryEval k q L frame two tree draws allowance start).2 ≤
      (100000000 * (A + 1) ^ 2) * coarseBinaryWeight k q L tree draws allowance := by
  have hkbound : Nat.size k + 2 * D + 1 ≤ A :=
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.size_le_size
      ((coarseLevelMagnitude_ge N k B R).trans (by omega))) _) _).trans hbound
  induction tree generalizing j allowance start with
  | leaf letter =>
    have hnat : (nat (CoarseSourceTree.leaf (B := B) letter).word.length).width ≤ A :=
      (nat_width_le _).trans ((Nat.add_le_add_right (Nat.size_le_size (by omega)) 2).trans hNbits)
    have hp := leWithWork_cost (nat (CoarseSourceTree.leaf (B := B) letter).word.length) allowance A hnat ha.2.2.2.2
    have hs : Nat.size (CoarseSourceTree.leaf (B := B) letter).word.length ≤ A :=
      (Nat.size_le_size (show (CoarseSourceTree.leaf (B := B) letter).word.length ≤ N by omega)).trans (by omega)
    rw [coarseBinaryEval, coarseBinaryWeight]
    split_ifs
    · exact ⟨coarseBinaryBox_none _ _ _ _ _, by dsimp only; nlinarith only [hp, hs, Nat.zero_le A]⟩
    · have hvbound : Nat.size (coarseLevelMagnitude N k B 0) + 2 * D + 1 ≤ A :=
        (Nat.add_le_add_right (Nat.add_le_add_right (Nat.size_le_size
          ((coarseLevelMagnitude_mono N k B 0 R (by omega)).trans (by omega))) _) _).trans hbound
      have hcell (shift : Fin (2 * k + 1)) :
          CoarseGridCell two (coarseGridNatWithWork allowance.denominator allowance.denominator_pos
            (coarseShiftCost k frame (.leaf (B := B) letter) start shift)).1
            (coarseLevelMagnitude N k B 0) D A := by
        apply coarseGridNatWithWork_bounds two _ _ _ _ _ _ ha.1 ha.2.1 _ hvbound
        have hcost : coarseShiftCost k frame (.leaf (B := B) letter) start shift ≤ 1 := by
          cases letter <;> simp only [coarseShiftCost] <;> (try split_ifs) <;> omega
        exact hcost.trans (coarseLevelMagnitude_pos N k B 0)
      constructor
      · intro cells hc
        have heq : (arithmeticMapWithWork (fun shift : Fin (2 * k + 1) =>
            coarseGridNatWithWork allowance.denominator allowance.denominator_pos
              (coarseShiftCost k frame (.leaf (B := B) letter) start shift))
            (List.finRange (2 * k + 1))).1 = cells := Option.some.inj hc
        rw [← heq, arithmeticMapWithWork_value]
        refine ⟨by simp, ?_⟩
        intro a hamem
        obtain ⟨shift, _, rfl⟩ := List.mem_map.mp hamem
        exact hcell shift
      · have hc := arithmeticMapWithWork_cost (fun shift : Fin (2 * k + 1) =>
            coarseGridNatWithWork allowance.denominator allowance.denominator_pos
              (coarseShiftCost k frame (.leaf (B := B) letter) start shift))
            (List.finRange (2 * k + 1)) (100 * (A + 1) ^ 2) (by
          intro shift _
          apply coarseGridNatWithWork_cost _ _ _ A _ ((le_max_right _ _).trans ha.2.2.2.2)
          have hcost : coarseShiftCost k frame (.leaf (B := B) letter) start shift ≤ 1 := by
            cases letter <;> simp only [coarseShiftCost] <;> (try split_ifs) <;> omega
          exact (Nat.size_le_size hcost).trans (by norm_num; omega))
        simp only [List.length_finRange] at hc
        have hBn : 2 * k + 1 ≤ B * (2 * k + 1) := by nlinarith
        have hbudget := Nat.mul_le_mul_left ((A + 1) ^ 2) hBn
        have hunit : 1 ≤ (A + 1) ^ 2 := by
          have hz : 0 < (A + 1) ^ 2 := by positivity
          omega
        have hnscale := Nat.mul_le_mul_right (2 * k + 1) hunit
        dsimp only
        nlinarith only [hp, hs, hc, hbudget, hnscale, Nat.zero_le A, Nat.zero_le k]
  | @branch d children ih =>
    obtain ⟨draws, below⟩ := draws
    have hnat : (nat (CoarseSourceTree.branch children).word.length).width ≤ A :=
      (nat_width_le _).trans ((Nat.add_le_add_right (Nat.size_le_size (by omega)) 2).trans hNbits)
    have hp := leWithWork_cost (nat (CoarseSourceTree.branch children).word.length) allowance A hnat ha.2.2.2.2
    have hslen : Nat.size (CoarseSourceTree.branch children).word.length ≤ A :=
      (Nat.size_le_size (show (CoarseSourceTree.branch children).word.length ≤ N by omega)).trans (by omega)
    rw [coarseBinaryEval, coarseBinaryWeight]
    split_ifs
    · exact ⟨coarseBinaryBox_none _ _ _ _ _, by dsimp only; nlinarith only [hp, hslen, Nat.zero_le A]⟩
    · have htval (draw : Fin B) : (coarseChildThresholdWithWork B q allowance draw).1.value =
          coarseChildThreshold B q allowance.value draw := by
        apply coarseChildThresholdWithWork_value
        rw [ha.1, hroot, ← hdepth]
        exact coarseThreshold_root_grid B q L j d allowance.value draw hB hq hpath
      have htgrid (draw : Fin B) : CoarseGridCell two
          (coarseChildThresholdWithWork B q allowance draw).1 k D A := by
        apply coarseChildThresholdWithWork_bounds two allowance B q k D A draw hq ha hd _ hkbound
        rw [ha.1, hroot, ← hdepth]
        exact coarseThreshold_root_grid B q L j d allowance.value draw hB hq hpath
      have hscale : CoarseGridCell two (coarseChildAllowanceWithWork q allowance).1 k D A := by
        apply coarseChildAllowanceWithWork_bounds two allowance q k D A hq ha hd _ hkbound
        rw [ha.1, hroot, ← hdepth]
        exact coarseScale_root_grid B q L j (d + 1) allowance.value hq hpath
      have hstep (draw : Fin B) :
          CoarseGridCell two (coarseChildAllowanceWithWork L
            (coarseChildThresholdWithWork B q allowance draw).1).1 k D A ∧
          (coarseChildAllowanceWithWork L (coarseChildThresholdWithWork B q allowance draw).1).1.value.den ∣
            (L * B * q) ^ (j + 1) := by
        let threshold := (coarseChildThresholdWithWork B q allowance draw).1
        have hden : (threshold.value / L).den ∣ threshold.representation.den := by
          rw [htval draw, (htgrid draw).1, hroot, ← hdepth]
          rw [show coarseChildThreshold B q allowance.value draw / (L : ℚ) =
            (1 / (L : ℚ)) * coarseChildThreshold B q allowance.value draw by ring]
          exact coarseChildAllowance_root_grid B q L j d allowance.value draw hB hq hL hpath
        refine ⟨coarseChildAllowanceWithWork_bounds two threshold L k D A hL (htgrid draw) hd hden hkbound, ?_⟩
        rw [coarseChildAllowanceWithWork_value L threshold hden, htval draw]
        convert coarseChildAllowance_grid B q L j allowance.value draw hB hq hL hpath using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        ring
      have hchildbound : Nat.size (B * (coarseLevelMagnitude N k B d + k) + 2) + 2 * D + 1 ≤ A := by
        apply le_trans _ hbound
        apply Nat.add_le_add_right
        apply Nat.add_le_add_right
        apply Nat.size_le_size
        exact (coarseLevelMagnitude_succ N k B d).trans
          ((coarseLevelMagnitude_mono N k B (d + 1) R (by omega)).trans (by omega))
      have hc := coarseBinaryChildren_bounds k q L N (coarseLevelMagnitude N k B d) D A two allowance
        (fun child => coarseBinaryEval k q L frame two child)
        (fun child => coarseBinaryWeight k q L child)
        (List.ofFn fun i => (children i, draws i, below i)) hB (by simp) htwo htw ha.2.2.2.2
        hBbits hqbits hLbits (by omega) (fun draw => (htgrid draw).2.2.2.2) hscale hchildbound (by
          intro child draw childBelow hmem s hs
          obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
          cases hi
          exact ih i (below i) (j + 1) (by omega) _ s (hstep (draws i)).1 (hstep (draws i)).2 hs)
        start (by rwa [coarseChildrenSpan_ofFn])
      constructor
      · have hm : (List.ofFn fun i => (children i, draws i, below i)).length *
            (coarseLevelMagnitude N k B d + k) ≤ coarseLevelMagnitude N k B (d + 1) := by
          simp only [List.length_ofFn]
          exact (Nat.le_add_right _ 2).trans (coarseLevelMagnitude_succ N k B d)
        exact coarseBinaryBox_mono two (2 * k + 1) _ _ D A _ hc.1 hm
      · have hcost := hc.2
        simp only [List.length_ofFn] at hcost
        have hprune : (leWithWork (nat (CoarseSourceTree.branch children).word.length) allowance).2 +
            Nat.size (CoarseSourceTree.branch children).word.length + 1 ≤ 100000000 * (A + 1) ^ 2 := by
          nlinarith only [hp, hslen, Nat.zero_le A]
        dsimp only
        nlinarith only [hcost, hprune]

end BinaryFraction
end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.BinaryFraction.coarseBinaryEval_bitWork_oai.{u_1} := @OAI.EditApproximation.BinaryFraction.coarseBinaryEval_bitWork_oai.{u_1}
