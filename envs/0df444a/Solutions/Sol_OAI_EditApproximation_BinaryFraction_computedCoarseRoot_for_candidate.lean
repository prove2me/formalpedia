-- Prove2me | solution 1 for OAI.EditApproximation.BinaryFraction.computedCoarseRoot_for_candidate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:26:52.726034+00:00
-- url     : https://prove2.me/submissions/4d5c1b2d-af4e-441d-afa9-286bf8ef0032

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
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea000
import Definitions.Def_OAIQ361V3Ea001
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_coarseBinaryEval_bitWork

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPowerStorage
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Construction of a prescribed power denominator uses literal Boolean
multiplication and trimming. The subsequent cache compression therefore has
no uncharged conversion from a natural number to its binary representation. -/

namespace EditApproximation



theorem bitPowerWithWork_length (base : List Bool) (n : ℕ) :
    (bitPowerWithWork base n).1.length = Nat.size (bitWordValue base ^ n) := by
  cases n with
  | zero => simp [bitPowerWithWork]
  | succ n =>
    simp only [bitPowerWithWork, trimBitWordWithWork_length, bitMulWithWork_value,
      bitPowerWithWork_value, pow_succ]

theorem bitPowerWithWork_length_le (base : List Bool) (n B : ℕ) (hB : base.length ≤ B) :
    (bitPowerWithWork base n).1.length ≤ n * B + 1 := by
  rw [bitPowerWithWork_length]
  exact (natural_power_bit_length _ _).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left n
      ((Nat.size_le.mpr (bitWordValue_lt_pow_length base)).trans hB)) 1)

theorem bitPowerWithWork_cost (base : List Bool) (n B : ℕ) (hB : base.length ≤ B) :
    (bitPowerWithWork base n).2 ≤ bitPowerBitBudget n B := by
  let W := (n + 1) * (B + 1)
  have hbase : base.length ≤ W := by
    have := Nat.le_mul_of_pos_left (B + 1) (by omega : 0 < n + 1)
    dsimp only [W]
    omega
  have hwidth (j : ℕ) (hj : j ≤ n) : (bitPowerWithWork base j).1.length ≤ W := by
    have hb := bitPowerWithWork_length_le base j B hB
    have hm := Nat.mul_le_mul_right B hj
    dsimp only [W]
    nlinarith only [hb, hm, Nat.zero_le n, Nat.zero_le B]
  have hcost (j : ℕ) (hj : j ≤ n) :
      (bitPowerWithWork base j).2 ≤ 1 + j * (200 * (W + 1) ^ 2) := by
    induction j with
    | zero => simp [bitPowerWithWork]
    | succ j ih =>
      have hj' : j ≤ n := by omega
      have hi := ih hj'
      have hw := hwidth j hj'
      let previous := bitPowerWithWork base j
      let product := bitMulWithWork previous.1 base
      change previous.1.length ≤ W at hw
      have hp := bitMulWithWork_cost previous.1 base
      have hpl := bitMulWithWork_length previous.1 base
      have ht := trimBitWordWithWork_cost product.1
      change product.2 ≤ _ at hp
      have hstep : product.2 + (trimBitWordWithWork product.1).2 + 2 ≤ 200 * (W + 1) ^ 2 := by
        have hmul := Nat.mul_le_mul (show previous.1.length + 1 ≤ W + 1 by omega)
          (show previous.1.length + base.length + 1 ≤ 2 * W + 1 by omega)
        change product.1.length ≤ 2 * previous.1.length + base.length + 1 at hpl
        nlinarith only [hp, hpl, ht, hmul, hw, hbase, Nat.zero_le W]
      change (bitPowerWithWork base j).2 + product.2 + (trimBitWordWithWork product.1).2 + 2 ≤ _
      rw [Nat.add_mul, Nat.one_mul]
      omega
  exact hcost n le_rfl



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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseSeed
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The actual bounded-shift coarse tree

Section 3's deterministic shift representation uses a complete finite
branching tree with empty/singleton source leaves. Bounded integer shifts
are encoded by `Fin (2k+1)`; code `k` is shift zero. Virtual target positions
are represented by fresh `none` symbols in a finite surrounding frame.
-/

namespace EditApproximation

open Finset EditDistortion

universe u



/-- The literal consecutive capacity chunks cover exactly the permitted
before; zero capacity and empty trailing chunks are included. -/
theorem coarse_capacity_chunks {α : Type u} (source : List α) (B capacity : ℕ) :
    (List.ofFn fun i : Fin B => (source.drop (i.val * capacity)).take capacity).flatten =
      source.take (B * capacity) := by
  induction B generalizing source with
  | zero => simp
  | succ B ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    simp only [Fin.val_zero, zero_mul, List.drop_zero, Fin.val_succ]
    have hchunks : (List.ofFn fun i : Fin B =>
        (source.drop ((i.val + 1) * capacity)).take capacity) =
        List.ofFn (fun i : Fin B => ((source.drop capacity).drop (i.val * capacity)).take capacity) := by
      congr 1
      funext i
      simp only [List.drop_drop, Nat.add_mul, one_mul, Nat.add_comm]
    rw [hchunks, ih, ← List.take_add]
    simp only [Nat.succ_mul, Nat.add_comm]

/-- A concrete complete source tree with empty/singleton leaves. Its
recursive child chunks have the capacity prescribed by the remaining depth. -/


theorem coarseSourceTreeOfList_word {α : Type u} (B D : ℕ) (source : List α) :
    (coarseSourceTreeOfList B D source).word = source.take (B ^ D) := by
  induction D generalizing source with
  | zero => simp only [coarseSourceTreeOfList, CoarseSourceTree.word, pow_zero, List.take_one]
  | succ D ih =>
    simp only [coarseSourceTreeOfList, CoarseSourceTree.word, ih, List.take_take, min_self]
    rw [coarse_capacity_chunks, pow_succ, Nat.mul_comm]

theorem coarseSourceTreeOfList_word_eq {α : Type u} (B D : ℕ) (source : List α)
    (hcapacity : source.length ≤ B ^ D) :
    (coarseSourceTreeOfList B D source).word = source := by
  rw [coarseSourceTreeOfList_word, List.take_of_length_le hcapacity]

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarsePadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Fresh-symbol right padding

Padding uses `none`, while original letters are tagged by `some`. Removing
the fresh symbols contracts every unrestricted unit-cost edit script.
-/

namespace EditApproximation

open EditDistortion

universe u v

/-- Right padding to a prescribed common width with a fresh tagged letter. -/


theorem coarsePadTo_length {α : Type u} (n : ℕ) (word : List α) (h : word.length ≤ n) :
    (coarsePadTo n word).length = n := by
  simp only [coarsePadTo, List.length_append, List.length_map, List.length_replicate]
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseInitial
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The executable initial integer estimate

The direct branches handle long targets and equality. The remaining branch
evaluates the concrete coarse recurrence at every dyadic guess, takes the
rational minimum, rounds up and clamps to the input length.
-/

namespace EditApproximation

open EditDistortion Finset MeasureTheory ProbabilityTheory

universe u

theorem coarseEntryTree_word {α : Type u} (B D : ℕ) (x y : List α)
    (hcapacity : coarseEntryWidth x y ≤ B ^ D) :
    (coarseEntryTree B D x y).word = coarsePadTo (coarseEntryWidth x y) x := by
  apply coarseSourceTreeOfList_word_eq
  rw [coarsePadTo_length _ _ (le_max_left _ _)]
  exact hcapacity

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

end BinaryFraction
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

 theorem coarseChildThresholdWithWork_den (B q : ℕ) (allowance : BinaryFraction) (draw : Fin B) :
    (coarseChildThresholdWithWork B q allowance draw).1.representation.den = allowance.representation.den := by
  exact (coarseDivideWithWork_den _ _).trans (coarseMultiply_nat_den allowance _)

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

 theorem coarseChildAllowanceWithWork_den (L : ℕ) (threshold : BinaryFraction) :
    (coarseChildAllowanceWithWork L threshold).1.representation.den = threshold.representation.den :=
  coarseDivideWithWork_den _ _

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseLabelWork
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.coarseInitialMeasure_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

/-- Only expanded internal nodes request their child thresholds. The full
product seed is a specification; labels below a pruned node are never read. -/




private theorem coarseLabelChildren_le {B d : ℕ} {α : Type*} (Q lam allowance : ℚ)
    (labels arrays : CoarseSourceTree B α d → CoarseThresholdDraws B d → ℚ → ℕ)
    (children : List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d))
    (hle : ∀ child draw below, (child, draw, below) ∈ children → ∀ a, labels child below a ≤ arrays child below a) :
    coarseLabelChildren Q lam allowance labels children ≤
      coarseActiveChildrenWork Q lam allowance arrays children := by
  induction children with
  | nil => exact le_rfl
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    exact Nat.add_le_add (hle child draw below List.mem_cons_self _)
      (ih (fun child draw below hmem => hle child draw below (List.mem_cons_of_mem _ hmem)))

 theorem coarseLabelCount_le_arrayWork {B d : ℕ} {α : Type*} (k : ℕ) (Q lam : ℚ)
    (tree : CoarseSourceTree B α d) (draws : CoarseThresholdDraws B d) (allowance : ℚ) :
    coarseLabelCount Q lam tree draws allowance ≤ coarseActiveArrayWork k Q lam tree draws allowance := by
  induction tree generalizing allowance with
  | leaf letter =>
    simp only [coarseLabelCount, coarseActiveArrayWork]
    split_ifs <;> omega
  | branch children ih =>
    obtain ⟨draws, below⟩ := draws
    simp only [coarseLabelCount, coarseActiveArrayWork]
    split_ifs
    · exact le_rfl
    · have hc := coarseLabelChildren_le Q lam allowance
        (fun child => coarseLabelCount Q lam child)
        (fun child => coarseActiveArrayWork k Q lam child)
        (List.ofFn fun i => (children i, draws i, below i)) (by
          intro child draw childBelow hmem a
          obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
          cases hi
          exact ih i (below i) a)
      have hunit : B ≤ B * (2 * k + 1) := by nlinarith
      exact Nat.add_le_add hunit hc

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseDenominatorArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

 theorem coarseDenominatorWithWork_length (allowanceDen q L branching : List Bool) (D : ℕ) :
    (coarseDenominatorWithWork allowanceDen q L branching D).1.length =
      Nat.size (coarseCommonDenominator (bitWordValue allowanceDen) (bitWordValue q)
        (bitWordValue L) (bitWordValue branching) D) := by
  simp only [coarseDenominatorWithWork, trimBitWordWithWork_length,
    bitMulWithWork_value, bitPowerWithWork_value, trimBitWordWithWork_value,
    coarseCommonDenominator]

 theorem coarseDenominatorWithWork_cost (allowanceDen q L branching : List Bool) (D A : ℕ)
    (ha : allowanceDen.length ≤ A) (hq : q.length ≤ A) (hL : L.length ≤ A)
    (hb : branching.length ≤ A) :
    (coarseDenominatorWithWork allowanceDen q L branching D).2 ≤
      bitPowerBitBudget D (7 * A + 3) + 1000 * (10 * (D + 2) * (A + 1) + 1) ^ 2 := by
  let first := bitMulWithWork L branching
  let base := bitMulWithWork first.1 q
  let trimmed := trimBitWordWithWork base.1
  let power := bitPowerWithWork trimmed.1 D
  let initial := bitMulWithWork allowanceDen q
  let product := bitMulWithWork initial.1 power.1
  let W := 10 * (D + 2) * (A + 1)
  have hf := bitMulWithWork_cost L branching
  have hfl := bitMulWithWork_length L branching
  have hbc := bitMulWithWork_cost first.1 q
  have hbl := bitMulWithWork_length first.1 q
  have ht := (trimBitWordWithWork_cost base.1).le
  have htl : trimmed.1.length ≤ 7 * A + 3 := by
    have hh : trimmed.1.length ≤ base.1.length := by
      rw [trimBitWordWithWork_length]
      exact Nat.size_le.mpr (bitWordValue_lt_pow_length _)
    change base.1.length ≤ 2 * first.1.length + q.length + 1 at hbl
    change first.1.length ≤ 2 * L.length + branching.length + 1 at hfl
    omega
  have hp := bitPowerWithWork_cost trimmed.1 D (7 * A + 3) htl
  have hpl := bitPowerWithWork_length_le trimmed.1 D (7 * A + 3) htl
  have hi := bitMulWithWork_cost allowanceDen q
  have hil := bitMulWithWork_length allowanceDen q
  have hprod := bitMulWithWork_cost initial.1 power.1
  have hprodl := bitMulWithWork_length initial.1 power.1
  have htrim := trimBitWordWithWork_cost product.1
  have hfirst : first.1.length ≤ W := by
    change first.1.length ≤ 2 * L.length + branching.length + 1 at hfl
    dsimp only [W]
    nlinarith only [hfl, hL, hb, Nat.zero_le D, Nat.zero_le A]
  have hbase : base.1.length ≤ W := by
    change base.1.length ≤ 2 * first.1.length + q.length + 1 at hbl
    change first.1.length ≤ 2 * L.length + branching.length + 1 at hfl
    dsimp only [W]
    nlinarith only [hbl, hfl, hq, hL, hb, Nat.zero_le D, Nat.zero_le A]
  have hinitial : initial.1.length ≤ W := by
    change initial.1.length ≤ 2 * allowanceDen.length + q.length + 1 at hil
    dsimp only [W]
    nlinarith only [hil, ha, hq, Nat.zero_le D, Nat.zero_le A]
  have hpower : power.1.length ≤ W := by
    dsimp only [W]
    nlinarith only [hpl, Nat.zero_le D, Nat.zero_le A]
  have hAW : A ≤ W := by dsimp only [W]; nlinarith only [Nat.zero_le D, Nat.zero_le A]
  have bound (x y : List Bool) (hx : x.length ≤ W) (hy : y.length ≤ W) :
      (bitMulWithWork x y).2 ≤ 40 * (W + 1) ^ 2 := by
    apply (bitMulWithWork_cost x y).trans
    have hm := Nat.mul_le_mul (show x.length + 1 ≤ W + 1 by omega)
      (show x.length + y.length + 1 ≤ 2 * (W + 1) by omega)
    nlinarith only [hm]
  have hf' := bound L branching (hL.trans hAW) (hb.trans hAW)
  have hb' := bound first.1 q hfirst (hq.trans hAW)
  have hi' := bound allowanceDen q (ha.trans hAW) (hq.trans hAW)
  have hprod' := bound initial.1 power.1 hinitial hpower
  change base.1.length ≤ 2 * first.1.length + q.length + 1 at hbl
  change product.1.length ≤ 2 * initial.1.length + power.1.length + 1 at hprodl
  change first.2 + base.2 + trimmed.2 + power.2 + initial.2 + product.2 +
    (trimBitWordWithWork product.1).2 + 7 ≤ _
  change trimmed.2 ≤ 3 * base.1.length + 1 at ht
  change first.2 ≤ _ at hf'
  change base.2 ≤ _ at hb'
  change initial.2 ≤ _ at hi'
  change product.2 ≤ _ at hprod'
  change power.2 ≤ _ at hp
  change _ ≤ bitPowerBitBudget D (7 * A + 3) + 1000 * (W + 1) ^ 2
  nlinarith only [hf', hb', hi', hprod', hp, ht, htrim, hbase, hprodl, hinitial,
    hpower, Nat.zero_le W]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseRootExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
namespace BinaryFraction



 theorem coarseRootDenominator_length (B q L d : ℕ) :
    (coarseRootDenominator B q L d).1.length = Nat.size (coarseCommonDenominator 1 q L B d) := by
  simp only [coarseRootDenominator, coarseDenominatorWithWork_length, bitWordValue_bits]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseWeightSimulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

 theorem coarseBinaryChildrenWeight_eq {B d : ℕ} {α : Type*} (q L : ℕ)
    (weight : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ)
    (arrays labels : CoarseSourceTree B α d → CoarseThresholdDraws B d → ℚ → ℕ)
    (allowance : BinaryFraction)
    (children : List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d))
    (he : ∀ child draw below, (child, draw, below) ∈ children →
      weight child below (coarseChildAllowanceWithWork L
        (coarseChildThresholdWithWork B q allowance draw).1).1 =
      arrays child below ((1 / L) * coarseChildThreshold B q allowance.value draw) +
      labels child below ((1 / L) * coarseChildThreshold B q allowance.value draw) + 1) :
    coarseBinaryChildrenWeight q L weight allowance children =
      coarseActiveChildrenWork q (1 / L) allowance.value arrays children +
      coarseLabelChildren q (1 / L) allowance.value labels children + children.length := by
  induction children with
  | nil => rfl
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    rw [coarseBinaryChildrenWeight, he child draw below List.mem_cons_self,
      ih (fun child draw below hmem => he child draw below (List.mem_cons_of_mem _ hmem))]
    simp only [coarseActiveChildrenWork, coarseLabelChildren, List.length_cons]
    omega

 theorem coarseBinaryWeight_eq {B d : ℕ} {α : Type*}
    (k q L R : ℕ) (tree : CoarseSourceTree B α d) (draws : CoarseThresholdDraws B d)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (j : ℕ) (hdepth : j + d = R) (allowance : BinaryFraction)
    (ha : allowance.representation.den = coarseCommonDenominator 1 q L B R)
    (hpath : allowance.value.den ∣ (L * B * q) ^ j) :
    coarseBinaryWeight k q L tree draws allowance =
      coarseActiveArrayWork k q (1 / L) tree draws allowance.value +
      coarseLabelCount q (1 / L) tree draws allowance.value + 1 := by
  induction tree generalizing j allowance with
  | leaf letter =>
    have hp := leWithWork_value (nat (CoarseSourceTree.leaf (B := B) letter).word.length) allowance
    rw [nat_value] at hp
    rw [coarseBinaryWeight, coarseActiveArrayWork, coarseLabelCount]
    by_cases h : ((CoarseSourceTree.leaf (B := B) letter).word.length : ℚ) ≤ allowance.value
    · simp only [ite_eq_left (hp.mpr h), ite_eq_left h]
    · simp only [ite_eq_right (fun hh => h (hp.mp hh)), ite_eq_right h]
  | @branch d children ih =>
    obtain ⟨draws, below⟩ := draws
    have hp := leWithWork_value (nat (CoarseSourceTree.branch children).word.length) allowance
    rw [nat_value] at hp
    rw [coarseBinaryWeight, coarseActiveArrayWork, coarseLabelCount]
    by_cases h : ((CoarseSourceTree.branch children).word.length : ℚ) ≤ allowance.value
    · simp only [ite_eq_left (hp.mpr h), ite_eq_left h]
    · simp only [ite_eq_right (fun hh => h (hp.mp hh)), ite_eq_right h]
      have he : coarseBinaryChildrenWeight q L (fun child => coarseBinaryWeight k q L child)
          allowance (List.ofFn fun i => (children i, draws i, below i)) =
          coarseActiveChildrenWork q (1 / L) allowance.value
            (fun child => coarseActiveArrayWork k q (1 / L) child)
            (List.ofFn fun i => (children i, draws i, below i)) +
          coarseLabelChildren q (1 / L) allowance.value
            (fun child => coarseLabelCount q (1 / L) child)
            (List.ofFn fun i => (children i, draws i, below i)) + B := by
        refine (coarseBinaryChildrenWeight_eq q L (fun child => coarseBinaryWeight k q L child)
          (fun child => coarseActiveArrayWork k q (1 / L) child)
          (fun child => coarseLabelCount q (1 / L) child) allowance
          (List.ofFn fun i => (children i, draws i, below i)) ?_).trans ?_
        · intro child draw childBelow hmem
          obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
          cases hi
          let threshold := (coarseChildThresholdWithWork B q allowance (draws i)).1
          let childAllowance := (coarseChildAllowanceWithWork L threshold).1
          have ht : threshold.value = coarseChildThreshold B q allowance.value (draws i) := by
            apply coarseChildThresholdWithWork_value
            rw [ha, ← hdepth]
            exact coarseThreshold_root_grid B q L j d allowance.value (draws i) hB hq hpath
          have htd : threshold.representation.den = coarseCommonDenominator 1 q L B R :=
            (coarseChildThresholdWithWork_den B q allowance (draws i)).trans ha
          have hcd : childAllowance.representation.den = coarseCommonDenominator 1 q L B R :=
            (coarseChildAllowanceWithWork_den L threshold).trans htd
          have hv : childAllowance.value = (1 / (L : ℚ)) *
              coarseChildThreshold B q allowance.value (draws i) := by
            have hg : (threshold.value / L).den ∣ threshold.representation.den := by
              rw [ht, htd, ← hdepth]
              rw [show coarseChildThreshold B q allowance.value (draws i) / (L : ℚ) =
                (1 / (L : ℚ)) * coarseChildThreshold B q allowance.value (draws i) by ring]
              exact coarseChildAllowance_root_grid B q L j d allowance.value (draws i) hB hq hL hpath
            have hz := coarseChildAllowanceWithWork_value L threshold hg
            change childAllowance.value = _ at hz
            rw [hz, ht]
            ring
          have hcp : childAllowance.value.den ∣ (L * B * q) ^ (j + 1) := by
            rw [hv]
            exact coarseChildAllowance_grid B q L j allowance.value (draws i) hB hq hL hpath
          have hc := ih i (below i) (j + 1) (by omega) childAllowance hcd hcp
          rw [hv] at hc
          exact hc
        · simp only [List.length_ofFn]
      rw [he]
      omega

 theorem coarseBinaryWeight_le {B d : ℕ} {α : Type*}
    (k q L R : ℕ) (tree : CoarseSourceTree B α d) (draws : CoarseThresholdDraws B d)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (j : ℕ) (hdepth : j + d = R) (allowance : BinaryFraction)
    (ha : allowance.representation.den = coarseCommonDenominator 1 q L B R)
    (hpath : allowance.value.den ∣ (L * B * q) ^ j) :
    coarseBinaryWeight k q L tree draws allowance ≤
      2 * coarseActiveArrayWork k q (1 / L) tree draws allowance.value + 1 := by
  rw [coarseBinaryWeight_eq k q L R tree draws hB hq hL j hdepth allowance ha hpath]
  have h := coarseLabelCount_le_arrayWork k (q : ℚ) (1 / L) tree draws allowance.value
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseRootWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

 theorem coarseRootWithWork_cost {B d : ℕ} {α : Type*} [DecidableEq α]
    (k q L N D A : ℕ) (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (frame : List (Option α)) (tree : CoarseSourceTree B α d)
    (draws : CoarseThresholdDraws B d) (start : ℕ) (shift : Fin (2 * k + 1))
    (hBbits : Nat.size B + 2 ≤ A) (hqbits : Nat.size q + 2 ≤ A)
    (hLbits : Nat.size L + 2 ≤ A) (hNbits : Nat.size N + 2 ≤ A)
    (hd : Nat.size (coarseCommonDenominator 1 q L B d) ≤ D) (hD : D ≤ A)
    (hbound : Nat.size (coarseLevelMagnitude N k B d + 2) + 2 * D + 1 ≤ A)
    (hstart : start + tree.word.length ≤ N) :
    (coarseRootWithWork k q L hB hq hL frame tree draws start shift).2 ≤
      bitPowerBitBudget d (7 * A + 3) + 1000 * (10 * (d + 2) * (A + 1) + 1) ^ 2 +
      100001000 * (A + 1) ^ 2 * (2 * coarseActiveArrayWork k q (1 / L) tree draws k + 1) := by
  let den := coarseRootDenominator B q L d
  let denPos := coarseRootDenominator_pos B q L d hB hq hL
  let two := (coarseGridNatWithWork den.1 denPos 2).1
  let allowance := (coarseGridNatWithWork den.1 denPos k).1
  have hden := coarseRootDenominator_value B q L d
  have hdenLen : den.1.length ≤ D := (coarseRootDenominator_length B q L d).trans_le hd
  have htwo : two.value = 2 := coarseGridNatWithWork_value _ _ 2
  have htwoDen : two.representation.den = coarseCommonDenominator 1 q L B d :=
    (coarseGridNatWithWork_den _ _ 2).trans hden
  have hkwidth : Nat.size k + 2 * D + 1 ≤ A :=
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.size_le_size
      ((coarseLevelMagnitude_ge N k B d).trans (by omega))) _) _).trans hbound
  have h2width : Nat.size 2 + 2 * D + 1 ≤ A :=
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.size_le_size (by omega : 2 ≤ coarseLevelMagnitude N k B d + 2)) _) _).trans hbound
  have htwocell : CoarseGridCell two two 2 D A :=
    coarseGridNatWithWork_bounds two den.1 denPos 2 2 D A
      (coarseGridNatWithWork_den _ _ 2).symm hdenLen le_rfl h2width
  have hacell : CoarseGridCell two allowance k D A :=
    coarseGridNatWithWork_bounds two den.1 denPos k k D A
      (coarseGridNatWithWork_den _ _ 2).symm hdenLen le_rfl hkwidth
  have hav : allowance.value = k := coarseGridNatWithWork_value _ _ k
  have hpath : allowance.value.den ∣ (L * B * q) ^ 0 := by
    simp only [hav, Rat.den_natCast, one_dvd]
  have hc := (coarseBinaryEval_bitWork k q L N d D A frame two tree draws hB hq hL htwo
    htwocell.2.2.2.2 (by rw [htwoDen]; exact hd) htwoDen hBbits hqbits hLbits hNbits hbound
    0 (by omega) allowance start hacell hpath hstart).2
  have hw := coarseBinaryWeight_le k q L d tree draws hB hq hL 0 (by omega) allowance
    (hacell.1.trans htwoDen) hpath
  rw [hav] at hw
  have heval := hc.trans (Nat.mul_le_mul_left (100000000 * (A + 1) ^ 2) hw)
  have htwoCost := coarseGridNatWithWork_cost den.1 denPos 2 A (by omega)
    (hdenLen.trans hD)
  have haCost := coarseGridNatWithWork_cost den.1 denPos k A (by omega) (hdenLen.trans hD)
  have hdenCost := coarseDenominatorWithWork_cost (1 : ℕ).bits q.bits L.bits B.bits d A
    (by simp only [Nat.size_eq_bits_len, Nat.size_one]; omega)
    (by rw [Nat.size_eq_bits_len]; omega)
    (by rw [Nat.size_eq_bits_len]; omega)
    (by rw [Nat.size_eq_bits_len]; omega)
  change den.2 ≤ _ at hdenCost
  have hfactor := Nat.mul_le_mul_left ((A + 1) ^ 2)
    (show 1 ≤ 2 * coarseActiveArrayWork k q (1 / L) tree draws k + 1 by omega)
  change den.2 + (coarseGridNatWithWork den.1 denPos 2).2 +
    (coarseGridNatWithWork den.1 denPos k).2 +
    (coarseBinaryEval k q L frame two tree draws allowance start).2 + 1 ≤ _
  nlinarith only [heval, htwoCost, haCost, hdenCost, hfactor, Nat.zero_le A,
    Nat.zero_le (coarseActiveArrayWork k q (1 / L) tree draws k)]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseNumericalUnit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

 theorem bitPowerBitBudget_mono (d e A C : ℕ) (hd : d ≤ e) (hA : A ≤ C) :
    bitPowerBitBudget d A ≤ bitPowerBitBudget e C := by
  have hw : (d + 1) * (A + 1) + 1 ≤ (e + 1) * (C + 1) + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul (by omega) (by omega)) 1
  have hp := Nat.pow_le_pow_left hw 2
  have hc := Nat.mul_le_mul hd (Nat.mul_le_mul_left 200 hp)
  simpa only [bitPowerBitBudget] using Nat.add_le_add_left hc 1

 theorem coarseNumericalUnit_polynomial (H : ℕ) :
    coarseNumericalUnit H ≤ 10000000000 * (H + 1) ^ 10 := by
  have hp (j : ℕ) (hj : j ≤ 10) : H ^ j ≤ (H + 1) ^ 10 :=
    (Nat.pow_le_pow_left (Nat.le_succ H) j).trans
      (Nat.pow_le_pow_right (by omega) hj)
  have h0 := hp 0 (by decide)
  have h1 := hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  have h6 := hp 6 (by decide)
  have h7 := hp 7 (by decide)
  have h8 := hp 8 (by decide)
  have h9 := hp 9 (by decide)
  unfold coarseNumericalUnit bitPowerBitBudget
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

 theorem coarseNumericalUnit_le_power (H : ℕ) (hH : 10 ≤ H) :
    coarseNumericalUnit H ≤ H ^ 30 := by
  have hc : 10000000000 ≤ H ^ 10 := by
    have h := Nat.pow_le_pow_left hH 10
    norm_num at h ⊢
    exact h
  have hh : H + 1 ≤ H ^ 2 := by nlinarith
  have hp := Nat.pow_le_pow_left hh 10
  calc
    coarseNumericalUnit H ≤ 10000000000 * (H + 1) ^ 10 := coarseNumericalUnit_polynomial H
    _ ≤ H ^ 10 * (H ^ 2) ^ 10 := Nat.mul_le_mul hc hp
    _ = H ^ 30 := by rw [← pow_mul, ← pow_add]

 theorem coarseRootWithWork_height_bound {B d : ℕ} {α : Type*} [DecidableEq α]
    (k q L N D H : ℕ) (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (frame : List (Option α)) (tree : CoarseSourceTree B α d)
    (draws : CoarseThresholdDraws B d) (start : ℕ) (shift : Fin (2 * k + 1))
    (hBbits : Nat.size B + 2 ≤ H ^ 3) (hqbits : Nat.size q + 2 ≤ H ^ 3)
    (hLbits : Nat.size L + 2 ≤ H ^ 3) (hNbits : Nat.size N + 2 ≤ H ^ 3)
    (hd : Nat.size (coarseCommonDenominator 1 q L B d) ≤ D) (hD : D ≤ H ^ 3)
    (hdepth : d ≤ H)
    (hbound : Nat.size (coarseLevelMagnitude N k B d + 2) + 2 * D + 1 ≤ H ^ 3)
    (hstart : start + tree.word.length ≤ N) :
    (coarseRootWithWork k q L hB hq hL frame tree draws start shift).2 ≤
      coarseNumericalUnit H * (2 * coarseActiveArrayWork k q (1 / L) tree draws k + 1) := by
  have h := coarseRootWithWork_cost k q L N D (H ^ 3) hB hq hL frame tree draws start shift
    hBbits hqbits hLbits hNbits hd hD hbound hstart
  have hp := bitPowerBitBudget_mono d H (7 * H ^ 3 + 3) (7 * H ^ 3 + 3) hdepth le_rfl
  have hm : 10 * (d + 2) * (H ^ 3 + 1) + 1 ≤ 10 * (H + 2) * (H ^ 3 + 1) + 1 := by
    nlinarith only [Nat.mul_le_mul_right (10 * (H ^ 3 + 1)) hdepth]
  have hc := Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left hm 2)
  have hf := Nat.mul_le_mul_left
    (bitPowerBitBudget H (7 * H ^ 3 + 3) + 1000 * (10 * (H + 2) * (H ^ 3 + 1) + 1) ^ 2)
    (show 1 ≤ 2 * coarseActiveArrayWork k q (1 / L) tree draws k + 1 by omega)
  unfold coarseNumericalUnit
  nlinarith only [h, hp, hc, hf]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseRootBounds
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

 theorem coarseBinaryRead_width (array : CoarseBinaryArray) (i A : ℕ)
    (hA : 2 ≤ A) (hw : ∀ cells, array = some cells → ∀ a ∈ cells, a.width ≤ A) :
    (coarseBinaryRead array i).width ≤ A := by
  cases array with
  | none => exact (nat_width_le 0).trans (by simpa using hA)
  | some cells =>
    simp only [coarseBinaryRead]
    cases h : cells[i]? with
    | none => exact (nat_width_le 0).trans (by simpa using hA)
    | some a => exact hw cells rfl a (List.mem_of_getElem? h)

 theorem coarseRootWithWork_width {B d : ℕ} {α : Type*} [DecidableEq α]
    (k q L N D A : ℕ) (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (frame : List (Option α)) (tree : CoarseSourceTree B α d)
    (draws : CoarseThresholdDraws B d) (start : ℕ) (shift : Fin (2 * k + 1))
    (hBbits : Nat.size B + 2 ≤ A) (hqbits : Nat.size q + 2 ≤ A)
    (hLbits : Nat.size L + 2 ≤ A) (hNbits : Nat.size N + 2 ≤ A)
    (hd : Nat.size (coarseCommonDenominator 1 q L B d) ≤ D)
    (hbound : Nat.size (coarseLevelMagnitude N k B d + 2) + 2 * D + 1 ≤ A)
    (hstart : start + tree.word.length ≤ N) :
    (coarseRootWithWork k q L hB hq hL frame tree draws start shift).1.width ≤ A := by
  let den := coarseRootDenominator B q L d
  let denPos := coarseRootDenominator_pos B q L d hB hq hL
  let two := (coarseGridNatWithWork den.1 denPos 2).1
  let allowance := (coarseGridNatWithWork den.1 denPos k).1
  have hden := coarseRootDenominator_value B q L d
  have hdenLen : den.1.length ≤ D := (coarseRootDenominator_length B q L d).trans_le hd
  have htwo : two.value = 2 := coarseGridNatWithWork_value _ _ 2
  have htwoDen : two.representation.den = coarseCommonDenominator 1 q L B d :=
    (coarseGridNatWithWork_den _ _ 2).trans hden
  have hkwidth : Nat.size k + 2 * D + 1 ≤ A :=
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.size_le_size
      ((coarseLevelMagnitude_ge N k B d).trans (by omega))) _) _).trans hbound
  have h2width : Nat.size 2 + 2 * D + 1 ≤ A :=
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.size_le_size
      (by omega : 2 ≤ coarseLevelMagnitude N k B d + 2)) _) _).trans hbound
  have htwocell : CoarseGridCell two two 2 D A :=
    coarseGridNatWithWork_bounds two den.1 denPos 2 2 D A
      (coarseGridNatWithWork_den _ _ 2).symm hdenLen le_rfl h2width
  have hacell : CoarseGridCell two allowance k D A :=
    coarseGridNatWithWork_bounds two den.1 denPos k k D A
      (coarseGridNatWithWork_den _ _ 2).symm hdenLen le_rfl hkwidth
  have hav : allowance.value = k := coarseGridNatWithWork_value _ _ k
  have hpath : allowance.value.den ∣ (L * B * q) ^ 0 := by
    simp only [hav, Rat.den_natCast, one_dvd]
  have hc := (coarseBinaryEval_bitWork k q L N d D A frame two tree draws hB hq hL htwo
    htwocell.2.2.2.2 (by rw [htwoDen]; exact hd) htwoDen hBbits hqbits hLbits hNbits hbound
    0 (by omega) allowance start hacell hpath hstart).1
  apply coarseBinaryRead_width _ _ A (by omega)
  intro cells heq a ha
  exact ((hc cells heq).2 a ha).2.2.2.2

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

theorem computedCoarseRoot_for_candidate_oai :
    ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N → ∀ (hB : 0 < B) (hq : 0 < inputHeight N ^ 4)
      (hL : 0 < 64 * inputHeight N)
      (i : CoarseGuessIndex (coarseEntryWidth x y)) (draws : CoarseThresholdDraws B d),
      let k := coarseGuess (coarseEntryWidth x y) i
      let root := coarseRootWithWork k (inputHeight N ^ 4) (64 * inputHeight N) hB hq hL
        (coarseTargetFrame k (coarsePadTo (coarseEntryWidth x y) y))
        (coarseEntryTree B d x y) draws 0 (coarseRootShift k)
      root.1.width ≤ inputHeight N ^ 3 ∧
      root.2 ≤ inputHeight N ^ 30 * (2 * coarseActiveArrayWork k
        (initialThresholdQ N) (initialLambda N) (coarseEntryTree B d x y) draws k + 1) := by
  filter_upwards [computedCoarse_bitParameters, eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)] with N hbits hN hell
  intro B d x y hBdef hddef hsize hB hq hL i draws
  let H := inputHeight N
  let k := coarseGuess (coarseEntryWidth x y) i
  let frame := coarseTargetFrame k (coarsePadTo (coarseEntryWidth x y) y)
  let tree := coarseEntryTree B d x y
  let root := coarseRootWithWork k (H ^ 4) (64 * H) hB hq hL frame tree draws 0 (coarseRootShift k)
  have hH : 100 ≤ H := by
    exact (by decide : 100 ≤ 256).trans
      (computed_coarse_height_large N (by omega) hell)
  have hk : k ≤ 2 * (N + 2) :=
    (coarseGuess_le _ i).trans (by omega)
  obtain ⟨hden, hbound, hBbits, hqbits, hLbits, hNbits, hD⟩ :=
    hbits B d (coarseEntryWidth x y) k hBdef hddef hsize hk
  have hcap : coarseEntryWidth x y ≤ B ^ d := by
    rw [hBdef, hddef]
    exact (computed_coarse_depth N _ (by omega) hsize hell).1
  have htree : 0 + tree.word.length ≤ N := by
    dsimp only [tree]
    rw [coarseEntryTree_word B d x y hcap, coarsePadTo_length _ _ (le_max_left _ _)]
    simpa only [Nat.zero_add] using hsize
  have hdepth : d ≤ H := hddef.symm ▸ (computed_coarse_depth N _ (by omega) hsize hell).2
  have hrw : root.1.width ≤ H ^ 3 :=
    coarseRootWithWork_width k (H ^ 4) (64 * H) N (10 * H ^ 2) (H ^ 3)
      hB hq hL frame tree draws 0 (coarseRootShift k)
      hBbits hqbits hLbits hNbits hden hbound htree
  have hrc := coarseRootWithWork_height_bound k (H ^ 4) (64 * H) N (10 * H ^ 2) H
    hB hq hL frame tree draws 0 (coarseRootShift k)
    hBbits hqbits hLbits hNbits hden hD hdepth hbound htree
  have hrc' : root.2 ≤ H ^ 30 *
      (2 * coarseActiveArrayWork k (initialThresholdQ N) (initialLambda N) tree draws k + 1) := by
    have hc := hrc.trans (Nat.mul_le_mul_right _ (coarseNumericalUnit_le_power H (by omega)))
    simpa only [initialThresholdQ, initialLambda, H, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using hc
  exact ⟨hrw, hrc'⟩

end BinaryFraction
end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.BinaryFraction.computedCoarseRoot_for_candidate_oai := @OAI.EditApproximation.BinaryFraction.computedCoarseRoot_for_candidate_oai
