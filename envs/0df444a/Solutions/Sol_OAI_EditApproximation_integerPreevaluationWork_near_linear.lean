-- Prove2me | solution 1 for OAI.EditApproximation.integerPreevaluationWork_near_linear
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:22:26.16379+00:00
-- url     : https://prove2.me/submissions/5733974d-b13a-4360-b9dc-72b25dc29209

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Nat
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea002
import Definitions.Def_OAIQ361V3Ea003

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
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
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



end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryMemo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A finite binary dictionary for gathered and globally memoized inputs.
Each recursive step reads one key bit and touches one node. The explicit
counters charge pointer/node operations; multiword key/value processing
is accounted for separately by their bit lengths. -/

namespace EditApproximation



namespace BinaryMemo

variable {α : Type*}











/-- Persistent insertion allocates one new node at each visited level;
the two untouched subtrees are retained by pointer. -/


theorem insertCosted_spec (tree : BinaryMemo α) (key : List Bool) (a : α) :
    tree.insertCosted key a = (tree.insert key a, key.length + 1) := by
  induction key generalizing tree with
  | nil => rfl
  | cons b rest ih => cases b <;> simp only [insertCosted, insert, ih, List.length_cons]

end BinaryMemo

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerSymbols
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Integer word labels are encoded injectively using a sign bit. The
encoding preserves the actual unit-cost edit distance and takes one
linear pass; no constant-alphabet hypothesis is used. -/

namespace EditApproximation



theorem encodeIntegerSymbolsWithWork_spec (symbols : List ℤ) :
    encodeIntegerSymbolsWithWork symbols = (symbols.map integerSymbolCode, 3 * symbols.length) := by
  induction symbols with
  | nil => rfl
  | cons z zs ih =>
    simp only [encodeIntegerSymbolsWithWork, ih, List.map_cons, List.length_cons]
    congr 1

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_OccurrencePrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Cached binary position counts. Inserting a position and counting positions
strictly below a boundary both follow one root-to-leaf path. Counts are stored
at internal nodes, so a prefixCount query does not traverse a whole interval. -/

namespace EditApproximation



namespace PositionCounts









theorem addWithWork_spec (tree : PositionCounts) (d i : ℕ) :
    tree.addWithWork d i = (tree.add d i, 2 * d + 1) := by
  induction d generalizing tree i with
  | zero => rfl
  | succ d ih =>
    simp only [addWithWork, add]
    split_ifs <;> rw [ih] <;> simp only <;> congr 1



end PositionCounts

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_OccurrenceIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A symbol dictionary of cached position tries. The target is enumerated
once; interval occurrence queries use two logarithmic prefix counts. -/

namespace EditApproximation



theorem occurrenceBuildWithWork_spec (symbolBits positionBits : ℕ) (entries : List (ℕ × ℕ)) :
    occurrenceBuildWithWork symbolBits positionBits entries =
      (occurrenceBuild symbolBits positionBits entries,
        entries.length * (3 * symbolBits + 2 * positionBits + 5)) := by
  induction entries with
  | nil => simp only [occurrenceBuildWithWork, occurrenceBuild, List.length_nil, zero_mul]
  | cons e es ih =>
    simp only [occurrenceBuildWithWork, ih, BinaryMemo.lookupCosted_spec,
      PositionCounts.addWithWork_spec, BinaryMemo.insertCosted_spec,
      binaryMemoKey_length, occurrenceBuild, List.length_cons]
    congr 1
    ring



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerOccurrenceIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Uniform input preparation chooses dictionary widths from the actual
integer words. No alphabet size or polynomial exponent is an algorithm input. -/

namespace EditApproximation



theorem integerMagnitude_le (zs : List ℤ) (B : ℕ) (h : ∀ z ∈ zs, z.natAbs ≤ B) :
    integerMagnitude zs ≤ B := by
  induction zs with
  | nil => exact Nat.zero_le _
  | cons z zs ih =>
    exact max_le (h z List.mem_cons_self) (ih fun a ha => h a (List.mem_cons_of_mem _ ha))





theorem integerInputSymbolBits_le (source target : List ℤ) (B : ℕ)
    (h : ∀ z ∈ source ++ target, z.natAbs ≤ B) :
    integerInputSymbolBits source target ≤ Nat.size (2 * B) :=
  Nat.size_le_size (Nat.mul_le_mul_left 2 (integerMagnitude_le _ B h))



theorem integerOccurrenceBuildWithWork_spec (source target : List ℤ) :
    integerOccurrenceBuildWithWork source target =
      (integerOccurrenceIndex source target,
        target.length * (3 * integerInputSymbolBits source target +
          2 * integerInputPositionBits target + 5)) := by
  rw [integerOccurrenceBuildWithWork, occurrenceBuildWithWork_spec]
  simp only [List.length_zipIdx, List.length_map, integerOccurrenceIndex]

/-- Polynomially bounded input words produce logarithmic dictionary keys;
the polynomial degree is only an analysis parameter. -/
theorem integerInputSymbolBits_polynomial (source target : List ℤ) (N C : ℕ)
    (h : ∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) :
    integerInputSymbolBits source target ≤ C * Nat.size (N + 2) + 3 := by
  have hbits := integerInputSymbolBits_le source target ((N + 2) ^ C) h
  have hmul := natural_product_bit_length 2 ((N + 2) ^ C)
  have hpow := natural_power_bit_length (N + 2) C
  have htwo : Nat.size 2 = 2 := by decide
  omega

theorem integerOccurrenceBuildWithWork_polynomial (source target : List ℤ) (N C : ℕ)
    (hsize : source.length + target.length ≤ N)
    (h : ∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) :
    (integerOccurrenceBuildWithWork source target).2 ≤
      N * ((3 * C + 2) * Nat.size (N + 2) + 14) := by
  rw [integerOccurrenceBuildWithWork_spec]
  dsimp only
  have hs := integerInputSymbolBits_polynomial source target N C h
  have hp : integerInputPositionBits target ≤ Nat.size (N + 2) :=
    Nat.size_le_size (by omega)
  apply Nat.mul_le_mul (by omega)
  nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_ExactSuffixDPWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A costed implementation of the exact cut dynamic program. The counter
counts symbol comparisons and list-cell visits, with explicit outer-loop
overhead. Each counted transition uses a fixed number of word operations;
the surrounding RAM realization supplies that constant. Suffix lookups and
occurrence scans are charged rather than treated as constant-time arrays. -/

namespace EditApproximation











theorem dpLength_spec {α : Type*} (word : List α) :
    (dpLength word).1 = word.length ∧ (dpLength word).2 = word.length + 1 := by
  induction word with
  | nil => exact ⟨rfl, rfl⟩
  | cons first rest ih =>
    constructor <;> simp only [dpLength, List.length_cons, ih.1, ih.2]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerInputInspection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Explicit linear scans select the input-dependent symbol and position
widths. The alphabet exponent is used only in the analysis. -/

namespace EditApproximation



 theorem integerMagnitudeWithWork_spec (symbols : List ℤ) :
    integerMagnitudeWithWork symbols = (integerMagnitude symbols, 2 * symbols.length) := by
  induction symbols with
  | nil => rfl
  | cons z rest ih =>
    simp only [integerMagnitudeWithWork, ih, integerMagnitude, List.length_cons]
    congr 1

 theorem integerMagnitude_append (source target : List ℤ) :
    integerMagnitude (source ++ target) = max (integerMagnitude source) (integerMagnitude target) := by
  induction source with
  | nil => simp only [List.nil_append, integerMagnitude, Nat.zero_max]
  | cons z rest ih => simp only [List.cons_append, integerMagnitude, ih, max_assoc]

/-- Count the shifts in a literal binary-length loop. -/


private theorem size_div_two (n : ℕ) (hn : n ≠ 0) : n.size = (n / 2).size + 1 := by
  have hb : Nat.bit n.bodd n.div2 ≠ 0 := by rwa [Nat.bit_bodd_div2]
  have hs := Nat.size_bit hb
  rw [Nat.bit_bodd_div2] at hs
  simpa only [Nat.div2_val, Nat.succ_eq_add_one] using hs

 theorem inputBitLengthWithWork_spec (n : ℕ) :
    inputBitLengthWithWork n = (n.size, 2 * n.size + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [inputBitLengthWithWork]
    split_ifs with hn
    · subst n
      rfl
    · rw [ih (n / 2) (Nat.div_lt_self (by omega) (by decide)), size_div_two n hn]
      congr 1



 theorem integerInputInspectionWithWork_cost (source target : List ℤ) :
    (integerInputInspectionWithWork source target).2 ≤
      4 * (source.length + target.length) + 2 * integerInputSymbolBits source target +
        2 * integerInputPositionBits target + 8 := by
  simp only [integerInputInspectionWithWork, integerMagnitudeWithWork_spec,
    dpLength_spec, inputBitLengthWithWork_spec, integerInputSymbolBits,
    integerInputPositionBits, integerMagnitude_append]
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedEarlierInputBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual earlier-input cover satisfies the polynomial branching
budget at every seed, after substituting the computed time and grid
parameters. -/

namespace EditApproximation

theorem computed_smallLog_le_height (N : ℕ) : inputSmallLog N ≤ inputHeight N := by
  have hf : smallLogExponent N ≤ heightExponent N := by
    unfold smallLogExponent
    apply Nat.clog_le_of_le_pow
    exact max_le Nat.one_le_two_pow (heightExponent N).lt_two_pow_self.le
  exact pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) hf

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
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
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
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
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

theorem inputHeight_real_tendsto :
    Tendsto (fun N => (inputHeight N : ℝ)) atTop atTop := by
  simpa only [inputHeight, Nat.cast_pow, Nat.cast_ofNat, Function.comp_def] using
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp heightExponent_tendsto

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

theorem height_log_sandwich (N : ℕ) (hN : 0 < N) :
    Real.log (N + 2 : ℝ) / Real.log 2 ≤ inputHeight N ∧
      (inputHeight N : ℝ) ≤ (4 / Real.log 2) * Real.log (N + 2 : ℝ) := by
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcover : (N + 2 : ℝ) ≤ (2 : ℝ) ^ inputHeight N := by
    exact_mod_cast inputHeight_covers_length N
  have hlower := Real.log_le_log (by positivity : (0 : ℝ) < N + 2) hcover
  rw [Real.log_pow] at hlower
  have hL : 1 < Nat.clog 2 (N + 2) := by
    exact (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 (by norm_num; omega)
  have hpred := Nat.pow_pred_clog_lt_self (by decide : 1 < (2 : ℕ))
    (by omega : 1 < N + 2)
  have hpredR : (2 : ℝ) ^ (Nat.clog 2 (N + 2)).pred < N + 2 := by exact_mod_cast hpred
  have hpredlog := Real.log_lt_log (by positivity : (0 : ℝ) < 2 ^ (Nat.clog 2 (N + 2)).pred) hpredR
  rw [Real.log_pow] at hpredlog
  have hpredcast : ((Nat.clog 2 (N + 2)).pred : ℝ) = (Nat.clog 2 (N + 2) : ℝ) - 1 := by
    have hnat : (Nat.clog 2 (N + 2)).pred + 1 = Nat.clog 2 (N + 2) :=
      Nat.succ_pred_eq_of_pos (by omega)
    have hcast : ((Nat.clog 2 (N + 2)).pred : ℝ) + 1 = (Nat.clog 2 (N + 2) : ℝ) := by
      exact_mod_cast hnat
    linarith
  rw [hpredcast] at hpredlog
  have hH : (inputHeight N : ℝ) < 2 * (Nat.clog 2 (N + 2) : ℝ) := by
    have h := (rejectionWord_range (Nat.clog 2 (N + 2)) (by omega)).2
    simpa only [inputHeight, heightExponent, rejectionBitCount, Nat.cast_pow,
      Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_lt.mpr h :
      ((2 ^ rejectionBitCount (Nat.clog 2 (N + 2)) : ℕ) : ℝ) <
        ((2 * Nat.clog 2 (N + 2) : ℕ) : ℝ))
  have hlogN : Real.log 2 ≤ Real.log (N + 2 : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ N + 2))
  constructor
  · exact (div_le_iff₀ hlogtwo).2 hlower
  · have hproduct : (inputHeight N : ℝ) * Real.log 2 ≤ 4 * Real.log (N + 2 : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right hH.le hlogtwo.le
      nlinarith
    calc
      (inputHeight N : ℝ) ≤ (4 * Real.log (N + 2 : ℝ)) / Real.log 2 :=
        (le_div_iff₀ hlogtwo).2 hproduct
      _ = (4 / Real.log 2) * Real.log (N + 2 : ℝ) := by ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SubexponentialTransfer
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conversion from the computed-height bounds to asymptotics in the actual
input length. The bounds concern scalar envelopes, not an uncharged program. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem subexponential_height_to_input (f : ℕ → ℝ)
    (hf : Tendsto (fun N => f N / inputHeight N) atTop (𝓝 0))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, Real.exp (f N) ≤ (N + 2 : ℝ) ^ epsilon := by
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall := hf.eventually (gt_mem_nhds
    (show (0 : ℝ) < epsilon * Real.log 2 / 4 by positivity))
  filter_upwards [hsmall, eventually_ge_atTop 1] with N hsmall hN
  have hH : (0 : ℝ) < inputHeight N := by exact_mod_cast Nat.two_pow_pos (heightExponent N)
  have hfN : f N ≤ (epsilon * Real.log 2 / 4) * inputHeight N :=
    ((div_lt_iff₀ hH).1 hsmall).le
  have hheight := (height_log_sandwich N hN).2
  have hscaled := mul_le_mul_of_nonneg_left hheight
    (show (0 : ℝ) ≤ epsilon * Real.log 2 / 4 by positivity)
  have hcancel : (epsilon * Real.log 2 / 4) *
      ((4 / Real.log 2) * Real.log (N + 2 : ℝ)) = epsilon * Real.log (N + 2 : ℝ) := by
    field_simp [hlogtwo.ne']
  have hexponent : f N ≤ epsilon * Real.log (N + 2 : ℝ) :=
    hfN.trans (hscaled.trans_eq hcancel)
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < N + 2)]
  apply Real.exp_le_exp.mpr
  simpa only [mul_comm] using hexponent

theorem sublinear_height_near_linear (f : ℕ → ℝ)
    (hf : Tendsto (fun N => f N / inputHeight N) atTop (𝓝 0))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ (N : ℕ) in atTop, (N + 2 : ℝ) * Real.exp (f N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [subexponential_height_to_input f hf epsilon hepsilon] with N hN
  rw [Real.rpow_add (by positivity : (0 : ℝ) < N + 2), Real.rpow_one]
  exact mul_le_mul_of_nonneg_left hN (by positivity)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_DependencyPathEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit subpolynomial envelope for the finite dependency-path sum.
The connection between this sum and an execution is a separate obligation. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem nat_pow_eq_exp_log (a n : ℕ) (ha : 0 < a) :
    (a : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log a) := by
  rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast ha)]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedNumericalParameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All-seed numerical dimension and source-range bounds after substituting
the computed grid size. These bounds do not use an accuracy event. -/

namespace EditApproximation

theorem wide_coordinate_budget_le (H M P p : ℕ) (hH : 64 ≤ H) (hM : M ≤ H)
    (hP : 1 ≤ P) (hPcap : P ≤ H ^ (p + 20)) :
    M * (40 * P + 2) ^ 2 ≤ H ^ (2 * p + 45) := by
  have hbox : 40 * P + 2 ≤ H ^ (p + 22) := by
    have hconstant : 42 ≤ H ^ 2 := by nlinarith
    calc
      _ ≤ 42 * P := by omega
      _ ≤ H ^ 2 * H ^ (p + 20) := Nat.mul_le_mul hconstant hPcap
      _ = H ^ (2 + (p + 20)) := (pow_add H 2 (p + 20)).symm
      _ = _ := by congr 1; omega
  calc
    _ ≤ H * (H ^ (p + 22)) ^ 2 := Nat.mul_le_mul hM (Nat.pow_le_pow_left hbox 2)
    _ = H * H ^ ((p + 22) * 2) := by rw [pow_mul]
    _ = H ^ ((p + 22) * 2 + 1) := (pow_succ' H _).symm
    _ = _ := by congr 1; omega

theorem optimizer_parameter_budget_le (H M P p : ℕ) (hH : 64 ≤ H) (hM : M ≤ H)
    (hP : 1 ≤ P) (hPcap : P ≤ H ^ (p + 20)) :
    H + M * (40 * P + 2) ^ 2 + 4 ≤ H ^ (2 * p + 46) := by
  have hdimension := wide_coordinate_budget_le H M P p hH hM hP hPcap
  have hlarge : H ≤ H ^ (2 * p + 45) := Nat.le_pow (by omega)
  have hfour : 4 ≤ H ^ (2 * p + 45) := (by omega : 4 ≤ H).trans hlarge
  calc
    _ ≤ 3 * H ^ (2 * p + 45) := by omega
    _ ≤ H * H ^ (2 * p + 45) := Nat.mul_le_mul_right _ (by omega)
    _ = H ^ (2 * p + 45 + 1) := (pow_succ' H _).symm
    _ = _ := rfl

theorem optimizerTriangularMass_le_square (K : ℕ) : optimizerTriangularMass K ≤ K ^ 2 := by
  have htwice := optimizerTriangularMass_twice K
  have hpower : K ≤ K ^ 2 := Nat.le_pow (by decide)
  nlinarith only [htwice, hpower]

theorem localOnlineMassBound_polynomial (H M P p : ℕ) (hH : 64 ≤ H) (hM : M ≤ H)
    (hP : 1 ≤ P) (hPcap : P ≤ H ^ (p + 20)) :
    localOnlineMassBound M P H ≤ H ^ (8000 * (p + 1)) := by
  have hG : H + M * (40 * P + 2) ^ 2 + 2 ≤ H ^ (2 * p + 46) :=
    (by omega : H + M * (40 * P + 2) ^ 2 + 2 ≤ H + M * (40 * P + 2) ^ 2 + 4).trans
      (optimizer_parameter_budget_le H M P p hH hM hP hPcap)
  calc
    _ ≤ ((H + M * (40 * P + 2) ^ 2 + 2) ^ 80) ^ 2 := optimizerTriangularMass_le_square _
    _ = (H + M * (40 * P + 2) ^ 2 + 2) ^ (80 * 2) := (pow_mul _ 80 2).symm
    _ ≤ (H ^ (2 * p + 46)) ^ (80 * 2) := Nat.pow_le_pow_left hG _
    _ = H ^ ((2 * p + 46) * (80 * 2)) := (pow_mul H _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

theorem computed_localOnlineMassBound_polynomial (N : ℕ) (hH : 64 ≤ inputHeight N) :
    localOnlineMassBound (integerParameters N).M (integerParameters N).P (inputHeight N) ≤
      inputHeight N ^ (8000 * (coarseExponent (inputSmallLog N) + 1)) := by
  apply localOnlineMassBound_polynomial _ _ _ _ hH
  · exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.div_le_self _ _)
  · exact Nat.one_le_pow _ _ (by omega)
  · exact le_rfl

theorem computed_localOnlineMassBound_bits (N : ℕ) (hH : 64 ≤ inputHeight N) :
    Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P (inputHeight N)) ≤
      8000 * (coarseExponent (inputSmallLog N) + 1) * Nat.size (inputHeight N) + 1 :=
  (Nat.size_le_size (computed_localOnlineMassBound_polynomial N hH)).trans
    (natural_power_bit_length _ _)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerPreprocessing
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open Filter
open scoped Topology



 theorem integerEqualWithWork_spec (source target : List ℤ) :
    (integerEqualWithWork source target).1 = decide (source = target) ∧
      (integerEqualWithWork source target).2 ≤ source.length + target.length + 1 := by
  induction source generalizing target with
  | nil => cases target <;> simp [integerEqualWithWork]
  | cons x xs ih =>
    cases target with
    | nil => simp [integerEqualWithWork]
    | cons y ys =>
      by_cases hxy : x = y
      · subst y
        have h := ih ys
        constructor
        · simpa [integerEqualWithWork] using h.1
        · simpa [integerEqualWithWork, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (show (integerEqualWithWork xs ys).2 + 1 ≤ xs.length + ys.length + 3 by omega)
      · simp [integerEqualWithWork, hxy]

/-- Scans, integer encoding, indexed occurrence preprocessing and the
exact equality guard are charged before the local evaluator starts. -/


 theorem input_length_bits_le (N : ℕ) : Nat.size (N + 2) ≤ inputHeight N + 1 := by
  apply Nat.size_le.mpr
  exact (inputHeight_covers_length N).trans_lt
    (Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self _))

private theorem preprocessing_scalar_bound (N H C L s p : ℕ)
    (hH : 8 ≤ H) (hC : C ≤ H) (hL : L ≤ H + 1)
    (hs : s ≤ C * L + 3) (hp : p ≤ L) :
    4 * N + 2 * s + 2 * p + 8 + 3 * N + N * ((3 * C + 2) * L + 14) + (N + 1) + 1 ≤
      (N + 2) * H ^ 4 := by
  have hCL := Nat.mul_le_mul hC hL
  have hs' : s ≤ 3 * H ^ 2 := by nlinarith only [hs, hCL, hH]
  have hp' : p ≤ H + 1 := hp.trans hL
  have hcoef0 := Nat.mul_le_mul (by omega : 3 * C + 2 ≤ 3 * H + 2) hL
  have hcoef : (3 * C + 2) * L + 22 ≤ 10 * H ^ 2 := by
    nlinarith only [hcoef0, hH]
  have hcN := Nat.mul_le_mul_left N hcoef
  have hsquare : 10 * H ^ 2 ≤ H ^ 4 := by
    have hh : 10 ≤ H ^ 2 := by nlinarith only [hH]
    have hm := Nat.mul_le_mul_right (H ^ 2) hh
    nlinarith only [hm]
  have hm := Nat.mul_le_mul_left (N + 2) hsquare
  nlinarith only [hs', hp', hcN, hm, hH]

 theorem integerPreprocessingWork_le (source target : List ℤ) (N C : ℕ)
    (hsize : source.length + target.length ≤ N)
    (halphabet : ∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C)
    (hH : 8 ≤ inputHeight N) (hC : C ≤ inputHeight N) :
    integerPreprocessingWork source target ≤ (N + 2) * inputHeight N ^ 4 := by
  have hi := integerInputInspectionWithWork_cost source target
  have heq := (integerEqualWithWork_spec source target).2
  have hoc := integerOccurrenceBuildWithWork_polynomial source target N C hsize halphabet
  have hs := integerInputSymbolBits_polynomial source target N C halphabet
  have hp : integerInputPositionBits target ≤ Nat.size (N + 2) := Nat.size_le_size (by omega)
  have hscalar := preprocessing_scalar_bound N (inputHeight N) C (Nat.size (N + 2))
    (integerInputSymbolBits source target) (integerInputPositionBits target) hH hC
    (input_length_bits_le N) hs hp
  unfold integerPreprocessingWork
  rw [encodeIntegerSymbolsWithWork_spec, encodeIntegerSymbolsWithWork_spec]
  dsimp only
  omega

 theorem fixed_height_power_near_linear (C : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, (N + 2 : ℝ) * (inputHeight N : ℝ) ^ C ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (inputHeight N : ℝ) / inputHeight N)
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp inputHeight_real_tendsto
  have hlimit := hlog.const_mul (C : ℝ)
  simp only [mul_zero] at hlimit
  have hf : Tendsto (fun N => ((C : ℝ) * Real.log (inputHeight N : ℝ)) / inputHeight N)
      atTop (𝓝 0) := by convert hlimit using 1 <;> first | (with_reducible_and_instances rfl) | (ext N; ring)
  filter_upwards [sublinear_height_near_linear _ hf epsilon hepsilon] with N hN
  rwa [← nat_pow_eq_exp_log (inputHeight N) C (Nat.two_pow_pos _)] at hN

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_AccuracyPrefixInspection
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The uniform program inspects only a logarithmically bounded prefix
of each accuracy word. An encoding exceeding this bound takes the exact
fallback, without first scanning or retaining its unbounded suffix. -/

namespace EditApproximation

/-- One step reads a constructor of the input word. -/


 theorem inspectBitPrefix_accepts (budget : ℕ) (word : List Bool) :
    (inspectBitPrefix budget word).1 = true ↔ word.length ≤ budget := by
  induction budget generalizing word with
  | zero => cases word <;> simp [inspectBitPrefix]
  | succ budget ih =>
    cases word with
    | nil => simp [inspectBitPrefix]
    | cons bit rest => simpa only [inspectBitPrefix, List.length_cons, Nat.add_le_add_iff_right] using ih rest

 theorem inspectBitPrefix_cost (budget : ℕ) (word : List Bool) :
    (inspectBitPrefix budget word).2 ≤ budget + 1 := by
  induction budget generalizing word with
  | zero => cases word <;> exact le_rfl
  | succ budget ih =>
    cases word with
    | nil => exact Nat.succ_le_succ (Nat.zero_le _)
    | cons bit rest => exact Nat.add_le_add_right (ih rest) 1

/-- On acceptance the input words are already bounded; returning the
input value only retains those bounded words. -/


 theorem inspectAccuracyWithWork_spec (budget : ℕ) (epsilon : BinaryFraction) :
    (inspectAccuracyWithWork budget epsilon).1 =
      if epsilon.width ≤ budget then some epsilon else none := by
  simp only [inspectAccuracyWithWork, BinaryFraction.width, max_le_iff]
  by_cases hn : epsilon.numerator.bits.length ≤ budget <;>
    by_cases hd : epsilon.denominator.length ≤ budget
  all_goals
    have hnum := inspectBitPrefix_accepts budget epsilon.numerator.bits
    have hden := inspectBitPrefix_accepts budget epsilon.denominator
    simp_all

 theorem inspectAccuracyWithWork_cost (budget : ℕ) (epsilon : BinaryFraction) :
    (inspectAccuracyWithWork budget epsilon).2 ≤ 2 * budget + 4 := by
  have hn := inspectBitPrefix_cost budget epsilon.numerator.bits
  have hd := inspectBitPrefix_cost budget epsilon.denominator
  change (inspectBitPrefix budget epsilon.numerator.bits).2 +
    (inspectBitPrefix budget epsilon.denominator).2 + 2 ≤ _
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedSourceAddressBits
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability
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

theorem computed_localOnlineMassBound_word :
    ∀ᶠ N in atTop,
      Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P (inputHeight N)) ≤
        inputHeight N := by
  filter_upwards [computed_sourceAddressBits_le_height 8000,
    inputHeight_real_tendsto.eventually (eventually_ge_atTop 64)] with N hbits hH
  have hHnat : 64 ≤ inputHeight N := by exact_mod_cast hH
  exact (computed_localOnlineMassBound_bits N hHnat).trans hbits

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterConstruction
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Counted register loops for the global integer parameters. Multiplication
and division here are word operations; the word-cap theorem below supplies
room for their intermediate integers. -/
namespace EditApproximation
open Filter

 theorem size_pred_eq_clog_two (n : ℕ) : (n - 1).size = Nat.clog 2 n := by
  apply eq_of_forall_ge_iff
  intro k
  rw [Nat.size_le, Nat.clog_le_iff_le_pow (by decide)]
  have hp := Nat.two_pow_pos k
  omega

 theorem size_pred_eq_log_two (n : ℕ) : n.size - 1 = Nat.log 2 n := by
  by_cases hn : n = 0
  · subst n; simp
  apply eq_of_forall_le_iff
  intro k
  have hs : 0 < n.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [Nat.le_log_iff_pow_le (by decide) hn]
  have hk := Nat.lt_size (m := k) (n := n)
  omega



 @[simp] theorem parameterClogWithWork_spec (n : ℕ) :
    parameterClogWithWork n = (Nat.clog 2 n, 2 * Nat.clog 2 n + 3) := by
  simp only [parameterClogWithWork, inputBitLengthWithWork_spec, size_pred_eq_clog_two]



 @[simp] theorem parameterLogWithWork_value (n : ℕ) :
    (parameterLogWithWork n).1 = Nat.log 2 n := by
  simp only [parameterLogWithWork, inputBitLengthWithWork_spec, size_pred_eq_log_two]

 theorem parameterLogWithWork_cost (n : ℕ) :
    (parameterLogWithWork n).2 = 2 * n.size + 2 := by
  simp only [parameterLogWithWork, inputBitLengthWithWork_spec]



 theorem parameterRootSearch_value (n k : ℕ) (hk : n.sqrt ≤ k) :
    (parameterRootSearch n k).1 = n.sqrt := by
  induction k with
  | zero => simp only [parameterRootSearch]; omega
  | succ k ih =>
    rw [parameterRootSearch]
    split_ifs with h
    · have := Nat.le_sqrt.mpr h
      dsimp only
      omega
    · have hk' : n.sqrt ≤ k := by
        have := Nat.le_sqrt.not.mpr h
        omega
      exact ih hk'

 theorem parameterRootSearch_cost (n k : ℕ) :
    (parameterRootSearch n k).2 ≤ 3 * k + 1 := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [parameterRootSearch]
    split_ifs <;> dsimp only <;> omega



 @[simp] theorem parameterSqrtWithWork_value (n : ℕ) :
    (parameterSqrtWithWork n).1 = n.sqrt :=
  parameterRootSearch_value n n (Nat.sqrt_le_self n)

 theorem parameterSqrtWithWork_cost (n : ℕ) :
    (parameterSqrtWithWork n).2 ≤ 3 * n + 1 := parameterRootSearch_cost n n



 @[simp] theorem integerParametersWithWork_value (N : ℕ) :
    (integerParametersWithWork N).1 = integerParameters N := by
  simp only [integerParametersWithWork, parameterClogWithWork_spec, parameterPowerWithWork_spec,
    parameterLogWithWork_value, parameterSqrtWithWork_value, integerParameters,
    heightExponent, inputHeight, smallLogExponent, inputSmallLog, coarseExponent]

 theorem integerParametersWithWork_cost (N : ℕ) :
    (integerParametersWithWork N).2 ≤ 1000 * (inputHeight N + 1) := by
  have hfirst : Nat.clog 2 (N + 2) ≤ inputHeight N :=
    Nat.clog_le_of_le_pow (inputHeight_covers_length N)
  have he : heightExponent N ≤ inputHeight N := Nat.lt_two_pow_self.le
  have hs : smallLogExponent N ≤ inputHeight N :=
    (Nat.lt_two_pow_self.le : smallLogExponent N ≤ inputSmallLog N).trans
      (computed_smallLog_le_height N)
  have hp : coarseExponent (inputSmallLog N) ≤ inputHeight N :=
    (coarseExponent_le_smallLog N).trans (computed_smallLog_le_height N)
  have hl : Nat.log 2 (inputSmallLog N) ≤ inputHeight N :=
    (Nat.log_le_self _ _).trans (computed_smallLog_le_height N)
  have hr : (Nat.log 2 (inputSmallLog N)).sqrt ≤ inputHeight N :=
    (Nat.sqrt_le_self _).trans hl
  have hlogsize : (inputSmallLog N).size ≤ inputHeight N + 1 := by
    change (2 ^ smallLogExponent N).size ≤ _
    rw [Nat.size_pow]
    omega
  have hroot := parameterSqrtWithWork_cost (Nat.log 2 (inputSmallLog N))
  have hroot2 := parameterSqrtWithWork_cost ((Nat.log 2 (inputSmallLog N)).sqrt)
  have hlogcost := parameterLogWithWork_cost (inputSmallLog N)
  simp only [integerParametersWithWork, parameterClogWithWork_spec, parameterPowerWithWork_spec,
    parameterLogWithWork_value, parameterSqrtWithWork_value]
  change 2 * Nat.clog 2 (N + 2) + 3 + (2 * heightExponent N + 3) + (2 * heightExponent N + 1) +
    (2 * smallLogExponent N + 3) + (2 * smallLogExponent N + 1) +
    (parameterLogWithWork (inputSmallLog N)).2 +
    (parameterSqrtWithWork (Nat.log 2 (inputSmallLog N))).2 +
    (parameterSqrtWithWork ((Nat.log 2 (inputSmallLog N)).sqrt)).2 +
    (2 * (heightExponent N / 20) + 1) + (2 * coarseExponent (inputSmallLog N) + 1) +
    (2 * (coarseExponent (inputSmallLog N) + 4) + 1) +
    (2 * (coarseExponent (inputSmallLog N) + 20) + 1) +
    (2 * ((3 * heightExponent N + 3) / 4) + 1) + (2 * 2 + 1) + 15 ≤ _
  have hdiv := Nat.div_le_self (heightExponent N) 20
  have hdiv' := Nat.div_le_self (3 * heightExponent N + 3) 4
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterNumericalConstruction
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation



 theorem rationalParametersWithWork_cost (ell : ℕ) :
    (rationalParametersWithWork ell).2 = 183 := by
  simp only [rationalParametersWithWork, parameterPowerWithWork_spec]



 theorem onlineMassWithWork_cost (M P H : ℕ) :
    (onlineMassWithWork M P H).2 = 175 := by
  simp only [onlineMassWithWork, parameterPowerWithWork_spec]



 theorem globalParameterWork_le (N : ℕ) :
    globalParameterWork N ≤ 2000 * (inputHeight N + 1) := by
  have h := integerParametersWithWork_cost N
  simp only [globalParameterWork, rationalParametersWithWork_cost, onlineMassWithWork_cost]
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalInputGuard
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

 theorem physicalLargeInputWithWork_cost (N : ℕ) (epsilon : BinaryFraction)
    (hmass : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N) :
    (physicalLargeInputWithWork N epsilon).2 ≤ 100000 * (inputHeight N + 1005) ^ 2 := by
  let B := (inputHeight N) + 1005
  have hi := inspectAccuracyWithWork_cost (inputHeight N) epsilon
  by_cases haccepted : (inspectAccuracyWithWork (inputHeight N) epsilon).1.isSome = true
  · have hepsilon : epsilon.width ≤ (inputHeight N) := by
      rw [inspectAccuracyWithWork_spec] at haccepted
      split_ifs at haccepted with he
      · exact he
      · cases haccepted
    have hell : Nat.size (inputSmallLog N) + 2 ≤ B := by
      have hs := Nat.size_le_size (computed_smallLog_le_height N)
      have hh : Nat.size (inputHeight N) ≤ (inputHeight N) + 1 := by
        apply Nat.size_le.mpr
        exact Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ (inputHeight N)))
      dsimp only [B]
      omega
    have hleft : (BinaryFraction.nat (inputSmallLog N)).width ≤ B :=
      (BinaryFraction.nat_width_le _).trans hell
    have hright : epsilon.width ≤ B := hepsilon.trans (by dsimp [B]; omega)
    have hten : (BinaryFraction.nat 10).width ≤ 4 * B + 2 := by
      have ht := BinaryFraction.nat_width_le 10
      rw [show Nat.size 10 = 4 from by decide] at ht
      dsimp only [B]
      omega
    have hp := BinaryFraction.canonicalMulWithWork_cost
      (BinaryFraction.nat (inputSmallLog N)) epsilon B hleft hright
    have hpw := BinaryFraction.canonicalMulWithWork_width
      (BinaryFraction.nat (inputSmallLog N)) epsilon B hleft hright
    have ha := BinaryFraction.ltWithWork_cost
      (BinaryFraction.canonicalMulWithWork (BinaryFraction.nat (inputSmallLog N)) epsilon).1
      (BinaryFraction.nat 10) (4 * B + 2) hpw hten
    have ht := binaryNaturalCompareWithWork_cost (inputSmallLog N) (2 ^ 1000)
    have hc := binaryNaturalCompareWithWork_cost (inputHeight N)
      (Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P (inputHeight N)))
    have hHsize : Nat.size (inputHeight N) ≤ (inputHeight N) + 1 := by
      apply Nat.size_le.mpr
      exact Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ (inputHeight N)))
    have hmsize : Nat.size (Nat.size (localOnlineMassBound (integerParameters N).M
        (integerParameters N).P (inputHeight N))) ≤ (inputHeight N) + 1 := (Nat.size_le_size hmass).trans hHsize
    simp only [Nat.size_pow] at ht
    simp only [physicalLargeInputWithWork, haccepted, ite_true, if_true, inputBitLengthWithWork_spec,
      onlineMassWithWork_value, onlineMassWithWork_cost]
    change _ ≤ 100000 * B ^ 2
    dsimp only [B] at hp ha hell ⊢
    nlinarith only [hp, ha, ht, hi, hc, hHsize, hmsize, hmass, hell]
  · simp only [physicalLargeInputWithWork, haccepted, Bool.false_eq_true, ite_false, if_false]
    nlinarith only [hi, Nat.zero_le (inputHeight N)]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedPreevaluation
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open Filter

private theorem guard_scalar (H : ℕ) (hH : 1000000 ≤ H) :
    100000 * (H + 1005) ^ 2 ≤ H ^ 4 := by
  have hplus : H + 1005 ≤ 2 * H := by omega
  have hp := Nat.mul_le_mul_left 100000 (Nat.pow_le_pow_left hplus 2)
  have hcoef : 400000 ≤ H ^ 2 := by nlinarith only [hH]
  have hm := Nat.mul_le_mul_right (H ^ 2) hcoef
  calc
    _ ≤ 100000 * (2 * H) ^ 2 := hp
    _ = 400000 * H ^ 2 := by ring
    _ ≤ H ^ 2 * H ^ 2 := hm
    _ = _ := by ring

 theorem physicalLargeInputWithWork_le_height (N : ℕ) (epsilon : BinaryFraction)
    (hH : 1000000 ≤ inputHeight N)
    (hmass : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N) :
    (physicalLargeInputWithWork N epsilon).2 ≤ inputHeight N ^ 4 :=
  (physicalLargeInputWithWork_cost N epsilon hmass).trans (guard_scalar _ hH)

/-- All input scans, index construction, parameter arithmetic and the
bounded accuracy/word-cap decision occur before sampling. -/


private theorem setup_scalar (N H a b c : ℕ) (hH : 1000000 ≤ H)
    (ha : a ≤ (N + 2) * H ^ 4) (hb : b ≤ 2000 * (H + 1)) (hc : c ≤ H ^ 4) :
    a + b + c ≤ (N + 2) * H ^ 5 := by
  have hb' : 2000 * (H + 1) ≤ H ^ 2 := by nlinarith only [hH]
  have hs : H ^ 2 ≤ H ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hcoef0 := Nat.mul_le_mul_left (N + 2) (show 2 ≤ H by omega)
  have hcoef : N + 2 + 2 ≤ (N + 2) * H := by omega
  calc
    _ ≤ (N + 2) * H ^ 4 + H ^ 4 + H ^ 4 := by omega
    _ = (N + 2 + 2) * H ^ 4 := by ring
    _ ≤ ((N + 2) * H) * H ^ 4 := Nat.mul_le_mul_right _ hcoef
    _ = _ := by ring

 theorem integerPreevaluationWork_near_linear_oai (C : ℕ) (epsilonTime : ℝ) (htime : 0 < epsilonTime) :
    ∀ᶠ N in atTop, ∀ source target : List ℤ, source.length + target.length ≤ N →
      (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
      ∀ epsilon : BinaryFraction,
      (integerPreevaluationWork source target N epsilon : ℝ) ≤
        (N + 2 : ℝ) ^ (1 + epsilonTime) := by
  filter_upwards [fixed_height_power_near_linear 5 epsilonTime htime,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop (max 1000000 C)),
    computed_localOnlineMassBound_word] with N ht hH hmass
  intro source target hsize halphabet epsilon
  have hheight : 1000000 ≤ inputHeight N :=
    (le_max_left _ _).trans (hH.trans (computed_smallLog_le_height N))
  have hC : C ≤ inputHeight N :=
    (le_max_right _ _).trans (hH.trans (computed_smallLog_le_height N))
  have hp := integerPreprocessingWork_le source target N C hsize halphabet (by omega) hC
  have hg := globalParameterWork_le N
  have hd := physicalLargeInputWithWork_le_height N epsilon hheight hmass
  have hbound := setup_scalar N (inputHeight N) _ _ _ hheight hp hg hd
  exact (show (integerPreevaluationWork source target N epsilon : ℝ) ≤
      (N + 2 : ℝ) * (inputHeight N : ℝ) ^ 5 by exact_mod_cast hbound).trans ht

end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.integerPreevaluationWork_near_linear_oai := @OAI.EditApproximation.integerPreevaluationWork_near_linear_oai
