-- Prove2me | solution 1 for OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsWithWork_cost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:30:37.699211+00:00
-- url     : https://prove2.me/submissions/96e3ad15-3e75-4a5c-b18b-972ab65c7335

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
import Definitions.Def_OAIQ361V3Ea002
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_bandActionWithWork_cost
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_preparedRepresentativeWithWork_complete_cost
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_preparedUnskippedCandidateWithWork_uniform_cost

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ActionVectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The actual fixed-block action hull

Coordinates are precisely the child/state pairs occurring in a finite band.
Each action assigns its fixed rational child mass to one state per child.
This verifies the probability, coverage and block-mass hypotheses used by
the numerical optimizer and optimistic entropy regret.
-/

namespace EditApproximation

open Finset





theorem action_coordinate_mem {β σ : Type*} [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : Finset (β → σ)) {action : β → σ} (haction : action ∈ band) (child : β) :
    (child, action child) ∈ bandCoordinates band := by
  apply mem_biUnion.mpr
  exact ⟨action, haction, mem_image.mpr ⟨child, mem_univ _, rfl⟩⟩

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
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandOptimizerWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Reindexing the exact finite optimizer onto an explicit, duplicate-free
coordinate array. The array order is retained throughout the evaluation. -/

namespace EditApproximation

open Finset

/-- Concrete ordered coordinates; no enumeration of the ambient state
type and no choice of an equivalence is used by the evaluator. -/


theorem listedBandCoordinates_nodup {M : ℕ} {σ : Type*} [DecidableEq σ]
    (band : List (Fin M → σ)) : (listedBandCoordinates band).Nodup :=
  List.nodup_dedup _

theorem listedBandCoordinates_toFinset {M : ℕ} {σ : Type*} [DecidableEq σ]
    (band : List (Fin M → σ)) :
    (listedBandCoordinates band).toFinset = bandCoordinates band.toFinset := by
  ext coordinate
  constructor
  · intro hc
    obtain ⟨action, ha, hc⟩ := List.mem_flatMap.mp
      (List.mem_dedup.mp (List.mem_toFinset.mp hc))
    obtain ⟨child, hchild⟩ := List.mem_ofFn.mp hc
    rw [← hchild]
    exact action_coordinate_mem band.toFinset (List.mem_toFinset.mpr ha) child
  · intro hc
    obtain ⟨action, ha, hc⟩ := mem_biUnion.mp hc
    obtain ⟨child, _, heq⟩ := mem_image.mp hc
    apply List.mem_toFinset.mpr
    apply List.mem_dedup.mpr
    apply List.mem_flatMap.mpr
    exact ⟨action, List.mem_toFinset.mp ha, List.mem_ofFn.mpr ⟨child, heq⟩⟩

theorem listedBandCoordinates_length {M : ℕ} {σ : Type*} [DecidableEq σ]
    (band : List (Fin M → σ)) :
    (listedBandCoordinates band).length = (bandCoordinates band.toFinset).card := by
  rw [← listedBandCoordinates_toFinset band,
    List.toFinset_card_of_nodup (listedBandCoordinates_nodup band)]

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRoundedWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
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
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value
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



theorem dedupByWithWork_cost {α : Type*} (equal : α → α → Bool × ℕ)
    (C : ℕ) (hC : ∀ a b, (equal a b).2 ≤ C) (xs : List α) :
    (dedupByWithWork equal xs).2 ≤ (xs.length + 1) ^ 2 * (C + 4) := by
  induction xs with
  | nil => simp only [dedupByWithWork, List.length_nil] <;> nlinarith
  | cons a rest ih =>
    have hm := memberByWithWork_cost equal C hC a rest
    change _ + _ + 2 ≤ _
    simp only [List.length_cons]
    nlinarith only [ih, hm, Nat.zero_le C, Nat.zero_le rest.length]

namespace BinaryFraction



theorem bandCoordinatesWithWork_cost {M n : ℕ} (band : List (Fin M → TargetInterval n))
    (B : ℕ) (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    (bandCoordinatesWithWork band).2 ≤ bandCoordinatesBitBudget M band.length B := by
  let raw := arithmeticFlatMapWithWork (fun action : Fin M → TargetInterval n =>
    arithmeticMapWithWork (fun i : Fin M => ((i, action i), 1)) (List.finRange M)) band
  have hlength : raw.1.length = band.length * M := by
    dsimp only [raw]
    simp only [arithmeticFlatMapWithWork_value, arithmeticMapWithWork_value]
    induction band with
    | nil => simp
    | cons a rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_finRange,
        List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  have hraw := arithmeticFlatMapWithWork_cost
    (fun action : Fin M → TargetInterval n =>
      arithmeticMapWithWork (fun i : Fin M => ((i, action i), 1)) (List.finRange M))
    band (4 * M) M (by
      intro action _
      have h := arithmeticMapWithWork_cost
        (fun i : Fin M => ((i, action i), 1)) (List.finRange M) 1 (by intros; rfl)
      simpa only [List.length_finRange, Nat.mul_comm] using h) (by
      intro action _
      simp only [arithmeticMapWithWork_value, List.length_map, List.length_finRange, le_refl])
  change raw.2 ≤ _ at hraw
  have hunique := dedupByWithWork_cost coordinateEqualWithWork (24 * B + 8)
    (fun a b => coordinateEqualWithWork_cost a b B hM hn) raw.1
  rw [hlength] at hunique
  change raw.2 + (dedupByWithWork coordinateEqualWithWork raw.1).2 + 1 ≤ _
  unfold bandCoordinatesBitBudget
  nlinarith only [hraw, hunique]

end BinaryFraction
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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryTriangularChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The optimizer's sampled iteration is obtained by the exact triangular
block search, with every threshold multiplication and comparison charged. -/

namespace EditApproximation



theorem triangularMassWithWork_bounds (K B : ℕ) (hK : Nat.size K ≤ B) :
    (triangularMassWithWork K).1.length ≤ 3 * B + 4 ∧
      (triangularMassWithWork K).2 ≤ 10000 * (B + 3) ^ 2 := by
  let next := binaryNaturalAddWithWork K 1
  let product := binaryNaturalMulWithWork K (bitWordValue next.1)
  let quotient := binaryNaturalDivModWithWork (bitWordValue product.1) 2
  have hn : Nat.size (bitWordValue next.1) ≤ B + 3 := by
    rw [binaryNaturalAddWithWork_value]
    exact (binaryNaturalAdd_size_le K 1).trans (by simp only [Nat.size_one]; omega)
  have hp := bitMulWithWork_length K.bits (bitWordValue next.1).bits
  change product.1.length ≤ _ at hp
  simp only [Nat.size_eq_bits_len] at hp
  have hps : Nat.size (bitWordValue product.1) ≤ 3 * B + 4 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length product.1)).trans (by omega)
  have hq := (bitDivModWithWork_lengths (2 : ℕ).bits (bitWordValue product.1).bits).1
  change quotient.1.length = _ at hq
  rw [Nat.size_eq_bits_len] at hq
  have hc1 := binaryNaturalAddWithWork_cost K 1
  have hc2 := binaryNaturalMulWithWork_cost K (bitWordValue next.1)
  have hc3 := binaryNaturalDivModWithWork_cost (bitWordValue product.1) 2
  simp only [Nat.size_one, show Nat.size 2 = 2 by decide] at hc1 hc3
  constructor
  · change quotient.1.length ≤ _
    omega
  · change next.2 + product.2 + quotient.2.2 + 3 ≤ _
    change next.2 ≤ _ at hc1
    change product.2 ≤ _ at hc2
    change quotient.2.2 ≤ _ at hc3
    nlinarith only [hc1, hc2, hc3, hK, hn, hps, Nat.zero_le B]

theorem triangularChoiceWithWork_cost (K : ℕ) (integer : Fin (optimizerTriangularMass K))
    (B : ℕ) (hK : Nat.size K ≤ B) (hi : Nat.size integer.val ≤ B) :
    (triangularChoiceWithWork K integer).2 ≤ triangularChoiceBitBudget K B := by
  induction K generalizing B with
  | zero => exact Fin.elim0 integer
  | succ K ih =>
    have hprev : Nat.size K ≤ B := (Nat.size_le_size (Nat.le_succ K)).trans hK
    have hthreshold := triangularMassWithWork_bounds K B hprev
    have hs : Nat.size (bitWordValue (triangularMassWithWork K).1) ≤ 3 * B + 4 :=
      (Nat.size_le.mpr (bitWordValue_lt_pow_length _)).trans hthreshold.1
    have hcompare := binaryNaturalCompareWithWork_cost integer.val
      (bitWordValue (triangularMassWithWork K).1)
    change (let threshold := triangularMassWithWork K
      let test := binaryNaturalCompareWithWork integer.val (bitWordValue threshold.1)
      if h : test.1 = .lt then
        let hsmall : integer.val < optimizerTriangularMass K := by
          have ht := (binaryNaturalCompareWithWork_lt _ _).mp h
          simpa only [threshold, triangularMassWithWork_value] using ht
        let chosen := triangularChoiceWithWork K ⟨integer.val, hsmall⟩
        (chosen.1.castSucc, threshold.2 + test.2 + chosen.2 + 2)
      else (⟨K, Nat.lt_succ_self K⟩, threshold.2 + test.2 + 1) : Fin (K + 1) × ℕ).2 ≤ _
    dsimp only
    split_ifs with h
    · have hsmall : integer.val < optimizerTriangularMass K := by
        have hc := (binaryNaturalCompareWithWork_lt _ _).mp h
        simpa only [triangularMassWithWork_value] using hc
      have hr := ih ⟨integer.val, hsmall⟩ B hprev hi
      unfold triangularChoiceBitBudget at hr ⊢
      nlinarith only [hthreshold.2, hcompare, hr, hs, hi, Nat.zero_le K, Nat.zero_le B]
    · unfold triangularChoiceBitBudget
      nlinarith only [hthreshold.2, hcompare, hs, hi, Nat.zero_le K, Nat.zero_le B]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCoordinateAction
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.reduceOnlineIntegerWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The prepared online action explicitly constructs its coordinate array
and compares stored endpoints when constructing each vertex. -/

namespace EditApproximation
namespace BinaryFraction



theorem countedBandCoordinateWithWork_eq {M n : ℕ} (mass : Vector BinaryFraction M)
    (total : BinaryFraction) (action : Fin M → TargetInterval n)
    (coordinate : Fin M × TargetInterval n) :
    (countedBandCoordinateWithWork mass total action coordinate).1 =
      (bandCoordinateWithWork mass total action coordinate).1 ∧
    (countedBandCoordinateWithWork mass total action coordinate).2 =
      (coordinateEqualWithWork coordinate (coordinate.1, action coordinate.1)).2 +
      (bandCoordinateWithWork mass total action coordinate).2 + 1 := by
  have ht : (coordinateEqualWithWork coordinate (coordinate.1, action coordinate.1)).1 = true ↔
      coordinate.2 = action coordinate.1 := by
    rw [coordinateEqualWithWork_value]
    exact ⟨fun h => congrArg Prod.snd h, fun h => Prod.ext rfl h⟩
  unfold countedBandCoordinateWithWork bandCoordinateWithWork
  dsimp only
  by_cases h : coordinate.2 = action coordinate.1
  · simp only [ite_eq_left h, ite_eq_left (ht.mpr h), and_self]
  · simp only [ite_eq_right h, ite_eq_right (fun hp => h (ht.mp hp)), and_self]



@[simp] theorem countedBandVerticesWithWork_value {M n d : ℕ}
    (coordinates : Vector (Fin M × TargetInterval n) d)
    (mass : Vector BinaryFraction M) (band : List (Fin M → TargetInterval n)) :
    (countedBandVerticesWithWork coordinates mass band).1 =
      (labeledBandVerticesWithWork coordinates mass band).1 := by
  simp only [countedBandVerticesWithWork, labeledBandVerticesWithWork, List.map_map,
    Function.comp_def]
  apply List.map_congr_left
  intro action _
  apply congrArg (Prod.mk action)
  apply Vector.ext
  intro i hi
  change ((vectorMapWithWork d _).1.get ⟨i, hi⟩) = ((vectorMapWithWork d _).1.get ⟨i, hi⟩)
  rw [vectorMapWithWork_value, vectorMapWithWork_value]
  exact (countedBandCoordinateWithWork_eq _ _ _ _).1

@[simp] theorem countedPreparedActionWithWork_value {M n : ℕ}
    (mass : Vector BinaryFraction M) (table : ℕ → Fin M × TargetInterval n → BinaryFraction)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t : ℕ) :
    (countedPreparedActionWithWork mass table eta kappa band G j t).1 =
      (preparedBandActionWithWork mass table eta kappa band G j t).1 := by
  simp only [countedPreparedActionWithWork, coordinateVectorWithWork_value,
    countedBandVerticesWithWork_value, preparedBandActionWithWork]

@[simp] theorem countedBandActionWithWork_value {M n : ℕ} (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval n → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval n)) (G j t : ℕ) :
    (countedBandActionWithWork b initial table eta kappa band G j t).1 =
      (bandActionWithWork b initial table eta kappa band G j t).1 := by
  simp only [countedBandActionWithWork, countedPreparedActionWithWork_value, bandActionWithWork]

@[simp] theorem countedSampledOnlineWithWork_value {M n : ℕ} (center : TargetInterval n) (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval n → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (G K t : ℕ) (integer : Fin (optimizerTriangularMass K)) :
    (countedSampledOnlineWithWork center b initial table eta kappa band hne G K t integer).1 =
      (sampledOnlineActionWithWork center b initial table eta kappa band hne G K t integer).1 := by
  simp only [countedSampledOnlineWithWork, countedBandActionWithWork_value, sampledOnlineActionWithWork]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCoordinateActionWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cost of coordinate construction and every endpoint equality is
added to the complete optimizer cost, with no unit-cost rational
or uncharged generic equality operation. -/

namespace EditApproximation
namespace BinaryFraction

private theorem vectorMap_cost_le_add {α β : Type*} (d : ℕ)
    (first : Fin d → α × ℕ) (second : Fin d → β × ℕ) (C : ℕ)
    (h : ∀ i, (first i).2 ≤ (second i).2 + C) :
    (vectorMapWithWork d first).2 ≤ (vectorMapWithWork d second).2 + d * C := by
  simp only [vectorMapWithWork, Vector.toList_map, Vector.toList_ofFn,
    List.map_ofFn, Function.comp_def, List.sum_ofFn]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hs
  omega

theorem countedBandVerticesWithWork_cost {M n d : ℕ}
    (coordinates : Vector (Fin M × TargetInterval n) d) (mass : Vector BinaryFraction M)
    (band : List (Fin M → TargetInterval n)) (B : ℕ)
    (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    (countedBandVerticesWithWork coordinates mass band).2 ≤
      (labeledBandVerticesWithWork coordinates mass band).2 + band.length * d * (24 * B + 9) := by
  have hvertex (action : Fin M → TargetInterval n) :
      (vectorMapWithWork d (fun i => countedBandCoordinateWithWork mass
        (bandMassTotalWithWork mass).1 action (coordinates.get i))).2 ≤
      (vectorMapWithWork d (fun i => bandCoordinateWithWork mass
        (bandMassTotalWithWork mass).1 action (coordinates.get i))).2 + d * (24 * B + 9) := by
    apply vectorMap_cost_le_add
    intro i
    rw [(countedBandCoordinateWithWork_eq _ _ _ _).2]
    have hc := coordinateEqualWithWork_cost (coordinates.get i)
      ((coordinates.get i).1, action (coordinates.get i).1) B hM hn
    omega
  have hsum :
      (band.map (fun action => (vectorMapWithWork d (fun i => countedBandCoordinateWithWork mass
        (bandMassTotalWithWork mass).1 action (coordinates.get i))).2)).sum ≤
      (band.map (fun action => (vectorMapWithWork d (fun i => bandCoordinateWithWork mass
        (bandMassTotalWithWork mass).1 action (coordinates.get i))).2)).sum +
      band.length * (d * (24 * B + 9)) := by
    induction band with
    | nil => simp
    | cons action rest ih =>
      have ha := hvertex action
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  simp only [countedBandVerticesWithWork, labeledBandVerticesWithWork, List.map_map,
    Function.comp_def]
  simpa only [Nat.mul_assoc] using (show
    (bandMassTotalWithWork mass).2 + _ + 8 * band.length ≤
      (bandMassTotalWithWork mass).2 + _ + 8 * band.length + band.length * (d * (24 * B + 9)) by omega)

theorem countedPreparedActionWithWork_cost {M n : ℕ} (mass : Vector BinaryFraction M)
    (table : ℕ → Fin M × TargetInterval n → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval n)) (G j t B : ℕ)
    (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    (countedPreparedActionWithWork mass table eta kappa band G j t).2 ≤
      (preparedBandActionWithWork mass table eta kappa band G j t).2 +
      bandCoordinatesBitBudget M band.length B + (listedBandCoordinates band).length +
      band.length * (listedBandCoordinates band).length * (24 * B + 9) + 2 := by
  have hc := bandCoordinatesWithWork_cost band B hM hn
  have hv := countedBandVerticesWithWork_cost (listedBandCoordinateVector band) mass band B hM hn
  unfold countedPreparedActionWithWork
  simp only [coordinateVectorWithWork_value, countedBandVerticesWithWork_value]
  change (coordinateVectorWithWork band).2 +
    (countedBandVerticesWithWork (listedBandCoordinateVector band) mass band).2 + _ + _ + 3 ≤ _
  unfold coordinateVectorWithWork
  simp only [bandCoordinatesWithWork_value]
  unfold preparedBandActionWithWork
  dsimp only
  omega

theorem countedBandActionWithWork_cost {M n : ℕ} (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval n → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval n)) (G j t B : ℕ)
    (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    (countedBandActionWithWork b initial table eta kappa band G j t).2 ≤
      (bandActionWithWork b initial table eta kappa band G j t).2 +
      bandCoordinatesBitBudget M band.length B + (listedBandCoordinates band).length +
      band.length * (listedBandCoordinates band).length * (24 * B + 9) + 2 := by
  have h := countedPreparedActionWithWork_cost (envelopeVectorWithWork b band initial).1
    table eta kappa band G j t B hM hn
  unfold countedBandActionWithWork bandActionWithWork
  dsimp only
  omega

theorem countedSampledOnlineWithWork_cost {M n : ℕ} (center : TargetInterval n) (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval n → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (G K t B : ℕ) (integer : Fin (optimizerTriangularMass K))
    (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    (countedSampledOnlineWithWork center b initial table eta kappa band hne G K t integer).2 ≤
      (sampledOnlineActionWithWork center b initial table eta kappa band hne G K t integer).2 +
      bandCoordinatesBitBudget M band.length B + (listedBandCoordinates band).length +
      band.length * (listedBandCoordinates band).length * (24 * B + 9) + 2 := by
  have h := countedBandActionWithWork_cost b initial table eta kappa band G
    (triangularChoiceWithWork K integer).1.val t B hM hn
  unfold countedSampledOnlineWithWork sampledOnlineActionWithWork
  dsimp only
  omega

end BinaryFraction
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

theorem centerEligibilityWithWork_cost (b F B : ℕ) (a initial : BinaryFraction)
    (hB : 6 ≤ B) (hb : Nat.size b + 2 ≤ B) (hF : Nat.size F + 2 ≤ B)
    (ha : a.width ≤ B) (hi : initial.width ≤ B) :
    (centerEligibilityWithWork b F a initial).2 ≤ localEligibilityBitBudget B := by
  have hfour : (nat 4).width ≤ B := (nat_width_le 4).trans (by
    have h : Nat.size 4 = 3 := by decide
    omega)
  have height : (nat 8).width ≤ B := (nat_width_le 8).trans (by
    have h : Nat.size 8 = 4 := by decide
    omega)
  have hbn := (nat_width_le b).trans hb
  have hFn := (nat_width_le F).trans hF
  have hdw := canonicalMulWithWork_width (nat 4) a B hfour ha
  have hdc := canonicalMulWithWork_cost (nat 4) a B hfour ha
  have hlw := divWithWork_width_uniform (nat b) (canonicalMulWithWork (nat 4) a).1
    (4 * B + 2) (by omega) hdw
  have hlc := divWithWork_cost (nat b) (canonicalMulWithWork (nat 4) a).1
    (4 * B + 2) (by omega) hdw
  have hfw := canonicalMulWithWork_width (nat 8) (nat F) B height hFn
  have hfc := canonicalMulWithWork_cost (nat 8) (nat F) B height hFn
  have huw := canonicalMulWithWork_width (canonicalMulWithWork (nat 8) (nat F)).1 (nat b)
    (4 * B + 2) hfw (by omega)
  have huc := canonicalMulWithWork_cost (canonicalMulWithWork (nat 8) (nat F)).1 (nat b)
    (4 * B + 2) hfw (by omega)
  have hlow := leWithWork_cost (divWithWork (nat b) (canonicalMulWithWork (nat 4) a).1).1
    initial (16 * B + 12) (by omega) (by omega)
  have hhigh := leWithWork_cost initial
    (canonicalMulWithWork (canonicalMulWithWork (nat 8) (nat F)).1 (nat b)).1
    (16 * B + 12) (by omega) (by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hlc huc hlow hhigh
  change _ + _ + _ + _ + _ + _ + Nat.size b + Nat.size F + 8 ≤ _
  unfold localEligibilityBitBudget
  omega

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryOnlineSetupWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coordinate enumeration, index construction and range reduction
preceding the online optimizer, counted in Boolean operations. -/

namespace EditApproximation
namespace BinaryFraction

theorem onlineIndexSetupWithWork_bounds {M n : ℕ} (H B : ℕ)
    (band : List (Fin M → TargetInterval n))
    (_hB : 2 ≤ B) (hH : Nat.size H ≤ B) (hM : Nat.size M ≤ B)
    (hn : Nat.size n ≤ B) (hd : Nat.size (listedBandCoordinates band).length ≤ B) :
    Nat.size (onlineIndexSetupWithWork H band).1 ≤ B + 4 ∧
      (onlineIndexSetupWithWork H band).2 ≤ onlineIndexBitBudget M band.length B := by
  let coordinates := bandCoordinatesWithWork band
  let total := binaryNaturalAddWithWork H coordinates.1.length
  let offset := binaryNaturalAddWithWork (bitWordValue total.1) 2
  have hcoord := bandCoordinatesWithWork_cost band B hM hn
  have hd' : Nat.size coordinates.1.length ≤ B := by
    simpa only [coordinates, bandCoordinatesWithWork_value] using hd
  have htotal : Nat.size (bitWordValue total.1) ≤ B + 2 := by
    rw [binaryNaturalAddWithWork_value]
    exact (binaryNaturalAdd_size_le _ _).trans (by omega)
  have hoffset : offset.1.length ≤ B + 4 := by
    have hh := bitAddWithWork_length (bitWordValue total.1).bits (2 : ℕ).bits false
    change offset.1.length ≤ _ at hh
    rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len] at hh
    have htwo : Nat.size 2 = 2 := by decide
    omega
  have hsize : Nat.size (bitWordValue offset.1) ≤ B + 4 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length offset.1)).trans hoffset
  have hsumc := binaryNaturalAddWithWork_cost H coordinates.1.length
  have hoffc := binaryNaturalAddWithWork_cost (bitWordValue total.1) 2
  have hpower := bitPowerWithWork_cost offset.1 80 (B + 4) hoffset
  have htwo : Nat.size 2 = 2 := by decide
  constructor
  · exact hsize
  · change coordinates.2 + total.2 + offset.2 + (bitPowerWithWork offset.1 80).2 + 3 ≤ _
    change coordinates.2 ≤ _ at hcoord
    change total.2 ≤ _ at hsumc
    change offset.2 ≤ _ at hoffc
    rw [htwo] at hoffc
    unfold onlineIndexBitBudget
    omega

theorem reduceOnlineIntegerWithWork_bounds (K integer B : ℕ) (hK : 0 < K)
    (hKB : Nat.size K ≤ B) (hi : Nat.size integer ≤ B) :
    Nat.size (reduceOnlineIntegerWithWork K hK integer).1.val ≤ 3 * B + 4 ∧
      (reduceOnlineIntegerWithWork K hK integer).2 ≤ reduceOnlineBitBudget B := by
  let mass := triangularMassWithWork K
  have hm := triangularMassWithWork_bounds K B hKB
  have hms : Nat.size (bitWordValue mass.1) ≤ 3 * B + 4 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length mass.1)).trans hm.1
  have hpos : 0 < bitWordValue mass.1 := by
    rw [triangularMassWithWork_value]
    exact optimizerTriangularMass_positive K hK
  have hsmall := (binaryNaturalDivModWithWork_spec integer (bitWordValue mass.1) hpos).2
  have hrem : Nat.size (bitWordValue (binaryNaturalDivModWithWork integer (bitWordValue mass.1)).2.1) ≤
      3 * B + 4 := by
    rw [hsmall]
    exact (Nat.size_le_size (Nat.mod_lt integer hpos).le).trans hms
  have hc := binaryNaturalDivModWithWork_cost integer (bitWordValue mass.1)
  constructor
  · exact hrem
  · change mass.2 + (binaryNaturalDivModWithWork integer (bitWordValue mass.1)).2.2 + Nat.size integer + 2 ≤ _
    have hmc : mass.2 ≤ 10000 * (B + 3) ^ 2 := hm.2
    unfold reduceOnlineBitBudget
    have hprod : (Nat.size integer + 1) * (Nat.size integer + Nat.size (bitWordValue mass.1) + 1) ≤
        (4 * B + 6) ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul (by omega) (by omega)
    have h30 := Nat.mul_le_mul_left 30 hprod
    rw [Nat.mul_assoc] at hc
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySampledOnlineWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cost of the actual triangular choice followed by the complete stored
fraction online optimizer. This includes the envelope and vertex builders. -/

namespace EditApproximation
namespace BinaryFraction

theorem sampledOnlineActionWithWork_cost {ny M : ℕ} (center : TargetInterval ny) (b : ℕ)
    (initial : Fin M → TargetInterval ny → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval ny → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval ny)) (hne : band ≠ [])
    (G K t : ℕ) (integer : Fin (optimizerTriangularMass K))
    (B Be Bk Bi Bt E : ℕ) (hb : 0 < b) (hM : 0 < M)
    (hK : Nat.size K ≤ B) (hinteger : Nat.size integer.val ≤ B)
    (he : eta.width ≤ Be) (hk : kappa.width ≤ Bk)
    (hi : ∀ action ∈ band, ∀ j, (initial j (action j)).width ≤ Bi)
    (ht : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (table s ((listedBandCoordinateVector band).get i)).width ≤ Bt)
    (heabs : |eta.value| ≤ E) (hkrange : 0 ≤ kappa.value ∧ kappa.value ≤ 1)
    (htrange : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      0 ≤ (table s ((listedBandCoordinateVector band).get i)).value ∧
        (table s ((listedBandCoordinateVector band).get i)).value ≤
          (initial ((listedBandCoordinateVector band).get i).1
            ((listedBandCoordinateVector band).get i).2).value) :
    (sampledOnlineActionWithWork center b initial table eta kappa band hne G K t integer).2 ≤
      triangularChoiceBitBudget K B +
      bandActionBitBudget M (listedBandCoordinates band).length b band.length G
        (triangularChoice K integer).val t Be Bk Bi Bt E + M + 2 := by
  have hchoice := triangularChoiceWithWork_cost K integer B hK hinteger
  have hoptimizer := bandActionWithWork_cost b initial table eta kappa band G
    (triangularChoice K integer).val t Be Bk Bi Bt E hne hb hM he hk hi ht heabs hkrange htrange
  unfold sampledOnlineActionWithWork
  dsimp only
  rw [triangularChoiceWithWork_value]
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandActionPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed-degree envelope for the full labeled action selector, including
its final logarithm-gradient and argmax, after the iterative optimizer. -/

namespace EditApproximation

private theorem bandActionExpression_eval (M d b v G K t Be Bk Bi Bt E : ℕ) :
    bandActionExpression.eval (bandActionEnvironment M d b v G K t Be Bk Bi Bt E) =
      BinaryFraction.bandActionBitBudget M d b v G K t Be Bk Bi Bt E := by
  have hnat : (BinaryFraction.nat G).width = max (Nat.size G) 1 := by
    simp only [BinaryFraction.nat, BinaryFraction.width, SignedBinary.ofInt,
      Int.natAbs_natCast, ← Nat.size_eq_bits_len, List.length_cons, List.length_nil]
  simp only [bandActionExpression, bandActionEnvironment, expressionSelection,
    expressionEnvelopeWord, expressionEnvelopeWork, expressionBandPreparation_p0,
    expressionBandCoordinateBit_p0, expressionBandVertexWord_p0, expressionBandSumStorage_p0,
    expressionStoredSumBit_p0, expressionStoredSumWord_p0, expressionOnlineBit_p0,
    expressionOnlineStorage_p0, expressionOptimisticStorage_p0, expressionOptimisticBit_p0,
    expressionGainBit_p0, expressionDecrementBit_p0, expressionCoefficientBit_p0,
    expressionOptimizer_p0, expressionPoint_p0, expressionGradientStorage_p0,
    expressionGradientBit_p0, expressionLogStorage_p0, expressionLogBit_p0, expressionLogUniversal_p0,
    expressionLogStep_p0, expressionMaximizer_p0, expressionUpdate_p0, baSize, baMax,
    FiniteBitPolynomial.eval, BinaryFraction.bandActionBitBudget,
    BinaryFraction.preparedBandActionBitBudget, BinaryFraction.selectionBitBudget,
    BinaryFraction.bandEnvelopeWordBudget, BinaryFraction.bandEnvelopeBitBudget,
    BinaryFraction.bandPreparationBitBudget, BinaryFraction.bandCoordinateBitBudget,
    BinaryFraction.bandVertexWordBudget, BinaryFraction.bandMassTotalStorageBudget,
    BinaryFraction.storedSumBitBudget, BinaryFraction.storedSumWordBudget,
    BinaryFraction.onlineLinearBitBudget, BinaryFraction.onlineLinearStorageBudget,
    BinaryFraction.onlineFinalWordBudget, BinaryFraction.optimisticTermStorageBudget,
    BinaryFraction.optimisticTermBitBudget, BinaryFraction.optimisticTermWordBudget,
    BinaryFraction.gainBitBudget, BinaryFraction.decrementBitBudget,
    BinaryFraction.coefficientBitBudget, BinaryFraction.optimizerBitBudget,
    BinaryFraction.optimizerRoundBitBudget, BinaryFraction.optimizerPointWordBudget,
    BinaryFraction.optimizerGradientWordBudget, UnreducedRational.gradientStorageBudget,
    UnreducedRational.logarithmStorageBudget, BinaryFraction.gradientCellBitBudget,
    BinaryFraction.generalPowerWordBudget, BinaryFraction.smoothingStorageBudget,
    BinaryFraction.shiftedStorageBudget, BinaryFraction.gradientLogStorageBudget,
    BinaryFraction.logarithmBitBudget, BinaryFraction.logarithmUniversalWordBudget,
    BinaryFraction.logarithmPartialBitStep, BinaryFraction.maximizerBitBudget,
    BinaryFraction.maximizerWordBudget, BinaryFraction.dotWordBudget,
    BinaryFraction.optimizerUpdateBitBudget, BinaryFraction.updateCoordinateWordBudget,
    BinaryFraction.updateCoefficientWordBudget, hnat]
  rfl

theorem bandActionBitBudget_fixedPower (M d b v G K t Be Bk Bi Bt E S : ℕ)
    (hS : 2 ≤ S) (hM : M ≤ S) (hd : d ≤ S) (hb : Nat.size b ≤ S)
    (hv : v ≤ S) (hG : G ≤ S) (hK : K ≤ S) (ht : t ≤ S)
    (hBe : Be ≤ S) (hBk : Bk ≤ S) (hBi : Bi ≤ S) (hBt : Bt ≤ S) (hE : E ≤ S) :
    BinaryFraction.bandActionBitBudget M d b v G K t Be Bk Bi Bt E ≤ S ^ bandActionBitDegree := by
  have henv : ∀ i, bandActionEnvironment M d b v G K t Be Bk Bi Bt E i ≤ S := by
    intro i
    fin_cases i <;> simp only [bandActionEnvironment] <;> assumption
  simpa only [bandActionExpression_eval, bandActionBitDegree] using
    bandActionExpression.eval_le_pow _ S hS henv

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySampledOnlinePolynomial
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete sampled online action, including the triangular search,
coordinate equality tests, final logarithm-gradient and labeled argmax. -/

namespace EditApproximation

private theorem sampledOnlineOverhead_eval (M v d K B : ℕ) :
    sampledOnlineOverhead.eval (sampledOnlineOverheadEnv M v d K B) =
      triangularChoiceBitBudget K B + M + 2 + BinaryFraction.bandCoordinatesBitBudget M v B + d +
        v * d * (24 * B + 9) + 2 := rfl

theorem countedSampledOnlineWithWork_fixedPower {M n : ℕ} (center : TargetInterval n) (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval n → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (G K t B E S : ℕ) (integer : Fin (optimizerTriangularMass K))
    (hS : 2 ≤ S) (hMpos : 0 < M) (hbpos : 0 < b)
    (hM : M ≤ S) (hv : band.length ≤ S) (hd : (listedBandCoordinates band).length ≤ S)
    (hG : G ≤ S) (hK : K ≤ S) (ht : t ≤ S) (hB : B ≤ S) (hE : E ≤ S)
    (hb : Nat.size b ≤ S) (hMb : Nat.size M ≤ B) (hnb : Nat.size n ≤ B)
    (hKb : Nat.size K ≤ B) (hinteger : Nat.size integer.val ≤ B)
    (he : eta.width ≤ B) (hk : kappa.width ≤ B)
    (hi : ∀ i q, (initial i q).width ≤ B)
    (hh : ∀ s ≤ t + 1, ∀ i q, (table s (i, q)).width ≤ B)
    (heabs : |eta.value| ≤ E) (hkrange : 0 ≤ kappa.value ∧ kappa.value ≤ 1)
    (hhrange : ∀ s ≤ t + 1, ∀ i q, 0 ≤ (table s (i, q)).value ∧
      (table s (i, q)).value ≤ (initial i q).value) :
    (BinaryFraction.countedSampledOnlineWithWork center b initial table eta kappa band hne G K t integer).2 ≤
      S ^ sampledOnlineBitDegree := by
  let d := (listedBandCoordinates band).length
  let j := (triangularChoice K integer).val
  have hj : j ≤ S := (triangularChoice K integer).isLt.le.trans hK
  have ha := bandActionBitBudget_fixedPower
    M d b band.length G j t B B B B E S hS hM hd hb hv hG hj ht hB hB hB hB hE
  have hs := BinaryFraction.sampledOnlineActionWithWork_cost center b initial table eta kappa band hne
    G K t integer B B B B B E hbpos hMpos hKb hinteger he hk
    (fun action _ i => hi i (action i))
    (fun s hs i => hh s hs _ _) heabs hkrange
    (fun s hs i => hhrange s hs _ _)
  have hc := BinaryFraction.countedSampledOnlineWithWork_cost center b initial table eta kappa
    band hne G K t B integer hMb hnb
  have henv : ∀ i, sampledOnlineOverheadEnv M band.length d K B i ≤ S := by
    intro i
    fin_cases i <;> simp only [sampledOnlineOverheadEnv] <;> assumption
  have ho := sampledOnlineOverhead.eval_le_pow _ S hS henv
  rw [sampledOnlineOverhead_eval] at ho
  let D := max bandActionBitDegree sampledOnlineOverhead.degree
  have h1 : S ^ bandActionBitDegree ≤ S ^ D := Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)
  have h2 : S ^ sampledOnlineOverhead.degree ≤ S ^ D := Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)
  change (BinaryFraction.countedSampledOnlineWithWork center b initial table eta kappa band hne G K t integer).2 ≤
    S ^ (D + 1)
  calc
    _ ≤ 2 * S ^ D := by dsimp only [d, j] at ha ho; omega
    _ ≤ S * S ^ D := Nat.mul_le_mul_right _ hS
    _ = _ := (pow_succ' S D).symm

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalArithmeticBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compiled optimizer counter specialized to the literal representative
bands. Preparation of the input arrays remains a separate finite loop. -/

namespace EditApproximation

theorem computedBandActions_length_le {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (tau theta velocity : ℚ)
    (child : Fin M → TargetInterval ny → ℚ) :
    (computedBandActions parent r b P tau theta velocity child).length ≤
      (wideActionList M parent r b P).length := by
  dsimp only [computedBandActions]
  split_ifs <;> first | exact List.length_filter_le _ _ | exact Nat.zero_le _

theorem representativeBandActions_length_le {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P : ℕ) (tau theta : ℚ) (child : Fin M → TargetInterval target.length → ℚ) :
    (representativeBandActions source target parent r b P tau theta child).length ≤
      (wideActionList M parent r b P).length := by
  dsimp only [representativeBandActions]
  split_ifs <;> first | exact computedBandActions_length_le _ _ _ _ _ _ _ _ | exact Nat.zero_le _

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedUnskippedWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete unskipped-band constructor pays for both actual wide
grids, every prefix predicate, all child envelopes, and the final guards. -/

namespace EditApproximation
namespace BinaryFraction

theorem representativeCompleteBitBudget_mono_vertices (M v w B : ℕ) (h : v ≤ w) :
    representativeCompleteBitBudget M v B ≤ representativeCompleteBitBudget M w B := by
  unfold representativeCompleteBitBudget representativeTailBitBudget bandFromActionsBitBudget
    wideMinimumBitBudget bandPredicateBitBudget anchorGuardBitBudget bandToleranceBitBudget
    representativeGuardInputBudget naturalDistanceBitBudget
  dsimp only
  gcongr

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PreparedBandPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed-degree bound for the complete band constructor. The sole
non-polynomial quantity is the actual Cartesian-product list bound, an
explicit input subsequently bounded by the computed grid parameters. -/

namespace EditApproximation

private theorem preparedBandPolynomial_eval (e b M P v w B : ℕ) :
    preparedBandPolynomial.eval (preparedBandEnvironment e b M P v w B) =
      BinaryFraction.preparedUnskippedBitBudget e b M P v w B := rfl

theorem preparedUnskippedBitBudget_fixedPower (e b M P v w B S : ℕ)
    (hS : 2 ≤ S) (he : e ≤ S) (hb : Nat.size b ≤ S) (hM : M ≤ S) (hP : P ≤ S)
    (hv : v ≤ S) (hw : w ≤ S) (hB : B ≤ S)
    (hC : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ S) :
    BinaryFraction.preparedUnskippedBitBudget e b M P v w B ≤ S ^ preparedBandBitDegree := by
  have henv : ∀ i, preparedBandEnvironment e b M P v w B i ≤ S := by
    intro i
    fin_cases i <;> simp only [preparedBandEnvironment] <;> assumption
  simpa only [preparedBandPolynomial_eval, preparedBandBitDegree] using
    preparedBandPolynomial.eval_le_pow _ S hS henv

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedOnlineWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete local online call: materialized endpoint grids, all band
guards, explicit index/range construction and the actual sampled optimizer. -/

namespace EditApproximation
namespace BinaryFraction

theorem onlineIndexBitBudget_mono_vertices (M B vertices vertices' : ℕ)
    (hvertices : vertices ≤ vertices') :
    onlineIndexBitBudget M vertices B ≤ onlineIndexBitBudget M vertices' B := by
  unfold onlineIndexBitBudget bandCoordinatesBitBudget
  gcongr

theorem preparedOnlineWithWork_cost {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b B E S : ℕ)
    (hbpos : 0 < b) (hPpos : 0 < P) (hMpos : 0 < M)
    (tau eta kappa : BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction)
    (t : ℕ) (center : TargetInterval target.length) (integer : ℕ)
    (hB : 7 ≤ B) (hnx : Nat.size source.length + 2 ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hMb : Nat.size M ≤ B)
    (hb : Nat.size b + 2 ≤ B) (hP : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B)
    (he : exponent + 1 ≤ B) (hH : Nat.size H ≤ B)
    (hdBits : Nat.size (M * (40 * P + 2) ^ 2) ≤ B)
    (hKBits : Nat.size ((H + M * (40 * P + 2) ^ 2 + 2) ^ 80) ≤ B)
    (hInteger : Nat.size integer ≤ B)
    (htau : tau.width ≤ B) (heta : eta.width ≤ B) (hkappa : kappa.width ≤ B)
    (hchild : ∀ i q, (child i q).width ≤ B)
    (hinitial : ∀ i q, (initial i q).width ≤ B)
    (htable : ∀ s ≤ t + 1, ∀ i q, (table s (i, q)).width ≤ B)
    (hetaValue : |eta.value| ≤ E) (hkappaValue : 0 ≤ kappa.value ∧ kappa.value ≤ 1)
    (hvalues : ∀ s ≤ t + 1, ∀ i q, 0 ≤ (table s (i, q)).value ∧
      (table s (i, q)).value ≤ (initial i q).value)
    (hS : 2 ≤ S) (hMS : M ≤ S) (hPS : P ≤ S) (hES : E ≤ S) (htS : t ≤ S)
    (hBS : 3 * B + 4 ≤ S) (hvS : (40 * P + 2) ^ (2 * M) ≤ S)
    (hcartS : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ S)
    (hKS : (H + M * (40 * P + 2) ^ 2 + 2) ^ 80 ≤ S) :
    (preparedOnlineWithWork source target parent P F exponent H b hbpos hPpos tau eta kappa
      child initial table t center integer).2 ≤ preparedOnlineBitBudget M P B S := by
  let band := preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
    tau (inversePowerTwo exponent) child
  let setup := onlineIndexSetupWithWork H band.1
  let G := setup.1
  let accepted := reduceOnlineIntegerWithWork (G ^ 80) (by
    dsimp only [G, setup]
    rw [onlineIndexSetupWithWork_value]
    positivity) integer
  let V := (40 * P + 2) ^ (2 * M)
  let D := M * (40 * P + 2) ^ 2
  have hbandValue : band.1 = representativeBandActions source target parent center b P tau.value
      (inversePowerTwo exponent).value (fun i q => (child i q).value) :=
    preparedRepresentativeWithWork_value source target parent center b P hPpos tau (inversePowerTwo exponent) child
  have hbandLen : band.1.length ≤ V := by
    rw [hbandValue]
    exact (representativeBandActions_length_le source target parent center b P tau.value
      (inversePowerTwo exponent).value (fun i q => (child i q).value)).trans
      (wideActionList_length_le M parent center b P hPpos)
  have hd : (listedBandCoordinates band.1).length ≤ D := by
    rw [listedBandCoordinates_length, hbandValue]
    exact bandCoordinates_card_le parent center hPpos _
      (fun action ha => representativeBandActions_wide source target parent center b P tau.value
        (inversePowerTwo exponent).value (fun i q => (child i q).value) action ha)
  have hg : G ≤ H + D + 2 := by
    dsimp only [G, setup]
    rw [onlineIndexSetupWithWork_value]
    omega
  have hgp : 0 < G := by
    dsimp only [G, setup]
    rw [onlineIndexSetupWithWork_value]
    omega
  have hK : G ^ 80 ≤ (H + D + 2) ^ 80 := Nat.pow_le_pow_left hg 80
  have hGtotal : H + D + 2 ≤ S :=
    (Nat.le_pow (by omega : 0 < 80)).trans hKS
  have hdimS : (listedBandCoordinates band.1).length ≤ S := hd.trans (by omega)
  have hbS : B ≤ S := by omega
  have hguard := (preparedUnskippedCandidateWithWork_uniform_cost source target parent b P exponent B
    hbpos hPpos tau (nat F) child initial center hnx hny hMb hb hP he htau
    ((nat_width_le F).trans hF) hchild hinitial).trans
    (preparedUnskippedBitBudget_fixedPower exponent b M P V V B S hS (by omega) (by omega)
      hMS hPS hvS hvS hbS hcartS)
  have hwide : (wideActionGridWithWork M parent center b P).1.length ≤ V := by
    have hh := congrArg List.length (wideActionGridWithWork_value M parent center b P hPpos)
    simp only [List.length_map] at hh
    rw [hh]
    exact wideActionList_length_le M parent center b P hPpos
  have hbandCost := preparedRepresentativeWithWork_complete_cost parent center b P B hPpos tau
    (inversePowerTwo exponent) child (by omega) (by omega) hMb (by omega) hP htau
    (by rw [inversePowerTwo_width]; exact he) hchild
  have hrepMono := representativeCompleteBitBudget_mono_vertices M _ V (4 * B + 20) hwide
  have hbandPower : band.2 ≤ S ^ preparedBandBitDegree := by
    have hcap := preparedUnskippedBitBudget_fixedPower exponent b M P V V B S hS (by omega)
      (by omega) hMS hPS hvS hvS hbS hcartS
    apply le_trans _ hcap
    unfold preparedUnskippedBitBudget
    change band.2 ≤ _ at hbandCost
    omega
  have hsetup := onlineIndexSetupWithWork_bounds H B band.1 (by omega) hH hMb (by omega)
    ((Nat.size_le_size hd).trans hdBits)
  have hsetupCost : setup.2 ≤ onlineIndexBitBudget M V B :=
    hsetup.2.trans (onlineIndexBitBudget_mono_vertices M B _ _ hbandLen)
  have hKsize : Nat.size (G ^ 80) ≤ B := (Nat.size_le_size hK).trans hKBits
  have haccepted := reduceOnlineIntegerWithWork_bounds (G ^ 80) integer B (pow_pos hgp _) hKsize hInteger
  have hsample (hne : band.1 ≠ []) :
      (countedSampledOnlineWithWork center b initial table eta kappa band.1 hne G (G ^ 80) t accepted.1).2 ≤
        S ^ sampledOnlineBitDegree := by
    apply countedSampledOnlineWithWork_fixedPower center b initial table eta kappa band.1 hne
      G (G ^ 80) t (3 * B + 4) E S accepted.1 hS hMpos hbpos hMS
      (hbandLen.trans hvS) hdimS (hg.trans hGtotal) (hK.trans hKS) htS hBS hES (by omega)
      (by omega) (by omega) (by omega) haccepted.1
      (heta.trans (by omega)) (hkappa.trans (by omega))
      (fun i q => (hinitial i q).trans (by omega))
      (fun s hs i q => (htable s hs i q).trans (by omega)) hetaValue hkappaValue hvalues
  dsimp only [V] at hsetupCost
  unfold preparedOnlineWithWork
  dsimp only
  split_ifs with hempty hactive
  · change band.2 + setup.2 + accepted.2 + 1 ≤ _
    have hc : accepted.2 ≤ reduceOnlineBitBudget B := haccepted.2
    unfold preparedOnlineBitBudget
    omega
  · have hs := hsample hempty
    have hc : accepted.2 ≤ reduceOnlineBitBudget B := haccepted.2
    change band.2 + setup.2 + accepted.2 +
      (preparedUnskippedCandidateWithWork source target parent b P exponent hbpos hPpos tau (nat F)
        child initial center).2 +
      (countedSampledOnlineWithWork center b initial table eta kappa band.1 hempty
        G (G ^ 80) t accepted.1).2 + 2 ≤ _
    unfold preparedOnlineBitBudget
    omega
  · have hc : accepted.2 ≤ reduceOnlineBitBudget B := haccepted.2
    change band.2 + setup.2 + accepted.2 + _ + 1 ≤ _
    unfold preparedOnlineBitBudget
    omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedLocalOnlineWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All selected scales execute rounding, the center guard, and the complete
sampled optimizer. The list contains at most one action per tested scale. -/

namespace EditApproximation
namespace BinaryFraction

theorem preparedLocalOnlineScaleWithWork_cost {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H e B E S : ℕ)
    (hPpos : 0 < P) (hMpos : 0 < M)
    (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (query : TargetInterval target.length)
    (hB : 7 ≤ B) (heScale : e ≤ B) (hnx : Nat.size source.length + 2 ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hMb : Nat.size M ≤ B)
    (hP : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B)
    (he : exponent + 1 ≤ B) (hH : Nat.size H ≤ B)
    (hdBits : Nat.size (M * (40 * P + 2) ^ 2) ≤ B)
    (hKBits : Nat.size ((H + M * (40 * P + 2) ^ 2 + 2) ^ 80) ≤ B)
    (hInteger : ∀ b r, Nat.size (integer b r) ≤ B)
    (htau : tau.width ≤ B) (ha : a.width ≤ B) (heta : eta.width ≤ B) (hkappa : kappa.width ≤ B)
    (hparent : ∀ r, (parentInitial r).width ≤ B)
    (hchild : ∀ i q, (child i q).width ≤ B) (hinitial : ∀ i q, (initial i q).width ≤ B)
    (htable : ∀ s ≤ t + 1, ∀ i q, (table s (i, q)).width ≤ B)
    (hetaValue : |eta.value| ≤ E) (hkappaValue : 0 ≤ kappa.value ∧ kappa.value ≤ 1)
    (hvalues : ∀ s ≤ t + 1, ∀ i q, 0 ≤ (table s (i, q)).value ∧
      (table s (i, q)).value ≤ (initial i q).value)
    (hS : 2 ≤ S) (hMS : M ≤ S) (hPS : P ≤ S) (hES : E ≤ S) (htS : t ≤ S)
    (hBS : 3 * (B + 4) + 4 ≤ S) (hvS : (40 * P + 2) ^ (2 * M) ≤ S)
    (hcartS : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ S)
    (hKS : (H + M * (40 * P + 2) ^ 2 + 2) ^ 80 ≤ S) :
    (preparedLocalOnlineScaleWithWork source target parent P F exponent H e hPpos tau a eta kappa
      parentInitial child initial table t integer query).2 ≤ preparedLocalOnlineScaleBitBudget M P B S := by
  let W := B + 4
  let spacing := seedGridSpacingWithWork (2 ^ e) P
  let center := roundStateWithWork (bitWordValue spacing.1)
    (seedGridSpacingWithWork_pos (2 ^ e) P hPpos) query
  have hb : Nat.size (2 ^ e) + 2 ≤ W := by rw [Nat.size_pow]; dsimp only [W]; omega
  have hspacing := seedGridSpacingWithWork_bounds (2 ^ e) P W (by omega) (by dsimp only [W]; omega)
  have hspacingBits : Nat.size (bitWordValue spacing.1) ≤ W := by
    rw [seedGridSpacingWithWork_value _ _ hPpos]
    have hh : max 1 (2 ^ e / P) = 1 ∨ max 1 (2 ^ e / P) = 2 ^ e / P := max_choice _ _
    rcases hh with hh | hh
    · rw [seedGridSpacing, hh, Nat.size_one]
      dsimp only [W]
      omega
    · rw [seedGridSpacing, hh]
      exact (Nat.size_le_size (Nat.div_le_self _ _)).trans (by omega)
  have hround := roundStateWithWork_cost (bitWordValue spacing.1)
    (seedGridSpacingWithWork_pos (2 ^ e) P hPpos) query W hspacingBits (by dsimp only [W]; omega)
  have hguard := centerEligibilityWithWork_cost (2 ^ e) F W a (parentInitial center.1)
    (by dsimp only [W]; omega) hb (by dsimp only [W]; omega)
    (ha.trans (by dsimp only [W]; omega)) ((hparent _).trans (by dsimp only [W]; omega))
  have honline := preparedOnlineWithWork_cost source target parent P F exponent H (2 ^ e) W E S
    (Nat.two_pow_pos _) hPpos hMpos tau eta kappa child initial table t center.1
    (integer (2 ^ e) center.1) (by dsimp only [W]; omega)
    (by dsimp only [W]; omega) (by dsimp only [W]; omega) (by dsimp only [W]; omega)
    hb (by dsimp only [W]; omega) (by dsimp only [W]; omega) (by dsimp only [W]; omega)
    (by dsimp only [W]; omega) (by dsimp only [W]; omega) (by dsimp only [W]; omega)
    ((hInteger _ _).trans (by dsimp only [W]; omega))
    (htau.trans (by dsimp only [W]; omega)) (heta.trans (by dsimp only [W]; omega))
    (hkappa.trans (by dsimp only [W]; omega))
    (fun i q => (hchild i q).trans (by dsimp only [W]; omega))
    (fun i q => (hinitial i q).trans (by dsimp only [W]; omega))
    (fun s hs i q => (htable s hs i q).trans (by dsimp only [W]; omega))
    hetaValue hkappaValue hvalues hS hMS hPS hES htS hBS hvS hcartS hKS
  have hs : spacing.2 ≤ 100 * (W + 2) ^ 2 := hspacing.2
  have hr : center.2 ≤ 500 * (W + 1) ^ 2 + 1 := hround
  unfold preparedLocalOnlineScaleWithWork
  dsimp only
  split_ifs
  · change spacing.2 + center.2 + (centerEligibilityWithWork (2 ^ e) F a (parentInitial center.1)).2 +
      (preparedOnlineWithWork source target parent P F exponent H (2 ^ e) (Nat.two_pow_pos e) hPpos
        tau eta kappa child initial table t center.1 (integer (2 ^ e) center.1)).2 + e + 4 ≤ _
    unfold preparedLocalOnlineScaleBitBudget
    change _ ≤ 100 * (W + 2) ^ 2 + (500 * (W + 1) ^ 2 + 1) +
      localEligibilityBitBudget W + preparedOnlineBitBudget M P W S + B + 4
    omega
  · change spacing.2 + center.2 + (centerEligibilityWithWork (2 ^ e) F a (parentInitial center.1)).2 + e + 3 ≤ _
    unfold preparedLocalOnlineScaleBitBudget
    change _ ≤ 100 * (W + 2) ^ 2 + (500 * (W + 1) ^ 2 + 1) +
      localEligibilityBitBudget W + preparedOnlineBitBudget M P W S + B + 4
    omega

theorem preparedLocalOnlineActionsWithWork_cost_oai {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H B E S : ℕ)
    (hPpos : 0 < P) (hMpos : 0 < M)
    (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (query : TargetInterval target.length)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hnx : Nat.size source.length + 2 ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hMb : Nat.size M ≤ B)
    (hP : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B)
    (he : exponent + 1 ≤ B) (hH : Nat.size H ≤ B)
    (hdBits : Nat.size (M * (40 * P + 2) ^ 2) ≤ B)
    (hKBits : Nat.size ((H + M * (40 * P + 2) ^ 2 + 2) ^ 80) ≤ B)
    (hInteger : ∀ b r, Nat.size (integer b r) ≤ B)
    (htau : tau.width ≤ B) (ha : a.width ≤ B) (heta : eta.width ≤ B) (hkappa : kappa.width ≤ B)
    (hparent : ∀ r, (parentInitial r).width ≤ B)
    (hchild : ∀ i q, (child i q).width ≤ B) (hinitial : ∀ i q, (initial i q).width ≤ B)
    (htable : ∀ s ≤ t + 1, ∀ i q, (table s (i, q)).width ≤ B)
    (hetaValue : |eta.value| ≤ E) (hkappaValue : 0 ≤ kappa.value ∧ kappa.value ≤ 1)
    (hvalues : ∀ s ≤ t + 1, ∀ i q, 0 ≤ (table s (i, q)).value ∧
      (table s (i, q)).value ≤ (initial i q).value)
    (hS : 2 ≤ S) (hMS : M ≤ S) (hPS : P ≤ S) (hES : E ≤ S) (htS : t ≤ S)
    (hBS : 3 * (B + 4) + 4 ≤ S) (hvS : (40 * P + 2) ^ (2 * M) ≤ S)
    (hcartS : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ S)
    (hKS : (H + M * (40 * P + 2) ^ 2 + 2) ^ 80 ≤ S) :
    (preparedLocalOnlineActionsWithWork source target parent N P F exponent H hPpos tau a eta kappa
      parentInitial child initial table t integer query).2 ≤ preparedLocalOnlineBitBudget M P B S := by
  let scales := queryExponentsWithWork N F a (parentInitial query)
  have hs := queryExponentsWithWork_bounds N F B a (parentInitial query) hB hN hF ha (hparent query)
  have hc (e : ℕ) (heMem : e ∈ scales.1) :
      (preparedLocalOnlineScaleWithWork source target parent P F exponent H e hPpos tau a eta kappa
        parentInitial child initial table t integer query).2 ≤ preparedLocalOnlineScaleBitBudget M P B S := by
    have heRange := heMem
    change e ∈ (queryExponentsWithWork N F a (parentInitial query)).1 at heRange
    simp only [queryExponentsWithWork, filterWithWork_value] at heRange
    have heB : e ≤ B := by
      have hh := List.mem_range.mp (List.mem_filter.mp heRange).1
      rw [Nat.size_eq_bits_len] at hh
      omega
    exact preparedLocalOnlineScaleWithWork_cost source target parent P F exponent H e B E S
      hPpos hMpos tau a eta kappa parentInitial child initial table t integer query
      hB heB hnx hny hMb hP hF he hH hdBits hKBits hInteger htau ha heta hkappa hparent
      hchild hinitial htable hetaValue hkappaValue hvalues hS hMS hPS hES htS hBS hvS hcartS hKS
  have hf := filterMapWithWork_cost
    (fun e => preparedLocalOnlineScaleWithWork source target parent P F exponent H e hPpos
      tau a eta kappa parentInitial child initial table t integer query) scales.1
    (preparedLocalOnlineScaleBitBudget M P B S) hc
  have hfc := hf.trans (Nat.mul_le_mul_right _ hs.2)
  change scales.2 + (filterMapWithWork
    (fun e => preparedLocalOnlineScaleWithWork source target parent P F exponent H e hPpos
      tau a eta kappa parentInitial child initial table t integer query) scales.1).2 + 1 ≤ _
  have hsc : scales.2 ≤ queryExponentsBitBudget B := hs.1
  unfold preparedLocalOnlineBitBudget
  omega

end BinaryFraction
end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsWithWork_cost_oai.{u_1} := @OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsWithWork_cost_oai.{u_1}
