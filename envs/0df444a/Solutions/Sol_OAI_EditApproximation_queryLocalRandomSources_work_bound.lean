-- Prove2me | solution 1 for OAI.EditApproximation.queryLocalRandomSources_work_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:37:23.102075+00:00
-- url     : https://prove2.me/submissions/cdbe5b6a-9aa3-4cd9-b4ef-e91704625ea7

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
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_OAIQ361V3Ea002
import Definitions.Def_OAIQ361V3Ea003
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_preparedRepresentativeWithWork_complete_cost
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_queryGroupKeysWithWork_bounds
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_queryGroupSourceKeysWithWork_bounds
import Theorems.Thm_OAI_EditApproximation_queryLocalRefinement_work_bound
import Theorems.Thm_OAI_EditApproximation_queryOnlineSourceGather_work_bound

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
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandGroupSampling
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Executable shared group estimates

All dyadic powers in the prescribed closed range are enumerated, including
negative exponents. A scale is evaluated exactly when its sample count
reaches the child count; otherwise one shared array of uniform labels is
used for every member of the group. The selected member is the first
minimizer in the fixed list order.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory



theorem groupDyadicScales_length (M b : ℕ) (F : ℚ) :
    (groupDyadicScales M b F).length =
      (Int.log 2 (64 * F * b) - Int.clog 2 ((b : ℚ) / M) + 1).toNat := by
  simp only [groupDyadicScales, List.length_map, integerClosedRange, List.length_range]

theorem groupDyadicScales_length_dyadic (eM eb eF : ℕ) :
    (groupDyadicScales (2 ^ eM) (2 ^ eb) ((2 : ℚ) ^ eF)).length = 7 + eM + eF := by
  have hlower : ((2 ^ eb : ℕ) : ℚ) / (2 ^ eM : ℕ) = (2 : ℚ) ^ ((eb : ℤ) - eM) := by
    rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0),
      zpow_natCast, zpow_natCast]
  have hupper : (64 : ℚ) * (2 : ℚ) ^ eF * (2 ^ eb : ℕ) =
      (2 : ℚ) ^ ((6 + eF + eb : ℕ) : ℤ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, zpow_natCast, pow_add, pow_add]
    norm_num
  have hlog : Int.log 2 ((2 : ℚ) ^ ((6 + eF + eb : ℕ) : ℤ)) = ((6 + eF + eb : ℕ) : ℤ) := by
    simpa only [Nat.cast_ofNat] using Int.log_zpow (R := ℚ) (by decide : 1 < 2) ((6 + eF + eb : ℕ) : ℤ)
  have hclog : Int.clog 2 ((2 : ℚ) ^ ((eb : ℤ) - eM)) = (eb : ℤ) - eM := by
    simpa only [Nat.cast_ofNat] using Int.clog_zpow (R := ℚ) (by decide : 1 < 2) ((eb : ℤ) - eM)
  rw [groupDyadicScales_length, hlower, hupper, hlog, hclog]
  omega

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
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
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



theorem saturatingSubtractWithWork_cost (a b : ℕ) :
    (saturatingSubtractWithWork a b).2 ≤ 13 * (Nat.size a + Nat.size b) + 4 := by
  have htest := binaryNaturalCompareWithWork_cost a b
  have hsub := binaryNaturalSubtractWithWork_cost a b
  unfold saturatingSubtractWithWork
  dsimp only
  split_ifs <;> omega

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryReadCostBounds
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lookup overhead is controlled by the loops that actually run.
These comparisons require only a bound on one finite-buffer lookup. -/

namespace EditApproximation

theorem arithmeticMapWithWork_factor {α β : Type*} (read plain : α → β × ℕ)
    (xs : List α) (K : ℕ) (hK : 1 ≤ K)
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 * K) :
    (arithmeticMapWithWork read xs).1 = (arithmeticMapWithWork plain xs).1 ∧
    (arithmeticMapWithWork read xs).2 ≤ (arithmeticMapWithWork plain xs).2 * K := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [arithmeticMapWithWork, Nat.zero_mul, le_refl]⟩
  | cons x xs ih =>
    have hx := hv x List.mem_cons_self
    have hcx := hc x List.mem_cons_self
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    constructor
    · simp only [arithmeticMapWithWork, hx, ht.1]
    · simp only [arithmeticMapWithWork]
      nlinarith only [hcx, ht.2, hK]


theorem filterWithWork_factor {α : Type*} (read plain : α → Bool × ℕ)
    (xs : List α) (K : ℕ) (hK : 1 ≤ K)
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 * K) :
    (filterWithWork read xs).1 = (filterWithWork plain xs).1 ∧
    (filterWithWork read xs).2 ≤ (filterWithWork plain xs).2 * K := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [filterWithWork, Nat.zero_mul, le_refl]⟩
  | cons x xs ih =>
    have hx := hv x List.mem_cons_self
    have hcx := hc x List.mem_cons_self
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    constructor
    · simp only [filterWithWork, hx, ht.1]
    · simp only [filterWithWork]
      nlinarith only [hcx, ht.2, hK]

theorem allWithWork_factor {α : Type*} (read plain : α → Bool × ℕ)
    (xs : List α) (K : ℕ) (hK : 1 ≤ K)
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 * K) :
    (allWithWork read xs).1 = (allWithWork plain xs).1 ∧
    (allWithWork read xs).2 ≤ (allWithWork plain xs).2 * K := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [allWithWork, Nat.zero_mul, le_refl]⟩
  | cons x xs ih =>
    have hx := hv x List.mem_cons_self
    have hcx := hc x List.mem_cons_self
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    constructor
    · simp only [allWithWork, hx, ht.1]
    · simp only [allWithWork]
      nlinarith only [hcx, ht.2, hK]

/-- Multiplicative work bounds are preserved when the same nonnegative
overhead is added to both counters. -/
theorem cost_replace_factor (a c old new K : ℕ) (hc : c ≤ a * K) (hK : 1 ≤ K)
    (ha : a ≤ old) (hn : new + a ≤ old + c) : new ≤ old * K := by
  have hx := Nat.mul_le_mul_left (old - a) hK
  simp only [Nat.mul_one] at hx
  have he : a + (old - a) = old := by omega
  calc
    new ≤ c + (old - a) := by omega
    _ ≤ a * K + (old - a) * K := Nat.add_le_add hc hx
    _ = old * K := by rw [← Nat.add_mul, he]

namespace BinaryFraction

theorem tableReadFactor_pos (R : ℕ) : 1 ≤ tableReadFactor R := by
  unfold tableReadFactor
  omega

theorem tableReadFactor_absorb (a c n R : ℕ) (hc : c ≤ a + n * (R + 3)) (hn : n ≤ a) :
    c ≤ a * tableReadFactor R := by
  have hm := Nat.mul_le_mul_right (R + 3) hn
  have hk : R + 4 ≤ tableReadFactor R := by unfold tableReadFactor; omega
  calc
    c ≤ a + a * (R + 3) := hc.trans (Nat.add_le_add_left hm a)
    _ = a * (R + 4) := by ring
    _ ≤ a * tableReadFactor R := Nat.mul_le_mul_left a hk

theorem endpointScoreReadWithWork_factor {n M : ℕ} (r : TargetInterval n)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (states : Fin M → TargetInterval n)
    (R : ℕ) (hr : ∀ i, (read i (states i)).2 ≤ R) :
    (endpointScoreReadWithWork r read states).2 ≤
      (endpointScoreWithWork r (fun i q => (read i q).1) states).2 * tableReadFactor R := by
  apply tableReadFactor_absorb _ _ M R (endpointScoreReadWithWork_cost r read states R hr)
  simp only [endpointScoreWithWork, endpointConnectionWithWork]
  omega

theorem prefixReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx) (r : TargetInterval n)
    (states : Fin M → TargetInterval n) (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (j : ℕ) (p : BinaryFraction) (R : ℕ) (hr : ∀ i, (read i (states i)).2 ≤ R) :
    (prefixReadWithWork parent r states read j p).2 ≤
      (prefixWithWork parent r states (fun i q => (read i q).1) j p).2 * tableReadFactor R := by
  have hc := prefixReadWithWork_cost parent r states read j p R hr
  have hn : M ≤ (prefixWithWork parent r states (fun i q => (read i q).1) j p).2 := by
    simp only [prefixWithWork]
    omega
  have hm := Nat.mul_le_mul_right (R + 4) hn
  have hk : R + 5 ≤ tableReadFactor R := by unfold tableReadFactor; omega
  calc
    _ ≤ _ + M * (R + 4) := hc
    _ ≤ _ + (prefixWithWork parent r states (fun i q => (read i q).1) j p).2 * (R + 4) :=
      Nat.add_le_add_left hm _
    _ = (prefixWithWork parent r states (fun i q => (read i q).1) j p).2 * (R + 5) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hk

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandReadCosts
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite-buffer lookup multiplies local band-loop work by a fixed
linear factor. Every comparison uses the same actual band and output. -/

namespace EditApproximation
namespace BinaryFraction

theorem wideMinimumReadWithWork_factor {n M : ℕ} (r : TargetInterval n)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ [])
    (R : ℕ) (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (wideMinimumReadWithWork r read actions hne).2 ≤
      (wideMinimumWithWork r (fun i q => (read i q).1) actions hne).2 * tableReadFactor R := by
  have hm := arithmeticMapWithWork_factor
    (endpointScoreReadWithWork r read) (endpointScoreWithWork r (fun i q => (read i q).1))
    actions (tableReadFactor R) (tableReadFactor_pos R)
    (fun action _ => endpointScoreReadWithWork_eq r read action)
    (fun action ha => endpointScoreReadWithWork_factor r read action R (hr action ha))
  have hf := endpointScoreReadWithWork_factor r read (actions.head hne) R
    (hr _ (List.head_mem hne))
  have hc := Nat.add_le_add hf hm.2
  rw [← Nat.add_mul] at hc
  apply cost_replace_factor _ _ _ _ _ hc (tableReadFactor_pos R)
  · unfold wideMinimumWithWork
    dsimp only
    omega
  · unfold wideMinimumReadWithWork wideMinimumWithWork
    dsimp only
    rw [hm.1, endpointScoreReadWithWork_eq]
    omega

theorem prefixMinimumReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (j : ℕ) (p : BinaryFraction)
    (R : ℕ) (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (prefixMinimumReadWithWork parent r actions hne read j p).2 ≤
      (prefixMinimumWithWork parent r actions hne (fun i q => (read i q).1) j p).2 *
        tableReadFactor R := by
  have hm := arithmeticMapWithWork_factor
    (fun action => prefixReadWithWork parent r action read j p)
    (fun action => prefixWithWork parent r action (fun i q => (read i q).1) j p)
    actions (tableReadFactor R) (tableReadFactor_pos R)
    (fun action _ => prefixReadWithWork_eq parent r action read j p)
    (fun action ha => prefixReadWithWork_factor parent r action read j p R (hr action ha))
  have hf := prefixReadWithWork_factor parent r (actions.head hne) read j p R
    (hr _ (List.head_mem hne))
  have hc := Nat.add_le_add hf hm.2
  rw [← Nat.add_mul] at hc
  apply cost_replace_factor _ _ _ _ _ hc (tableReadFactor_pos R)
  · unfold prefixMinimumWithWork
    dsimp only
    omega
  · unfold prefixMinimumReadWithWork prefixMinimumWithWork
    dsimp only
    rw [hm.1, prefixReadWithWork_eq]
    omega

theorem cutGuardReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (states : Fin M → TargetInterval n)
    (velocity tolerance : BinaryFraction) (j : Fin M) (R : ℕ)
    (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (cutGuardReadWithWork parent r actions hne read states velocity tolerance j).2 ≤
      (cutGuardWithWork parent r actions hne (fun i q => (read i q).1) states velocity tolerance j).2 *
        tableReadFactor R := by
  unfold cutGuardReadWithWork cutGuardWithWork
  split_ifs
  · simpa only [Nat.one_mul] using tableReadFactor_pos R
  · have h := prefixMinimumReadWithWork_factor parent r actions hne read j.val
      (subWithWork (nat (states j).lo) (nat (sourceChild parent j).lo)).1 R hr
    dsimp only
    rw [prefixMinimumReadWithWork_eq]
    apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R)
    · omega
    · omega

theorem bandPredicateReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (b : ℕ) (tau theta velocity : BinaryFraction)
    (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (states : Fin M → TargetInterval n)
    (R : ℕ) (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (bandPredicateReadWithWork parent r b tau theta velocity actions hne read states).2 ≤
      (bandPredicateWithWork parent r b tau theta velocity actions hne (fun i q => (read i q).1) states).2 *
        tableReadFactor R := by
  have hc := allWithWork_factor
    (cutGuardReadWithWork parent r actions hne read states velocity (bandToleranceWithWork tau theta b M).1)
    (cutGuardWithWork parent r actions hne (fun i q => (read i q).1) states velocity
      (bandToleranceWithWork tau theta b M).1)
    (List.finRange M) (tableReadFactor R) (tableReadFactor_pos R)
    (fun j _ => cutGuardReadWithWork_eq parent r actions hne read states velocity _ j)
    (fun j _ => cutGuardReadWithWork_factor parent r actions hne read states velocity _ j R hr)
  apply cost_replace_factor _ _ _ _ _ hc.2 (tableReadFactor_pos R)
  · unfold bandPredicateWithWork
    dsimp only
    omega
  · unfold bandPredicateReadWithWork bandPredicateWithWork
    dsimp only
    omega

theorem bandFromActionsReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (b : ℕ) (tau theta velocity : BinaryFraction)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ [])
    (R : ℕ) (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (bandFromActionsReadWithWork parent r b tau theta velocity read actions hne).2 ≤
      (bandFromActionsWithWork parent r b tau theta velocity (fun i q => (read i q).1) actions hne).2 *
        tableReadFactor R := by
  have hf := filterWithWork_factor
    (bandPredicateReadWithWork parent r b tau theta velocity actions hne read)
    (bandPredicateWithWork parent r b tau theta velocity actions hne (fun i q => (read i q).1))
    actions (tableReadFactor R) (tableReadFactor_pos R)
    (fun action _ => (bandPredicateReadWithWork_eq_cost parent r b tau theta velocity actions hne
      read action R hr).1)
    (fun action _ => bandPredicateReadWithWork_factor parent r b tau theta velocity actions hne
      read action R hr)
  unfold bandFromActionsReadWithWork bandFromActionsWithWork
  dsimp only
  split_ifs
  · apply cost_replace_factor _ _ _ _ _ hf.2 (tableReadFactor_pos R)
    · omega
    · omega
  · exact Nat.le_mul_of_pos_right _ (by have := tableReadFactor_pos R; omega)

theorem representativeFromActionsReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (sourceLength b : ℕ) (tau theta : BinaryFraction)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (actions : List (Fin M → TargetInterval n)) (R : ℕ)
    (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (representativeFromActionsReadWithWork parent r sourceLength b tau theta read actions).2 ≤
      (representativeFromActionsWithWork parent r sourceLength b tau theta
        (fun i q => (read i q).1) actions).2 * tableReadFactor R := by
  unfold representativeFromActionsReadWithWork representativeFromActionsWithWork
  by_cases hne : actions = []
  · simp only [dite_eq_left hne]
    simpa only [Nat.one_mul] using tableReadFactor_pos R
  · simp only [dite_eq_right hne]
    have hz := wideMinimumReadWithWork_factor r read actions hne R hr
    rw [wideMinimumReadWithWork_eq]
    split_ifs
    · have hb := bandFromActionsReadWithWork_factor parent r b tau theta
        (divWithWork (stateGapWithWork sourceLength r).1
          (wideMinimumWithWork r (fun i q => (read i q).1) actions hne).1).1 read actions hne R hr
      have hc := Nat.add_le_add hz hb
      rw [← Nat.add_mul] at hc
      apply cost_replace_factor _ _ _ _ _ hc (tableReadFactor_pos R) <;> omega
    · apply cost_replace_factor _ _ _ _ _ hz (tableReadFactor_pos R) <;> omega

theorem preparedRepresentativeReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (sourceLength b P : ℕ) (tau theta : BinaryFraction)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (R : ℕ)
    (hr : ∀ i q, (read i q).2 ≤ R) :
    (preparedRepresentativeReadWithWork parent r sourceLength b P tau theta read).2 ≤
      (preparedRepresentativeWithWork parent r sourceLength b P tau theta
        (fun i q => (read i q).1)).2 * tableReadFactor R := by
  have h := representativeFromActionsReadWithWork_factor parent r sourceLength b tau theta read
    ((wideActionGridWithWork M parent r b P).1.map Vector.get) R (fun _ _ i => hr i _)
  unfold preparedRepresentativeReadWithWork preparedRepresentativeWithWork
  dsimp only
  apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R) <;> omega

end BinaryFraction
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupSetup
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The literal scale list and sample counts, including scales below one.
Dyadic input exponents are carried by the computed parameter construction;
no real logarithm is evaluated by these routines. -/

namespace EditApproximation
namespace BinaryFraction



theorem groupScalesWithWork_length (eM eb eF : ℕ) :
    (groupScalesWithWork eM eb eF).1.length = 7 + eM + eF := by
  have h := congrArg List.length (groupScalesWithWork_value eM eb eF)
  simpa only [List.length_map, groupDyadicScales_length_dyadic] using h

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

end BinaryFraction
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedOnlineWork
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



theorem work_bind {ι α β : Type*} (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (program : BitQuery ι α) (next : α → BitQuery ι β) :
    (program.bind next).work oracle readWork =
      program.work oracle readWork + (next (program.value oracle)).work oracle readWork := by
  induction program with
  | done result => simp only [bind, work, value, Nat.zero_add]
  | read key continuation ih => simp only [bind, work, value, ih, Nat.add_assoc]
  | charge steps continuation ih => simp only [bind, work, value, ih, Nat.add_assoc]

/- A local charged step executes a Boolean routine with an explicit cost. -/


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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInitialSupport
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.triangularMassWithWork_value
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
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialSupportWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value
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



@[simp] theorem queryOrderedHistoryInputsWithWork_value {M n : ℕ}
    (inputs : List (Fin M × ℕ × TargetInterval n)) :
    (queryOrderedHistoryInputsWithWork inputs).1 =
      orderedInputs historyInputCode (historyInputCode_injective M n) inputs.toFinset := by
  apply queryOrderedInputsWithWork_value historyInputCode (historyInputCode_injective M n)
    _ _ queryHistoryEqualWithWork_value
  intro a b
  simp only [queryEncodedLEWithWork_value, queryHistoryCodeWithWork_value]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryRepresentatives
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryOrderedChildInputsWithWork_value _root_.OAI.EditApproximation.queryOrderedHistoryInputsWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryScalarDispatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The physical scalar sources locate a dyadic scale by a counted scan.
The scan computes the original first index and works also for absent scales. -/

namespace EditApproximation



theorem dyadicScales_size_bound (N b : ℕ) (hb : b ∈ dyadicScales N) :
    Nat.size b ≤ Nat.size N + 1 := by
  rw [← dyadicScalesWithWork_value N] at hb
  simp only [dyadicScalesWithWork, arithmeticMapWithWork_value, List.mem_map] at hb
  obtain ⟨e, he, rfl⟩ := hb
  rw [powerTwoWord_value, Nat.size_pow]
  have he' := List.mem_range.mp he
  rw [Nat.size_eq_bits_len] at he'
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryRawCenterCost
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
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

end EditApproximation.BinaryFraction

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryGroupSamples
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Group sample coordinates are enumerated from the computed dyadic
scale array and binary sample counts. Equalities used in index casts are
proofs only; the loop bounds are the values just computed. -/

namespace EditApproximation



namespace BinaryFraction



theorem queryGroupKeySamplesWithWork_value (M F Q eM eb eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (cell : ℕ × ℕ) :
    (queryGroupKeySamplesWithWork M F Q eM eb eF hM hF cell).1 =
      groupScalarKeys M F Q [(2 ^ eb, cell)] := by
  simp only [queryGroupKeySamplesWithWork, arithmeticFlatMapWithWork_value,
    arithmeticMapWithWork_value, queryFinRange_value, groupScalarKeys,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryGroupSources
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Complete scalar-source key generation uses the original dyadic
query window, cell order, scale order, and sample order. -/

namespace EditApproximation
namespace BinaryFraction



theorem queryGroupSourceKeysWithWork_value {n : ℕ} (M N F Q exponent eM eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (a value : BinaryFraction)
    (q : TargetInterval n) :
    (queryGroupSourceKeysWithWork M N F Q exponent eM eF hM hF a value q).1 =
      groupScalarKeys M F Q (localGroupQueryKeys N F exponent a.value (fun _ => value.value) q) := by
  simp only [queryGroupSourceKeysWithWork, arithmeticFlatMapWithWork_value,
    targetCellsWithWork_value, canonicalMulWithWork_value, inversePowerTwo_value, nat_value,
    naturalCeilingWithWork_value, queryGroupKeySamplesWithWork_value]
  conv_rhs => unfold localGroupQueryKeys
  rw [← queryExponentsWithWork_value N F a value]
  simp only [groupScalarKeys, List.flatMap_map, List.flatMap_assoc,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]

end BinaryFraction



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryDataBuffers
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
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



end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySourceBufferBounds
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Random-source lookups are charged at the bounded coordinates actually
consumed by the local loops. No bound is assumed on all natural keys. -/

namespace EditApproximation

theorem queryGroupKeyEqualWithWork_cost {M F Q : ℕ}
    (a b : GroupScalarKey M F Q) (B : ℕ)
    (ha : queryGroupKeySize a ≤ B) (hb : queryGroupKeySize b ≤ B) :
    (queryGroupKeyEqualWithWork a b).2 ≤ 40 * B + 14 := by
  unfold queryGroupKeySize at ha hb
  have h1 := naturalEqualWithWork_cost a.1.1 b.1.1 B (by omega) (by omega)
  have h2 := naturalEqualWithWork_cost a.1.2.1 b.1.2.1 B (by omega) (by omega)
  have h3 := naturalEqualWithWork_cost a.1.2.2 b.1.2.2 B (by omega) (by omega)
  have h4 := naturalEqualWithWork_cost a.2.1.val b.2.1.val B (by omega) (by omega)
  have h5 := naturalEqualWithWork_cost a.2.2.val b.2.2.val B (by omega) (by omega)
  change _ + _ + _ + _ + _ + 4 ≤ _
  omega

theorem queryOnlineKeyEqualWithWork_cost {n : ℕ} (a b : ℕ × TargetInterval n)
    (B : ℕ) (ha : Nat.size a.1 ≤ B) (hb : Nat.size b.1 ≤ B) (hn : Nat.size n ≤ B) :
    (queryOnlineKeyEqualWithWork a b).2 ≤ 24 * B + 8 := by
  have hs := naturalEqualWithWork_cost a.1 b.1 B ha hb
  have hi := queryIntervalEqualWithWork_cost a.2 b.2 B hn
  change _ + _ + 1 ≤ _
  omega

namespace BinaryFraction

theorem queryGroupDrawReadWithWork_cost {M F Q : ℕ} [NeZero M]
    (keys : List (GroupScalarKey M F Q)) (values : List BinaryFraction)
    (b : ℕ) (cell : ℕ × ℕ) (scale : Fin (groupDyadicScales M b F).length)
    (sample : Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)))
    (B V : ℕ) (hV : 2 ≤ V) (hM : Nat.size M ≤ B)
    (hkeys : ∀ key ∈ keys, queryGroupKeySize key ≤ B)
    (hquery : queryGroupKeySize (⟨(b, cell), scale, sample⟩ : GroupScalarKey M F Q) ≤ B)
    (hvalues : ∀ v ∈ values, v.width ≤ V) :
    (queryGroupDrawReadWithWork keys values b cell scale sample).2 ≤
      keys.length * (40 * B + 15) + 200 * (V + 1) ^ 2 +
        30 * (V + 1) * (V + B + 1) + 4 := by
  let query : GroupScalarKey M F Q := ⟨(b, cell), scale, sample⟩
  let word := gatheredWordLookupWithWork queryGroupKeyEqualWithWork keys values query
  have hl := gatheredWordLookupWithWork_cost_on queryGroupKeyEqualWithWork (40 * B + 14)
    keys values query (fun key hk => queryGroupKeyEqualWithWork_cost query key B hquery (hkeys key hk))
  have hw : word.1.width ≤ V := gatheredWordLookupWithWork_width _ keys values query V hV hvalues
  have hf := naturalFloorWithWork_bounds word.1
  have hs : Nat.size (bitWordValue (naturalFloorWithWork word.1).1) ≤ V :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length _)).trans (hf.1.trans hw)
  have hd := binaryNaturalDivModWithWork_cost (bitWordValue (naturalFloorWithWork word.1).1) M
  have hd' : (binaryNaturalDivModWithWork (bitWordValue (naturalFloorWithWork word.1).1) M).2.2 ≤
      30 * (V + 1) * (V + B + 1) := by
    apply hd.trans
    gcongr
  have hf' : (naturalFloorWithWork word.1).2 ≤ 200 * (V + 1) ^ 2 := by
    apply hf.2.trans
    gcongr
  have hl' : word.2 ≤ 1 + keys.length * (40 * B + 15) := by
    simpa only [word, query, Nat.add_assoc, Nat.reduceAdd] using hl
  change word.2 + (naturalFloorWithWork word.1).2 +
    (binaryNaturalDivModWithWork (bitWordValue (naturalFloorWithWork word.1).1) M).2.2 + 3 ≤ _
  omega

theorem queryOnlineIntegerReadWithWork_cost {n : ℕ}
    (keys : List (ℕ × TargetInterval n)) (values : List BinaryFraction)
    (b : ℕ) (q : TargetInterval n) (B V : ℕ) (hV : 2 ≤ V)
    (hn : Nat.size n ≤ B) (hb : Nat.size b ≤ B)
    (hkeys : ∀ key ∈ keys, Nat.size key.1 ≤ B) (hvalues : ∀ v ∈ values, v.width ≤ V) :
    (queryOnlineIntegerReadWithWork keys values b q).2 ≤
      keys.length * (24 * B + 9) + 200 * (V + 1) ^ 2 + 2 := by
  let word := gatheredWordLookupWithWork queryOnlineKeyEqualWithWork keys values (b, q)
  have hl := gatheredWordLookupWithWork_cost_on queryOnlineKeyEqualWithWork (24 * B + 8)
    keys values (b, q) (fun key hk => queryOnlineKeyEqualWithWork_cost (b, q) key B hb (hkeys key hk) hn)
  have hw : word.1.width ≤ V := gatheredWordLookupWithWork_width _ keys values (b, q) V hV hvalues
  have hf := (naturalFloorWithWork_bounds word.1).2
  have hf' : (naturalFloorWithWork word.1).2 ≤ 200 * (V + 1) ^ 2 := by
    apply hf.trans
    gcongr
  have hl' : word.2 ≤ 1 + keys.length * (24 * B + 9) := by
    simpa only [word, Nat.add_assoc, Nat.reduceAdd] using hl
  change word.2 + (naturalFloorWithWork word.1).2 + 1 ≤ _
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySourceKeyWidths
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

theorem groupScalarKeys_fst_mem (M F Q : ℕ) (groups : List (ℕ × (ℕ × ℕ)))
    (key : GroupScalarKey M F Q) (hk : key ∈ groupScalarKeys M F Q groups) : key.1 ∈ groups := by
  obtain ⟨group, hg, hk⟩ := List.mem_flatMap.mp hk
  obtain ⟨scale, _, hk⟩ := List.mem_flatMap.mp hk
  obtain ⟨sample, _, rfl⟩ := List.mem_map.mp hk
  exact hg

namespace BinaryFraction

theorem queryGroupKeySize_bound {n : ℕ} (M N F Q exponent eM eF B : ℕ)
    (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF) (a value : BinaryFraction) (q : TargetInterval n)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hM : Nat.size M ≤ B) (hes : 7 + eM + eF ≤ B) (he : exponent + 1 ≤ B)
    (hn : Nat.size n ≤ B) (ha : a.width ≤ B) (hv : value.width ≤ B) (hw : 0 ≤ value.value)
    (key : GroupScalarKey M F Q)
    (hk : key.1 ∈ (queryGroupKeysWithWork N F exponent a value q).1) :
    queryGroupKeySize key ≤ 40 * B + 500 := by
  have hFpos : 1 ≤ F := by rw [hFdef]; exact Nat.succ_le_of_lt (Nat.two_pow_pos _)
  have hk' := (queryGroupKeysWithWork_bounds N F exponent B a value q hB hN hF hFpos he hn ha hv hw).2.2 key.1 hk
  obtain ⟨hb, ⟨eb, heb⟩, hleft, hright⟩ := hk'
  have hlen : (groupDyadicScales M key.1.1 F).length = 7 + eM + eF := by
    have h := congrArg List.length (computedGroupScales_value M key.1.1 F eM eb eF hMdef heb hFdef)
    simpa only [List.length_map, groupScalesWithWork_length, nat_value] using h.symm
  have hscale : Nat.size key.2.1.val ≤ B := by
    have hv' : key.2.1.val ≤ B := by
      have hi : key.2.1.val < (groupDyadicScales M key.1.1 F).length := key.2.1.isLt
      have hl : (groupDyadicScales M key.1.1 F).length ≤ B := by rw [hlen]; exact hes
      exact (Nat.le_of_lt hi).trans hl
    exact (Nat.size_le_size hv').trans (Nat.size_le.mpr (Nat.lt_two_pow_self))
  have hsample : Nat.size key.2.2.val ≤ B := by
    have hi := key.2.2.isLt
    have hc : groupSampleCount M Q key.1.1 (groupDyadicScaleAt M key.1.1 F key.2.1) ≤ M := Nat.min_le_left _ _
    exact (Nat.size_le_size (show key.2.2.val ≤ M by omega)).trans hM
  unfold queryGroupKeySize
  omega

theorem queryGroupSourceKeysWithWork_width {n : ℕ} (M N F Q exponent eM eF B : ℕ)
    (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF) (a value : BinaryFraction) (q : TargetInterval n)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hM : Nat.size M ≤ B) (hes : 7 + eM + eF ≤ B) (he : exponent + 1 ≤ B)
    (hn : Nat.size n ≤ B) (ha : a.width ≤ B) (hv : value.width ≤ B) (hw : 0 ≤ value.value) :
    ∀ key ∈ (queryGroupSourceKeysWithWork M N F Q exponent eM eF hMdef hFdef a value q).1,
      queryGroupKeySize key ≤ 40 * B + 500 := by
  intro key hk
  rw [queryGroupSourceKeysWithWork_value] at hk
  apply queryGroupKeySize_bound M N F Q exponent eM eF B hMdef hFdef a value q
    hB hN hF hM hes he hn ha hv hw key
  rw [queryGroupKeysWithWork_value]
  exact groupScalarKeys_fst_mem M F Q _ key hk

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryScopedSourceCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source ports are bounded only at keys visited by the adaptive local
loops. Unused natural-number coordinates require no uniform size assumption. -/

namespace EditApproximation.BinaryFraction

theorem queryGroupKeysWithWork_mem_of_guard {n : ℕ} (N F exponent : ℕ)
    (a value : BinaryFraction) (q : TargetInterval n) (eb : ℕ)
    (heb : eb ∈ List.range (max 1 N.bits.length))
    (hg : (refinementScaleGuardWithWork F (2 ^ eb) a value).1 = true)
    (cell : ℕ × ℕ)
    (hc : cell ∈ (targetCellsWithWork
      (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
      (bitWordValue (naturalCeilingWithWork value).1) q).1) :
    (2 ^ eb, cell) ∈ (queryGroupKeysWithWork N F exponent a value q).1 := by
  have he : eb ∈ (queryExponentsWithWork N F a value).1 := by
    simp only [queryExponentsWithWork, filterWithWork_value, List.mem_filter]
    exact ⟨heb, hg⟩
  have hs : 2 ^ eb ∈ (queryScalesWithWork N F a value).1 := by
    simp only [queryScalesWithWork, arithmeticMapWithWork_value, List.mem_map]
    exact ⟨eb, he, powerTwoWord_value eb⟩
  simp only [queryGroupKeysWithWork, arithmeticFlatMapWithWork_value,
    arithmeticMapWithWork_value, List.mem_flatMap, List.mem_map]
  exact ⟨2 ^ eb, hs, cell, hc, rfl⟩

theorem queryGroupDrawReadWithWork_scoped_cost {n M N F Q : ℕ} [NeZero M]
    (exponent eM eF B V : ℕ) (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF)
    (a value : BinaryFraction) (q : TargetInterval n) (words : List BinaryFraction)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hM : Nat.size M ≤ B) (hes : 7 + eM + eF ≤ B) (he : exponent + 1 ≤ B)
    (hn : Nat.size n ≤ B) (ha : a.width ≤ B) (hv : value.width ≤ B) (hw : 0 ≤ value.value)
    (hV : 2 ≤ V) (hwords : ∀ v ∈ words, v.width ≤ V)
    (eb : ℕ) (heb : eb ∈ List.range (max 1 N.bits.length))
    (hg : (refinementScaleGuardWithWork F (2 ^ eb) a value).1 = true)
    (cell : ℕ × ℕ)
    (hc : cell ∈ (targetCellsWithWork
      (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
      (bitWordValue (naturalCeilingWithWork value).1) q).1)
    (scale : Fin (groupDyadicScales M (2 ^ eb) F).length)
    (sample : Fin (groupSampleCount M Q (2 ^ eb) (groupDyadicScaleAt M (2 ^ eb) F scale))) :
    let keys := (queryGroupSourceKeysWithWork M N F Q exponent eM eF hMdef hFdef a value q).1
    (queryGroupDrawReadWithWork keys words (2 ^ eb) cell scale sample).2 ≤
      queryGroupBufferReadBudget keys.length B V := by
  dsimp only
  apply queryGroupDrawReadWithWork_cost _ words _ cell scale sample (40 * B + 500) V hV
    (by omega)
    (queryGroupSourceKeysWithWork_width M N F Q exponent eM eF B hMdef hFdef a value q
      hB hN hF hM hes he hn ha hv hw) _ hwords
  apply queryGroupKeySize_bound M N F Q exponent eM eF B hMdef hFdef a value q
    hB hN hF hM hes he hn ha hv hw
  exact queryGroupKeysWithWork_mem_of_guard N F exponent a value q eb heb hg cell hc

theorem queryOnlineKeysWithWork_scale {n : ℕ} (N P F B : ℕ) (hP : 0 < P)
    (a value : BinaryFraction) (q : TargetInterval n) (hN : Nat.size N ≤ B) (hF : 1 ≤ F)
    (key : ℕ × TargetInterval n) (hk : key ∈ (queryOnlineKeysWithWork N P F hP a value q).1) :
    Nat.size key.1 ≤ B + 1 := by
  simp only [queryOnlineKeysWithWork, arithmeticMapWithWork_value, List.mem_map] at hk
  obtain ⟨b, hb, rfl⟩ := hk
  exact (queryScalesWithWork_member N F B a value hN hF b hb).1

theorem queryOnlineIntegerReadWithWork_scoped_cost {n : ℕ} (N P F B V : ℕ)
    (hP : 0 < P) (a value : BinaryFraction) (q : TargetInterval n) (words : List BinaryFraction)
    (hN : Nat.size N ≤ B) (hF : 1 ≤ F) (hn : Nat.size n ≤ B)
    (hV : 2 ≤ V) (hwords : ∀ v ∈ words, v.width ≤ V)
    (e : ℕ) (he : e ∈ (queryExponentsWithWork N F a value).1) :
    let keys := (queryOnlineKeysWithWork N P F hP a value q).1
    let center := (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
      (seedGridSpacingWithWork_pos (2 ^ e) P hP) q).1
    (queryOnlineIntegerReadWithWork keys words (2 ^ e) center).2 ≤
      queryOnlineBufferReadBudget keys.length B V := by
  have hs : 2 ^ e ∈ (queryScalesWithWork N F a value).1 := by
    simp only [queryScalesWithWork, arithmeticMapWithWork_value, List.mem_map]
    exact ⟨e, he, powerTwoWord_value e⟩
  apply queryOnlineIntegerReadWithWork_cost _ words _ _ (B + 1) V hV (by omega)
    (queryScalesWithWork_member N F B a value hN hF _ hs).1
    (queryOnlineKeysWithWork_scale N P F B hP a value q hN hF) hwords

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryBufferedSourceBounds
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

theorem queryBufferedGroupReadCost {n M N F Q : ℕ} [NeZero M]
    (exponent eM eF B V : ℕ) (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF)
    (a value : BinaryFraction) (q : TargetInterval n) (words : List BinaryFraction)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hM : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B) (hes : eM + eF + 7 ≤ B)
    (he : exponent + 1 ≤ B) (hn : Nat.size n ≤ B) (ha : a.width ≤ B)
    (hv : value.width ≤ B) (hw : 0 ≤ value.value) (hV : 2 ≤ V)
    (hwords : ∀ v ∈ words, v.width ≤ V) :
    let keys := (queryGroupSourceKeysWithWork M N F Q exponent eM eF hMdef hFdef a value q).1
    ∀ eb ∈ List.range (max 1 N.bits.length),
      (refinementScaleGuardWithWork F (2 ^ eb) a value).1 = true →
      ∀ cell ∈ (targetCellsWithWork
        (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
        (bitWordValue (naturalCeilingWithWork value).1) q).1,
      ∀ scale sample, (queryGroupDrawReadWithWork keys words (2 ^ eb) cell scale sample).2 ≤
        queryBufferedGroupReadBudget M F exponent eM eF B V := by
  dsimp only
  intro eb heb hg cell hc scale sample
  have hk := (queryGroupSourceKeysWithWork_bounds M N F Q exponent eM eF B hMdef hFdef a value q
    hB hN hF hM hQ hes he hn ha hv hw).1
  have hr := queryGroupDrawReadWithWork_scoped_cost exponent eM eF B V hMdef hFdef a value q words
    hB hN hF (by omega) (by omega) he hn ha hv hw hV hwords eb heb hg cell hc scale sample
  apply hr.trans
  unfold queryBufferedGroupReadBudget queryGroupBufferReadBudget
  gcongr

theorem queryBufferedOnlineReadCost {n : ℕ} (N P F B V : ℕ) (hP : 0 < P)
    (a value : BinaryFraction) (q : TargetInterval n) (words : List BinaryFraction)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hPb : Nat.size P ≤ B) (hn : Nat.size n ≤ B) (ha : a.width ≤ B) (hv : value.width ≤ B)
    (hV : 2 ≤ V) (hwords : ∀ v ∈ words, v.width ≤ V) :
    let keys := (queryOnlineKeysWithWork N P F hP a value q).1
    ∀ e ∈ (queryExponentsWithWork N F a value).1,
      (queryOnlineIntegerReadWithWork keys words (2 ^ e)
        (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
          (seedGridSpacingWithWork_pos (2 ^ e) P hP) q).1).2 ≤
        queryOnlineBufferReadBudget (B + 1) B V := by
  dsimp only
  intro e he
  have hk := (queryOnlineKeysWithWork_bounds N P F B hP a value q hB hN hF hFpos hPb hn ha hv).1
  have hr := queryOnlineIntegerReadWithWork_scoped_cost N P F B V hP a value q words
    hN hFpos hn hV hwords e he
  apply hr.trans
  unfold queryOnlineBufferReadBudget
  gcongr

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryHistoryInputCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

theorem queryRawHistoryInputsWithWork_time {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (P history : ℕ) (hP : 0 < P) (representatives : List (ℕ × TargetInterval ny))
    (input : Fin M × ℕ × TargetInterval ny)
    (hi : input ∈ (queryRawHistoryInputsWithWork M parent P history representatives).1) :
    input.2.1 < history := by
  rw [queryRawHistoryInputsWithWork_value M parent P history hP] at hi
  obtain ⟨br, _, hi⟩ := List.mem_flatMap.mp hi
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hi
  obtain ⟨t, ht, hi⟩ := List.mem_flatMap.mp hi
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hi
  exact List.mem_range.mp ht

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryHistoryBufferCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

theorem queryEarlierInputsWithWork_time {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (N P F exponent history : ℕ) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (q : TargetInterval ny)
    (input : Fin M × ℕ × TargetInterval ny)
    (hi : input ∈ (queryEarlierInputsWithWork M parent N P F exponent history hP a initial q).1) :
    input.2.1 < history := by
  simp only [queryEarlierInputsWithWork, queryOrderedHistoryInputsWithWork_value] at hi
  have hm := (mem_orderedInputs historyInputCode (historyInputCode_injective M ny) _ input).mp hi
  rw [List.mem_toFinset] at hm
  exact queryRawHistoryInputsWithWork_time M parent P history hP _ input hm

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryOnlineRangeCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Online source ranges are computed before their random draws. This
charges the actual band, coordinate set, two powers, and triangular mass. -/

namespace EditApproximation.BinaryFraction

theorem queryOnlineRangeWithWork_bounds {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P exponent H B R : ℕ) (hP : 0 < P)
    (tau : BinaryFraction) (child : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (key : ℕ × TargetInterval target.length)
    (hB : 2 ≤ B) (hnx : Nat.size source.length ≤ B) (hny : Nat.size target.length ≤ B)
    (hM : Nat.size M ≤ B) (hb : Nat.size key.1 ≤ B) (hPb : Nat.size P ≤ B)
    (he : exponent + 1 ≤ B) (hH : Nat.size H ≤ B)
    (hd : Nat.size (M * (40 * P + 2) ^ 2) ≤ B)
    (htau : tau.width ≤ B) (hchild : ∀ i q, (child i q).1.width ≤ B)
    (hR : ∀ i q, (child i q).2 ≤ R) :
    Nat.size (queryOnlineRangeWithWork parent P exponent H tau child key).1 ≤ 240 * (B + 4) + 7 ∧
    (queryOnlineRangeWithWork parent P exponent H tau child key).2 ≤ queryOnlineRangeBitBudget M P B R := by
  let V := (40 * P + 2) ^ (2 * M)
  let band := preparedRepresentativeReadWithWork parent key.2 (parent.hi - parent.lo) key.1 P
    tau (inversePowerTwo exponent) child
  let setup := onlineIndexSetupWithWork H band.1
  let power := bitPowerWithWork setup.1.bits 80
  let mass := triangularMassWithWork (bitWordValue power.1)
  have hvalue := (preparedRepresentativeReadWithWork_eq_cost parent key.2 (parent.hi - parent.lo)
    key.1 P tau (inversePowerTwo exponent) child R hR).1
  have hsemantic : band.1 = representativeBandActions source target parent key.2 key.1 P tau.value
      (inversePowerTwo exponent).value (fun i q => (child i q).1.value) := by
    exact hvalue.trans (preparedRepresentativeWithWork_value source target parent key.2 key.1 P hP
      tau (inversePowerTwo exponent) (fun i q => (child i q).1))
  have hlen : band.1.length ≤ V := by
    rw [hsemantic]
    exact (representativeBandActions_length_le source target parent key.2 key.1 P tau.value
      (inversePowerTwo exponent).value (fun i q => (child i q).1.value)).trans
      (wideActionList_length_le M parent key.2 key.1 P hP)
  have hdim : (listedBandCoordinates band.1).length ≤ M * (40 * P + 2) ^ 2 := by
    rw [listedBandCoordinates_length, hsemantic]
    exact bandCoordinates_card_le parent key.2 hP _
      (fun action ha => representativeBandActions_wide source target parent key.2 key.1 P tau.value
        (inversePowerTwo exponent).value (fun i q => (child i q).1.value) action ha)
  have hwide : (wideActionGridWithWork M parent key.2 key.1 P).1.length ≤ V := by
    have hh := congrArg List.length (wideActionGridWithWork_value M parent key.2 key.1 P hP)
    simp only [List.length_map] at hh
    rw [hh]
    exact wideActionList_length_le M parent key.2 key.1 P hP
  have hplain := preparedRepresentativeWithWork_complete_cost parent key.2 key.1 P B hP tau
    (inversePowerTwo exponent) (fun i q => (child i q).1) hnx hny hM hb hPb htau
    (by rw [inversePowerTwo_width]; exact he) hchild
  have hmono := representativeCompleteBitBudget_mono_vertices M _ V (4 * B + 20) hwide
  have hband := preparedRepresentativeReadWithWork_factor parent key.2 (parent.hi - parent.lo)
    key.1 P tau (inversePowerTwo exponent) child R hR
  have hbandCost : band.2 ≤
      (wideMaterializationBitBudget M P B + representativeCompleteBitBudget M V (4 * B + 20) + V + 1) *
        tableReadFactor R := by
    apply hband.trans
    apply Nat.mul_le_mul_right
    omega
  have hsetup := onlineIndexSetupWithWork_bounds H B band.1 hB hH hM hny
    ((Nat.size_le_size hdim).trans hd)
  have hsetupWork : setup.2 ≤ onlineIndexBitBudget M band.1.length B := by
    simpa only [setup] using hsetup.2
  have hsetupCost : setup.2 ≤ onlineIndexBitBudget M V B :=
    hsetupWork.trans (onlineIndexBitBudget_mono_vertices M B band.1.length V hlen)
  have hsetupSize : setup.1.bits.length ≤ B + 4 := by
    simpa only [setup, Nat.size_eq_bits_len] using hsetup.1
  have hpower : power.2 ≤ bitPowerBitBudget 80 (B + 4) := by
    simpa only [power] using bitPowerWithWork_cost setup.1.bits 80 (B + 4) hsetupSize
  have hpowerLength : power.1.length ≤ 80 * (B + 4) + 1 := by
    simpa only [power] using bitPowerWithWork_length_le setup.1.bits 80 (B + 4) hsetupSize
  have hpowerSize : Nat.size (bitWordValue power.1) ≤ 80 * (B + 4) + 1 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length power.1)).trans hpowerLength
  have hmass := triangularMassWithWork_bounds (bitWordValue power.1) (80 * (B + 4) + 1) hpowerSize
  have hmassLength : mass.1.length ≤ 3 * (80 * (B + 4) + 1) + 4 := by
    simpa only [mass] using hmass.1
  have hmassCost : mass.2 ≤ 10000 * (80 * (B + 4) + 4) ^ 2 := by
    simpa only [mass, Nat.add_assoc, Nat.reduceAdd] using hmass.2
  have hwidth : (saturatingSubtractWithWork parent.hi parent.lo).2 ≤ 26 * B + 4 := by
    have hhi := (Nat.size_le_size parent.valid).trans hnx
    have hlo := (Nat.size_le_size (parent.ordered.trans parent.valid)).trans hnx
    have hh := saturatingSubtractWithWork_cost parent.hi parent.lo
    omega
  constructor
  · have hm : Nat.size (bitWordValue mass.1) ≤ 3 * (80 * (B + 4) + 1) + 4 :=
      (Nat.size_le.mpr (bitWordValue_lt_pow_length mass.1)).trans hmassLength
    have hsize : Nat.size (bitWordValue mass.1) ≤ 240 * (B + 4) + 7 :=
      hm.trans_eq (by ring)
    simpa only [queryOnlineRangeWithWork, saturatingSubtractWithWork_value,
      band, setup, power, mass] using hsize
  · have hcost : (saturatingSubtractWithWork parent.hi parent.lo).2 +
        band.2 + setup.2 + power.2 + mass.2 + 4 ≤ queryOnlineRangeBitBudget M P B R := by
      have hsum := Nat.add_le_add_right
        (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hwidth hbandCost)
          hsetupCost) hpower) hmassCost) 4
      simpa only [queryOnlineRangeBitBudget, V] using hsum
    simpa only [queryOnlineRangeWithWork, saturatingSubtractWithWork_value,
      band, setup, power, mass] using hcost

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySourceWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact execution counters for both source gathers. The online counter
includes construction of every range before issuing its random read. -/

namespace EditApproximation

theorem queryGroupSourceGather_work {ι β : Type*} {n : ℕ}
    (M N F Q exponent eM eF : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
    (a : BinaryFraction) (initial : TargetInterval n → BinaryFraction × ℕ) (q : TargetInterval n)
    (reader : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
    (next : List (GroupScalarKey M F Q) → List BinaryFraction → BitQuery ι β)
    (oracle : ι → BinaryFraction) (readWork : ι → ℕ) :
    let keys := BinaryFraction.queryGroupSourceKeysWithWork M N F Q exponent eM eF hM hF a
      (initial q).1 q
    (queryGroupSourceGather M N F Q exponent eM eF hM hF a initial q reader next).work oracle readWork =
      (initial q).2 + keys.2 +
        (keys.1.map fun key => (reader key).work oracle readWork + 3).sum +
        (next keys.1 (keys.1.map fun key => (reader key).value oracle)).work oracle readWork := by
  simp only [queryGroupSourceGather, BitQuery.work_bind, BitQuery.work_collect,
    BitQuery.compute, BitQuery.work, BitQuery.value, Nat.add_zero, Nat.add_assoc]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySourceGatherCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

private theorem source_read_sum_bound {κ : Type*} (keys : List κ) (cost : κ → ℕ) (B : ℕ)
    (h : ∀ key ∈ keys, cost key ≤ B) : (keys.map cost).sum ≤ keys.length * B := by
  induction keys with
  | nil => simp
  | cons key keys ih =>
    have hh := h key List.mem_cons_self
    have ht := ih (fun k hk => h k (List.mem_cons_of_mem key hk))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

open BinaryFraction

theorem queryGroupSourceGather_work_bound {ι β : Type*} {n : ℕ}
    (M N F Q exponent eM eF B Rp W K : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
    (a : BinaryFraction) (initial : TargetInterval n → BinaryFraction × ℕ) (q : TargetInterval n)
    (reader : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
    (next : List (GroupScalarKey M F Q) → List BinaryFraction → BitQuery ι β)
    (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hFb : Nat.size F + 2 ≤ B)
    (hMb : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B) (hes : eM + eF + 7 ≤ B)
    (he : exponent + 1 ≤ B) (hn : Nat.size n ≤ B) (ha : a.width ≤ B)
    (hv : (initial q).1.width ≤ B) (hw : 0 ≤ (initial q).1.value) (hp : (initial q).2 ≤ Rp)
    (hr : ∀ key ∈ (queryGroupSourceKeysWithWork M N F Q exponent eM eF hM hF a (initial q).1 q).1,
      (reader key).work oracle readWork ≤ W)
    (hnext :
      let keys := (queryGroupSourceKeysWithWork M N F Q exponent eM eF hM hF a (initial q).1 q).1
      (next keys (keys.map fun key => (reader key).value oracle)).work oracle readWork ≤ K) :
    (queryGroupSourceGather M N F Q exponent eM eF hM hF a initial q reader next).work oracle readWork ≤
      queryGroupGatherBitBudget M F exponent eM eF B Rp W K := by
  let keys := queryGroupSourceKeysWithWork M N F Q exponent eM eF hM hF a (initial q).1 q
  have hk := queryGroupSourceKeysWithWork_bounds M N F Q exponent eM eF B hM hF a (initial q).1 q
    hB hN hFb hMb hQ hes he hn ha hv hw
  have hs := (source_read_sum_bound keys.1 (fun key => (reader key).work oracle readWork + 3) (W + 3)
    (fun key hkey => Nat.add_le_add_right (hr key hkey) 3)).trans (Nat.mul_le_mul_right _ hk.1)
  change (next keys.1 (keys.1.map fun key => (reader key).value oracle)).work oracle readWork ≤ K at hnext
  have hkc : keys.2 ≤ queryGroupSourceKeysBitBudget M F exponent eM eF B := hk.2
  rw [queryGroupSourceGather_work]
  change (initial q).2 + keys.2 + (keys.1.map fun key => (reader key).work oracle readWork + 3).sum +
    (next keys.1 (keys.1.map fun key => (reader key).value oracle)).work oracle readWork ≤ _
  unfold queryGroupGatherBitBudget
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalSourcesCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete random-source stage: source enumeration and range construction,
physical source reads, finite-buffer scans, and the inner local refinement. -/

namespace EditApproximation
section Sources
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF B E S : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (q : TargetInterval target.length)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (oracle : ι → BinaryFraction) (readWork : ι → ℕ)

open BinaryFraction

theorem queryLocalRandomSources_work_bound_oai (Rp W : ℕ)
    (htime : 0 < t) (ht : Nat.size t ≤ B) (hPd : ∃ j : ℕ, P = 2 ^ j)
    (hp : ∀ r, (parentInitial r).2 ≤ Rp)
    (hgW : ∀ key, ((readGroup key).value oracle).width ≤ B)
    (hzW : ∀ key range, ((readInteger key range).value oracle).width ≤ B)
    (heW : ∀ key, ((readEarlier key).value oracle).width ≤ B)
    (hcW : ∀ key, ((readCurrent key).value oracle).width ≤ B)
    (hgR : ∀ key, queryGroupKeySize key ≤ 40 * B + 500 →
      (readGroup key).work oracle readWork ≤ W)
    (hzR : ∀ key range, Nat.size key.1 ≤ B + 1 → Nat.size range ≤ 240 * (B + 5) + 7 →
      (readInteger key range).work oracle readWork ≤ W)
    (heR : ∀ key, Nat.size key.2.1 ≤ B → (readEarlier key).work oracle readWork ≤ W)
    (hcR : ∀ key, (readCurrent key).work oracle readWork ≤ W)
    (hb :
      let groupKeys := (queryGroupSourceKeysWithWork M N F Q exponent eM eF hM hF a (parentInitial q).1 q).1
      let groupWords := groupKeys.map fun key => (readGroup key).value oracle
      let onlineKeys := (queryOnlineKeysWithWork N P F hP a (parentInitial q).1 q).1
      let onlineWords := onlineKeys.map fun key =>
        (readInteger key (queryOnlineRangeWithWork parent P exponent H tau child key).1).value oracle
      let draw := queryGroupDrawReadWithWork groupKeys groupWords
      let integer := queryOnlineIntegerReadWithWork onlineKeys onlineWords
      let earlier := (queryEarlierInputsWithWork M parent N P F exponent t hP a parentInitial q).1
      let earlierWords := earlier.map fun key => (readEarlier key).value oracle
      let shared := (querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a
        (parentInitial q).1 q draw).1
      let sharedWords := shared.map fun key => (readCurrent key).value oracle
      PreparedKernelInputBounds (nx := source.length) N P F exponent H Q eM eF B E S (t - 1)
        tau a eta kappa delta (fun r => (parentInitial r).1)
        (fun i r => (child i r).1) (fun i r => (initial i r).1)
        (fun input => (queryHistoryReadWithWork earlier earlierWords (t - 1) input).1)
        (fun input => (queryChildReadWithWork shared sharedWords input.1 input.2).1)
        (fun s input => (queryHistoryReadWithWork earlier earlierWords s input).1)
        (fun b r => (integer b r).1)) :
    (queryLocalRandomSources source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta t parentInitial child initial R hc hi q
      readGroup readInteger readEarlier readCurrent).work oracle readWork ≤
      queryLocalSourcesBitBudget M N P F exponent eM eF B S t Rp R W := by
  let groupKeys := (queryGroupSourceKeysWithWork M N F Q exponent eM eF hM hF a (parentInitial q).1 q).1
  let groupWords := groupKeys.map fun key => (readGroup key).value oracle
  let onlineKeys := (queryOnlineKeysWithWork N P F hP a (parentInitial q).1 q).1
  let onlineWords := onlineKeys.map fun key =>
    (readInteger key (queryOnlineRangeWithWork parent P exponent H tau child key).1).value oracle
  let draw := queryGroupDrawReadWithWork groupKeys groupWords
  let integer := queryOnlineIntegerReadWithWork onlineKeys onlineWords
  have hB : 10 ≤ B := hb.largeBits
  have hnx : Nat.size source.length ≤ B := by have := hb.sourceSize; omega
  have hny : Nat.size target.length ≤ B := by have := hb.targetSize; omega
  have hMb : Nat.size M ≤ B := by have := hb.aritySize; omega
  have hFpos : 1 ≤ F := by rw [hF]; exact Nat.one_le_two_pow
  have hgw : ∀ w ∈ groupWords, w.width ≤ B := by
    intro w hw
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
    exact hgW key
  have how : ∀ w ∈ onlineWords, w.width ≤ B := by
    intro w hw
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
    exact hzW key _
  have hdg := queryBufferedGroupReadCost exponent eM eF B B hM hF a (parentInitial q).1 q groupWords
    (by omega) hb.inputSize hb.factorSize hb.aritySize hb.sampleSize
    (by have := hb.scaleSizes; omega) hb.thetaSize hny hb.factorWidth (hb.parentSize q)
    (hb.parentNonneg q) (by omega) hgw
  have hdo := queryBufferedOnlineReadCost N P F B B hP a (parentInitial q).1 q onlineWords
    (by omega) hb.inputSize hb.factorSize hFpos hb.precisionSize hny hb.factorWidth
    (hb.parentSize q) (by omega) how
  have hlocal := queryLocalRefinement_work_bound source target parent N P F exponent H Q eM eF B E S
    hP hM hF tau a eta kappa delta t parentInitial child initial R hc hi draw integer q
    readEarlier readCurrent oracle readWork Rp W _ _ htime ht hPd hp heW hcW
    (fun key hk => heR key ((Nat.size_le_size
      (queryEarlierInputsWithWork_time M parent N P F exponent t hP a parentInitial q key hk).le).trans ht))
    hcR hdg (fun e he _ => hdo e he) hb
  have hgCost : ∀ key ∈ groupKeys, (readGroup key).work oracle readWork ≤ W := by
    intro key hk
    apply hgR key
    exact queryGroupSourceKeysWithWork_width M N F Q exponent eM eF B hM hF a (parentInitial q).1 q
      (by omega) hb.inputSize hb.factorSize hMb (by have := hb.scaleSizes; omega)
      hb.thetaSize hny hb.factorWidth (hb.parentSize q) (hb.parentNonneg q) key hk
  have hzCost : ∀ key ∈ onlineKeys,
      (readInteger key (queryOnlineRangeWithWork parent P exponent H tau child key).1).work oracle readWork ≤ W := by
    intro key hk
    have hscale := queryOnlineKeysWithWork_scale N P F B hP a (parentInitial q).1 q
      hb.inputSize hFpos key hk
    apply hzR key _ hscale
    have hr := (queryOnlineRangeWithWork_bounds source target parent P exponent H (B + 1) R hP tau child key
      (by omega) (by omega) (by omega) (by omega) hscale (by have := hb.precisionSize; omega)
      (by have := hb.thetaSize; omega) (by have := hb.heightSize; omega)
      (by have := hb.coordinateSize; omega) (hb.tauSize.trans (by omega))
      (fun i r => (hb.massSize i r).trans (by omega)) hc).1
    simpa only [Nat.add_assoc] using hr
  unfold queryLocalRandomSources queryLocalSourcesBitBudget
  apply queryGroupSourceGather_work_bound M N F Q exponent eM eF B Rp W _ hM hF a parentInitial q
    readGroup _ oracle readWork (by omega) hb.inputSize hb.factorSize hb.aritySize hb.sampleSize
    (by have := hb.scaleSizes; omega) hb.thetaSize hny hb.factorWidth (hb.parentSize q)
    (hb.parentNonneg q) (hp q) hgCost
  apply queryOnlineSourceGather_work_bound source target parent N P F exponent H B Rp R W _ hP tau a
    parentInitial child q readInteger _ oracle readWork (by omega) hb.inputSize hb.factorSize hFpos
    hMb hb.precisionSize hb.thetaSize hnx hny hb.heightSize hb.coordinateSize hb.tauSize hb.factorWidth
    (hb.parentSize q) (hp q) hb.massSize hc hzCost
  exact hlocal

end Sources
end EditApproximation

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.EditApproximation.queryLocalRandomSources_work_bound_oai.{u_1, u_2} := @OAI.EditApproximation.queryLocalRandomSources_work_bound_oai.{u_1, u_2}
