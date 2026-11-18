-- Prove2me | solution 1 for OAI.EditApproximation.computedQueryParameters_numeric
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:23:23.202725+00:00
-- url     : https://prove2.me/submissions/50c2a081-17d1-4d82-8be3-29f8fe1837de

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
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
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_OAIQ361V3Ea000
import Definitions.Def_OAIQ361V3Ea001

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



end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupSetup
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



theorem signedPowerTwoWithWork_width (e : ℤ) :
    (signedPowerTwoWithWork e).1.width ≤ e.natAbs + 1 := by
  unfold signedPowerTwoWithWork
  split_ifs with h
  · simp only [width, powerTwoWord_length, List.length_cons, List.length_nil]
    have hs := Int.toNat_add_toNat_neg_eq_natAbs e
    have he : e.toNat ≤ e.natAbs := by omega
    omega
  · rw [inversePowerTwo_width]
    have hs := Int.toNat_add_toNat_neg_eq_natAbs e
    have he : (-e).toNat ≤ e.natAbs := by omega
    omega



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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryOnlineParameters
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The two numerical constants used by online optimization are built from
the binary small-log parameter. Their word widths and construction costs
come from the actual multiplication loops. -/

namespace EditApproximation
namespace BinaryFraction



theorem onlineParametersWithWork_eta (ell : List Bool) (hell : 0 < bitWordValue ell) :
    (onlineParametersWithWork ell hell).1.1.value = (rationalParameters (bitWordValue ell)).eta := by
  simp [onlineParametersWithWork, value, SignedBinary.value, signedMagnitude,
    bitPowerWithWork_value, bitWordValue, rationalParameters]

theorem onlineParametersWithWork_kappa (ell : List Bool) (hell : 0 < bitWordValue ell) :
    (onlineParametersWithWork ell hell).1.2.value = (rationalParameters (bitWordValue ell)).kappa := by
  simp [onlineParametersWithWork, value, SignedBinary.value, signedMagnitude,
    bitPowerWithWork_value, bitWordValue, rationalParameters]

theorem onlineParametersWithWork_width (ell : List Bool) (hell : 0 < bitWordValue ell)
    (B : ℕ) (hB : ell.length ≤ B) :
    (onlineParametersWithWork ell hell).1.1.width ≤ 5 * B + 1 ∧
      (onlineParametersWithWork ell hell).1.2.width ≤ 4 * B + 1 := by
  have he := bitPowerWithWork_length_le ell 5 B hB
  have hk := bitPowerWithWork_length_le ell 4 B hB
  simp only [onlineParametersWithWork, width, List.length_cons, List.length_nil]
  constructor <;> omega

theorem onlineParametersWithWork_range (ell : List Bool) (hell : 0 < bitWordValue ell)
    (H : ℕ) (hH : bitWordValue ell ≤ H) :
    |(onlineParametersWithWork ell hell).1.1.value| ≤ ((H ^ 5 : ℕ) : ℚ) ∧
      0 ≤ (onlineParametersWithWork ell hell).1.2.value ∧
      (onlineParametersWithWork ell hell).1.2.value ≤ 1 := by
  rw [onlineParametersWithWork_eta, onlineParametersWithWork_kappa]
  simp only [rationalParameters]
  have hn : (0 : ℚ) ≤ bitWordValue ell := Nat.cast_nonneg _
  have hp : (1 : ℚ) ≤ bitWordValue ell := by exact_mod_cast hell
  constructor
  · rw [abs_of_nonneg (pow_nonneg hn _), Nat.cast_pow]
    exact pow_le_pow_left₀ hn (by exact_mod_cast hH) _
  constructor
  · exact div_nonneg (by norm_num) (pow_nonneg hn _)
  · exact (div_le_one (pow_pos (lt_of_lt_of_le (by norm_num) hp) _)).mpr
      (one_le_pow₀ hp)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRefinementParameters
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The decrement is constructed on the same Boolean words as the online
constants. In particular no rational literal or uncharged inversion is
needed at a local refinement entry. -/

namespace EditApproximation
namespace BinaryFraction



theorem refinementDecrementWithWork_width (ell : List Bool) (hell : 0 < bitWordValue ell)
    (B : ℕ) (hB : ell.length ≤ B) : (refinementDecrementWithWork ell hell).1.width ≤ 10 * B + 1 := by
  have h := bitPowerWithWork_length_le ell 10 B hB
  simp only [refinementDecrementWithWork, width, List.length_cons, List.length_nil]
  exact max_le (by omega) h

theorem refinementDecrementWithWork_cost (ell : List Bool) (hell : 0 < bitWordValue ell)
    (B : ℕ) (hB : ell.length ≤ B) :
    (refinementDecrementWithWork ell hell).2 ≤ bitPowerBitBudget 10 B + 1 :=
  Nat.add_le_add_right (bitPowerWithWork_cost ell 10 B hB) 1

theorem refinementDecrementWithWork_cap (ell : List Bool) (hell : 0 < bitWordValue ell)
    (H : ℕ) (hH : 64 ≤ H) (hwidth : ell.length ≤ H) :
    (refinementDecrementWithWork ell hell).1.width ≤ H ^ 2 ∧
      (refinementDecrementWithWork ell hell).2 ≤ H ^ 8 := by
  constructor
  · exact (refinementDecrementWithWork_width ell hell H hwidth).trans (by nlinarith only [hH])
  · have h := refinementDecrementWithWork_cost ell hell H hwidth
    have hsmall : 11 * (H + 1) + 1 ≤ 12 * H := by omega
    have hsq := Nat.pow_le_pow_left hsmall 2
    have hnum : bitPowerBitBudget 10 H + 1 ≤ 300000 * H ^ 2 := by
      unfold bitPowerBitBudget
      nlinarith only [hsq, hH]
    have hc : 300000 ≤ H ^ 6 :=
      (by norm_num : 300000 ≤ (64 : ℕ) ^ 6).trans (Nat.pow_le_pow_left hH 6)
    exact h.trans (hnum.trans (by
      calc
        300000 * H ^ 2 ≤ H ^ 6 * H ^ 2 := Nat.mul_le_mul_right _ hc
        _ = H ^ 8 := by ring))

end BinaryFraction
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedEarlierInputBudget
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCacheWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit multiword cache storage after substituting the computed height. -/

namespace EditApproximation

theorem computed_input_size_le_height (N : ℕ) : Nat.size N ≤ inputHeight N := by
  apply Nat.size_le.mpr
  exact (show N < N + 2 by omega).trans_le (inputHeight_covers_length N)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedBinaryOnlineParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual binary online constants fit the same polynomial word cap as
the normalized local cache. No input-probability or good-seed assumption is
used here. -/

namespace EditApproximation

private theorem online_parameter_width_cap (H B : ℕ) (hH : 64 ≤ H) (hB : B ≤ H) :
    5 * B + 1 ≤ H ^ 2 ∧ 4 * B + 1 ≤ H ^ 2 := by
  constructor <;> nlinarith

theorem computedBinaryOnlineParameters_caps (N : ℕ) (word : List Bool)
    (hvalue : bitWordValue word = inputSmallLog N)
    (hwidth : word.length ≤ Nat.size (inputSmallLog N)) (hH : 64 ≤ inputHeight N)
    (hpositive : 0 < bitWordValue word) :
    (BinaryFraction.onlineParametersWithWork word hpositive).1.1.width ≤ inputHeight N ^ 2 ∧
      (BinaryFraction.onlineParametersWithWork word hpositive).1.2.width ≤ inputHeight N ^ 2 ∧
      |(BinaryFraction.onlineParametersWithWork word hpositive).1.1.value| ≤
        ((inputHeight N ^ 5 : ℕ) : ℚ) ∧
      0 ≤ (BinaryFraction.onlineParametersWithWork word hpositive).1.2.value ∧
      (BinaryFraction.onlineParametersWithWork word hpositive).1.2.value ≤ 1 := by
  have hsmall : Nat.size (inputSmallLog N) ≤ inputHeight N :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (computed_smallLog_le_height N)
  have hw := BinaryFraction.onlineParametersWithWork_width word hpositive
    (Nat.size (inputSmallLog N)) hwidth
  have hr := BinaryFraction.onlineParametersWithWork_range word hpositive (inputHeight N)
    (by rw [hvalue]; exact computed_smallLog_le_height N)
  have hc := online_parameter_width_cap _ _ hH hsmall
  exact ⟨hw.1.trans hc.1, hw.2.trans hc.2, hr.1, hr.2⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedNumericalParameters
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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedPreparedInputBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter

private theorem precision_power_bound (p : ℕ) : p + 20 ≤ 8000 * (p + 1) := by omega

private theorem prepared_loop_caps (H M P p : ℕ) (hH : 64 ≤ H)
    (hM : M ≤ H) (hP : 1 ≤ P) (hPcap : P ≤ H ^ (p + 20)) :
    (40 * P + 2) ^ (2 * M) ≤ H ^ ((100 * M + 100000) * (p + 1)) ∧
    ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ H ^ ((100 * M + 100000) * (p + 1)) ∧
    (H + M * (40 * P + 2) ^ 2 + 2) ^ 80 ≤ H ^ ((100 * M + 100000) * (p + 1)) := by
  have hHp : 0 < H := by omega
  have hbox : 40 * P + 2 ≤ H ^ (p + 22) := by
    calc
      _ ≤ 42 * P := by omega
      _ ≤ H ^ 2 * H ^ (p + 20) := Nat.mul_le_mul (by nlinarith only [hH]) hPcap
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hbase : (40 * P + 2) ^ 2 + 1 ≤ H ^ (2 * (p + 22) + 1) := by
    have hs := Nat.pow_le_pow_left hbox 2
    have hunit : 1 ≤ (H ^ (p + 22)) ^ 2 := one_le_pow₀ (one_le_pow₀ (by omega))
    calc
      _ ≤ 2 * (H ^ (p + 22)) ^ 2 := by omega
      _ ≤ H * (H ^ (p + 22)) ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by rw [← pow_mul, ← pow_succ']; congr 1; omega
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ (H ^ (p + 22)) ^ (2 * M) := Nat.pow_le_pow_left hbox _
      _ = H ^ ((p + 22) * (2 * M)) := (pow_mul H _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right hHp (by nlinarith only [Nat.zero_le (M * p), Nat.zero_le p, Nat.zero_le M])
  · calc
      _ ≤ (H ^ (2 * (p + 22) + 1)) ^ (M + 1) := Nat.pow_le_pow_left hbase _
      _ = H ^ ((2 * (p + 22) + 1) * (M + 1)) := (pow_mul H _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right hHp (by nlinarith only [Nat.zero_le (M * p), Nat.zero_le p, Nat.zero_le M])
  · have hg := optimizer_parameter_budget_le H M P p hH hM hP hPcap
    calc
      _ ≤ (H ^ (2 * p + 46)) ^ 80 := Nat.pow_le_pow_left (by omega) 80
      _ = H ^ ((2 * p + 46) * 80) := (pow_mul H _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right hHp (by nlinarith only [Nat.zero_le (M * p), Nat.zero_le p, Nat.zero_le M])

/-- Every numeric premise of the prepared kernel follows from the computed
parameters. Width assumptions here concern only the five actual parameter
words; cached data are added by `physicalPreparedStep_inputBounds`. -/
theorem computedPreparedNumericBounds :
    ∀ᶠ N : ℕ in atTop, ∀ nx ny : ℕ, nx + ny ≤ N → ∀ t : ℕ, t ≤ inputHeight N ^ 2 →
      ∀ tau a eta kappa delta : BinaryFraction,
      tau.width ≤ inputHeight N ^ 8 → a.width ≤ inputHeight N ^ 8 →
      eta.width ≤ inputHeight N ^ 8 → kappa.width ≤ inputHeight N ^ 8 →
      delta.width ≤ inputHeight N ^ 8 → |eta.value| ≤ ((inputHeight N ^ 5 : ℕ) : ℚ) →
      (0 ≤ kappa.value ∧ kappa.value ≤ 1) →
      ∀ integer : ℕ → TargetInterval ny → ℕ,
      (∀ b r, Nat.size (integer b r) ≤ inputHeight N) →
      BinaryFraction.PreparedKernelNumericBounds (nx := nx) (M := (integerParameters N).M)
        N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
        (inputHeight N) (inputSmallLog N ^ 80) (heightExponent N / 20) (smallLogExponent N)
        (inputHeight N ^ 8) (inputHeight N ^ 5)
        (inputHeight N ^ ((100 * (integerParameters N).M + 100000) *
          (coarseExponent (inputSmallLog N) + 1))) t tau a eta kappa delta integer := by
  filter_upwards [computedParameterPower_word,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 64)] with N hpower hell
  intro nx ny hsize t ht tau a eta kappa delta htau ha heta hk hd hrate hkRange integer hint
  let H := inputHeight N
  let p := coarseExponent (inputSmallLog N)
  let M := (integerParameters N).M
  let P := (integerParameters N).P
  let L := (100 * M + 100000) * (p + 1)
  have hpowers : ∀ k : ℕ, k ≤ 8000 * (p + 1) → Nat.size (H ^ k) ≤ H := hpower
  change BinaryFraction.PreparedKernelNumericBounds (nx := nx) (M := M)
    N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80)
    (heightExponent N / 20) (smallLogExponent N) (H ^ 8) (H ^ 5) (H ^ L) t
    tau a eta kappa delta integer
  have hH : 64 ≤ H := hell.trans (computed_smallLog_le_height N)
  have hHp : 0 < H := by omega
  have hM : M ≤ H := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.div_le_self _ _)
  have hP : 1 ≤ P := one_le_pow₀ (by omega)
  have hPcap : P ≤ H ^ (p + 20) := le_rfl
  have hH8 : H ^ 2 ≤ H ^ 8 := Nat.pow_le_pow_right hHp (by decide)
  have hsmall : H + 2 ≤ H ^ 8 := (by nlinarith only [hH] : H + 2 ≤ H ^ 2).trans hH8
  have hHle : H ≤ H ^ 8 := by omega
  have hL : p + 20 ≤ L := by dsimp only [L]; nlinarith only [Nat.zero_le (M * p), Nat.zero_le M, Nat.zero_le p]
  have hL20 : 20 ≤ L := (Nat.le_add_left 20 p).trans hL
  have hHL : H ≤ H ^ L := Nat.le_pow (by omega)
  have hsizeN : Nat.size N ≤ H := computed_input_size_le_height N
  have hMF : Nat.size M ≤ H := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hM
  have hF : Nat.size (inputSmallLog N) ≤ H :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (computed_smallLog_le_height N)
  have hPs : Nat.size P ≤ H := by
    change Nat.size (H ^ (p + 20)) ≤ H
    exact hpowers (p + 20) (precision_power_bound p)
  have hQs : Nat.size (inputSmallLog N ^ 80) ≤ H :=
    (Nat.size_le_size (Nat.pow_le_pow_left (computed_smallLog_le_height N) 80)).trans
      (hpowers 80 (by omega))
  have he : smallLogExponent N ≤ H :=
    (Nat.lt_two_pow_self.le : smallLogExponent N ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  have htheta : 40 * smallLogExponent N + 1 ≤ H ^ 8 :=
    (by nlinarith only [he, hH] : 40 * smallLogExponent N + 1 ≤ H ^ 2).trans hH8
  have hscale : heightExponent N / 20 + smallLogExponent N + 7 ≤ H ^ 8 := by
    have heM : heightExponent N / 20 ≤ H :=
      (Nat.div_le_self _ _).trans Nat.lt_two_pow_self.le
    exact (by nlinarith only [heM, he, hH] :
      heightExponent N / 20 + smallLogExponent N + 7 ≤ H ^ 2).trans hH8
  have hcoord : Nat.size (M * (40 * P + 2) ^ 2) ≤ H :=
    (Nat.size_le_size (wide_coordinate_budget_le H M P p hH hM hP hPcap)).trans
      (hpowers (2 * p + 45) (by omega))
  have hiter : Nat.size ((H + M * (40 * P + 2) ^ 2 + 2) ^ 80) ≤ H := by
    have hg := optimizer_parameter_budget_le H M P p hH hM hP hPcap
    have hi : (H + M * (40 * P + 2) ^ 2 + 2) ^ 80 ≤ H ^ ((2 * p + 46) * 80) := by
      calc
        _ ≤ (H ^ (2 * p + 46)) ^ 80 := Nat.pow_le_pow_left (by omega) 80
        _ = _ := (pow_mul H _ _).symm
    exact (Nat.size_le_size hi).trans (hpowers ((2 * p + 46) * 80) (by omega))
  have hcaps := prepared_loop_caps H M P p hH hM hP hPcap
  have hword : 3 * (H ^ 8 + 4) + 4 ≤ H ^ L := by
    have hunit : 1 ≤ H ^ 8 := one_le_pow₀ (by omega)
    calc
      _ ≤ 19 * H ^ 8 := by omega
      _ ≤ H ^ 2 * H ^ 8 := Nat.mul_le_mul_right _ (by nlinarith only [hH])
      _ = H ^ 10 := by rw [← pow_add]
      _ ≤ _ := Nat.pow_le_pow_right hHp (by omega)
  refine {
    largeBits := (by nlinarith only [hH] : 10 ≤ H ^ 2).trans hH8
    inputSize := hsizeN.trans hHle
    sourceSize := (Nat.add_le_add_right (Nat.size_le_size (show nx ≤ N by omega) |>.trans hsizeN) 2).trans hsmall
    targetSize := (Nat.add_le_add_right (Nat.size_le_size (show ny ≤ N by omega) |>.trans hsizeN) 2).trans hsmall
    aritySize := (Nat.add_le_add_right hMF 2).trans hsmall
    precisionSize := hPs.trans hHle
    factorSize := (Nat.add_le_add_right hF 2).trans hsmall
    sampleSize := (Nat.add_le_add_right hQs 2).trans hsmall
    thetaSize := htheta
    scaleSizes := hscale
    heightSize := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hHle
    coordinateSize := hcoord.trans hHle
    iterationSize := hiter.trans hHle
    drawSize := fun b r => (hint b r).trans hHle
    tauSize := htau
    factorWidth := ha
    rateSize := heta
    optimismSize := hk
    decrementSize := hd
    rateMagnitude := hrate
    optimismRange := hkRange
    scalePositive := ?_
    arityCap := hM.trans ?_
    precisionCap := hPcap.trans (Nat.pow_le_pow_right hHp hL)
    rateCap := Nat.pow_le_pow_right hHp (by omega)
    timeCap := ht.trans (Nat.pow_le_pow_right hHp (by omega))
    wordCap := hword
    actionCap := hcaps.1
    cartesianCap := hcaps.2.1
    iterationCap := hcaps.2.2 }
  · exact (by omega : 2 ≤ H).trans hHL
  · exact hHL

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedRefinementWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

theorem scheduledRefinementWordWithWork_bounds (N pass : ℕ) (hH : 64 ≤ inputHeight N) :
    (scheduledRefinementWordWithWork N pass).1.width ≤ inputHeight N ^ 3 ∧
      (scheduledRefinementWordWithWork N pass).2 ≤ inputHeight N ^ 3 := by
  let H := inputHeight N
  change (scheduledRefinementWordWithWork N pass).1.width ≤ H ^ 3 ∧
    (scheduledRefinementWordWithWork N pass).2 ≤ H ^ 3
  have hp : coarseExponent (inputSmallLog N) ≤ H :=
    (coarseExponent_le_smallLog N).trans (computed_smallLog_le_height N)
  have he : heightExponent N ≤ H := Nat.lt_two_pow_self.le
  have hinitial : computedSeedInitialExponent N + 8 ≤ H ^ 3 := by
    unfold computedSeedInitialExponent
    have hm := Nat.mul_le_mul (Nat.add_le_add_right hp 4) he
    change 64 ≤ H at hH
    have hc : 3 * H ^ 2 ≤ H ^ 3 := by
      calc
        _ ≤ H * H ^ 2 := Nat.mul_le_mul_right (H ^ 2) (show 3 ≤ H by omega)
        _ = _ := by ring
    nlinarith only [hm, hH, hc]
  unfold scheduledRefinementWordWithWork
  split_ifs
  · have he' : dyadicSeedExponent (smallLogExponent N) (computedSeedInitialExponent N) pass -
        smallLogExponent N ≤ computedSeedInitialExponent N :=
      (Nat.sub_le _ _).trans (Nat.sub_le _ _)
    have hw := BinaryFraction.signedPowerTwoWithWork_width
      ((dyadicSeedExponent (smallLogExponent N) (computedSeedInitialExponent N) pass - smallLogExponent N : ℕ) : ℤ)
    simp only [Int.natAbs_natCast] at hw
    constructor
    · exact hw.trans (by omega)
    · simp only [BinaryFraction.signedPowerTwoWithWork, Int.natCast_nonneg, ite_true, if_true, Int.toNat_natCast]
      omega
  · have hw := BinaryFraction.nat_width_le 1
    have h3 : 3 ≤ H ^ 3 := (by omega : 3 ≤ H).trans (Nat.le_pow (by decide))
    exact ⟨hw.trans (by simpa only [Nat.size_one] using h3), h3⟩

/-- Width and range bounds for all five constructed scalar words. Tau and
kappa share the same reciprocal fourth-power word. -/
theorem computedRefinementWords_bounds (N pass : ℕ) (word : List Bool)
    (hvalue : bitWordValue word = inputSmallLog N)
    (hwidth : word.length ≤ Nat.size (inputSmallLog N))
    (hH : 64 ≤ inputHeight N) (hpositive : 0 < bitWordValue word) :
    let parameters := BinaryFraction.onlineParametersWithWork word hpositive
    parameters.1.2.width ≤ inputHeight N ^ 8 ∧
    (scheduledRefinementWordWithWork N pass).1.width ≤ inputHeight N ^ 8 ∧
    parameters.1.1.width ≤ inputHeight N ^ 8 ∧
    (BinaryFraction.refinementDecrementWithWork word hpositive).1.width ≤ inputHeight N ^ 8 ∧
    |parameters.1.1.value| ≤ ((inputHeight N ^ 5 : ℕ) : ℚ) ∧
    0 ≤ parameters.1.2.value ∧ parameters.1.2.value ≤ 1 := by
  have hc := computedBinaryOnlineParameters_caps N word hvalue hwidth hH hpositive
  have hword : word.length ≤ inputHeight N := hwidth.trans
    ((Nat.size_le.mpr Nat.lt_two_pow_self).trans (computed_smallLog_le_height N))
  have hd := (BinaryFraction.refinementDecrementWithWork_cap word hpositive (inputHeight N) hH hword).1
  have ha := (scheduledRefinementWordWithWork_bounds N pass hH).1
  have h2 : inputHeight N ^ 2 ≤ inputHeight N ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have h3 : inputHeight N ^ 3 ≤ inputHeight N ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  exact ⟨hc.2.1.trans h2, ha.trans h3, hc.1.trans h2, hd.trans h2, hc.2.2⟩



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedPreparedWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter

/-- The numeric record is inhabited by the actual constructed scalar words. -/
theorem computedPreparedWords_numeric :
    ∀ᶠ N : ℕ in atTop, ∀ nx ny : ℕ, nx + ny ≤ N → ∀ t : ℕ, t ≤ inputHeight N ^ 2 →
      ∀ (pass : ℕ) (word : List Bool) (hpositive : 0 < bitWordValue word),
      bitWordValue word = inputSmallLog N → word.length ≤ Nat.size (inputSmallLog N) →
      ∀ integer : ℕ → TargetInterval ny → ℕ,
      (∀ b r, Nat.size (integer b r) ≤ inputHeight N) →
      let values := (refinementParameterWordsWithWork N pass word hpositive).1
      BinaryFraction.PreparedKernelNumericBounds (nx := nx) (M := (integerParameters N).M)
        N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
        (inputHeight N) (inputSmallLog N ^ 80) (heightExponent N / 20) (smallLogExponent N)
        (inputHeight N ^ 8) (inputHeight N ^ 5)
        (inputHeight N ^ ((100 * (integerParameters N).M + 100000) *
          (coarseExponent (inputSmallLog N) + 1))) t
        values.tau values.factor values.eta values.kappa values.delta integer := by
  filter_upwards [computedPreparedNumericBounds,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 64)] with N hn hell
  intro nx ny hsize t ht pass word hpositive hvalue hwidth integer hint
  have hH : 64 ≤ inputHeight N := hell.trans (computed_smallLog_le_height N)
  have hw := computedRefinementWords_bounds N pass word hvalue hwidth hH hpositive
  exact hn nx ny hsize t ht _ _ _ _ _ hw.1 hw.2.1 hw.2.2.1 hw.1 hw.2.2.2.1
    hw.2.2.2.2.1 hw.2.2.2.2.2 integer hint

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryConstants
attribute [-simp] _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter

/-- The prepared record for the precise shared constants used by the memo. -/
theorem computedQueryParameters_numeric_oai :
    ∀ᶠ N : ℕ in atTop, ∀ nx ny, nx + ny ≤ N → ∀ t, t ≤ inputHeight N ^ 2 → ∀ pass,
      BinaryFraction.PreparedKernelNumericBounds (nx := nx) (ny := ny) (M := (integerParameters N).M)
        N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
        (inputHeight N) (inputSmallLog N ^ 80) (heightExponent N / 20) (smallLogExponent N)
        (inputHeight N ^ 8) (inputHeight N ^ 5)
        (inputHeight N ^ ((100 * (integerParameters N).M + 100000) *
          (coarseExponent (inputSmallLog N) + 1))) t
        (computedQueryParameters N 0).tau (computedQueryParameters N pass).factor
        (computedQueryParameters N 0).eta (computedQueryParameters N 0).kappa
        (computedQueryParameters N 0).delta (fun _ _ => 0) := by
  filter_upwards [computedPreparedWords_numeric] with N hn
  intro nx ny hsize t ht pass
  exact hn nx ny hsize t ht pass (inputSmallLog N).bits _ (bitWordValue_bits _)
    (by rw [← Nat.size_eq_bits_len]) (fun _ _ => 0) (by intros; simp)

end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.computedQueryParameters_numeric_oai := @OAI.EditApproximation.computedQueryParameters_numeric_oai
