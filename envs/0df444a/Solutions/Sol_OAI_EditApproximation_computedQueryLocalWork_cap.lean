-- Prove2me | solution 1 for OAI.EditApproximation.computedQueryLocalWork_cap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:23:58.883492+00:00
-- url     : https://prove2.me/submissions/be56d0ed-ce8f-4288-8b75-a01107b4e0b3

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
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_EditApproxScheme_16
import Definitions.Def_OAIQ361V3Ea002
import Theorems.Thm_OAI_EditApproximation_computedQueryMemoNormalized_correct
import Theorems.Thm_OAI_EditApproximation_computedQueryMemoNormalized_width
import Theorems.Thm_OAI_EditApproximation_computedQueryTable_work_width

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_CanonicalFractionWork
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
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



theorem canonicalizeWithWork_cost (a : BinaryFraction) :
    (canonicalizeWithWork a).2 ≤ 6 * a.width + 4 := by
  have hn : a.numerator.bits.length ≤ a.width := le_max_left _ _
  have hd : a.denominator.length ≤ a.width := le_max_right _ _
  simp only [canonicalizeWithWork, trimBitWordWithWork_cost]
  omega





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
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
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

theorem fixedDenominatorWithWork_cost (a : BinaryFraction) (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) (A B : ℕ)
    (ha : a.width ≤ A) (hB : denominator.length ≤ B) :
    (fixedDenominatorWithWork a denominator hden).2 ≤ 5000 * (A + B + 2) ^ 2 := by
  let product := bitMulWithWork a.numerator.bits denominator
  let quotient := bitDivModWithWork a.denominator product.1
  let raw : BinaryFraction := ⟨⟨a.numerator.negative, quotient.1⟩, denominator, hden⟩
  have hn : a.numerator.bits.length ≤ A := (le_max_left _ _).trans ha
  have hd : a.denominator.length ≤ A := (le_max_right _ _).trans ha
  have hp := bitMulWithWork_cost a.numerator.bits denominator
  have hpl := bitMulWithWork_length a.numerator.bits denominator
  have hq := bitDivModWithWork_cost a.denominator product.1
  have hql := (bitDivModWithWork_lengths a.denominator product.1).1
  change product.1.length ≤ 2 * a.numerator.bits.length + denominator.length + 1 at hpl
  change quotient.1.length = product.1.length at hql
  have hraw : raw.width ≤ 2 * A + B + 1 := by
    change max quotient.1.length denominator.length ≤ _
    exact max_le (by omega) (by omega)
  have hc := canonicalizeWithWork_cost raw
  change product.2 + quotient.2.2 + (canonicalizeWithWork raw).2 + 4 ≤ _
  have hprod : product.2 ≤ 20 * (A + B + 2) ^ 2 := by
    apply hp.trans
    have h1 : a.numerator.bits.length + 1 ≤ A + B + 2 := by omega
    have h2 : a.numerator.bits.length + denominator.length + 1 ≤ A + B + 2 := by omega
    nlinarith only [Nat.mul_le_mul h1 h2]
  have hquot : quotient.2.2 ≤ 30 * (3 * (A + B + 2)) * (4 * (A + B + 2)) := by
    apply hq.trans
    have h1 : product.1.length + 1 ≤ 3 * (A + B + 2) := by omega
    have h2 : product.1.length + a.denominator.length + 1 ≤ 4 * (A + B + 2) := by omega
    nlinarith only [Nat.mul_le_mul h1 h2]
  nlinarith only [hprod, hquot, hc, hraw, Nat.zero_le A, Nat.zero_le B]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPowerStorage
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
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



theorem refinementBaseWithWork_length (ell : List Bool) :
    (refinementBaseWithWork ell).1.length = Nat.size (bitWordValue ell ^ 10 + 1) := by
  simp only [refinementBaseWithWork, trimBitWordWithWork_length, bitAddWithWork_value,
    bitPowerWithWork_value, bitWordValue, Bool.toNat_true, Bool.toNat_false]

namespace BinaryFraction



theorem powerDenominatorWithWork_cost (a : BinaryFraction) (base : List Bool)
    (hbase : 0 < bitWordValue base) (n A B : ℕ) (ha : a.width ≤ A) (hB : base.length ≤ B) :
    (powerDenominatorWithWork a base hbase n).2 ≤ powerDenominatorBitBudget n A B := by
  have hp := bitPowerWithWork_cost base n B hB
  have hf := fixedDenominatorWithWork_cost a (bitPowerWithWork base n).1
    (by rw [bitPowerWithWork_value]; exact Nat.pow_pos hbase) A (n * B + 1)
    ha (bitPowerWithWork_length_le base n B hB)
  change (bitPowerWithWork base n).2 + (fixedDenominatorWithWork a (bitPowerWithWork base n).1 _).2 + 1 ≤ _
  unfold powerDenominatorBitBudget
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_TreeParameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Depth of the computed interval tree

The branching factor is the power of two prescribed by the algorithm.
Ceiling logarithms count physical levels, including empty intervals.
-/

namespace EditApproximation

open Finset



theorem computed_branching_bounds (N : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) :
    2 ≤ (integerParameters N).M ∧
      inputSmallLog N ≤ 50 * (heightExponent N / 20) ∧
      heightExponent N / 20 ≤ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hquot := Nat.mod_lt (heightExponent N) (by decide : 0 < 20)
  have hsplit := Nat.mod_add_div (heightExponent N) 20
  have hk : 1 ≤ heightExponent N / 20 := by omega
  have hpow : 2 ≤ 2 ^ (heightExponent N / 20) := by
    simpa using pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hk
  have hexp : heightExponent N ≤ inputHeight N := by
    exact (Nat.lt_pow_self (by decide : 1 < 2)).le
  exact ⟨hpow, by omega, (Nat.div_le_self _ _).trans hexp⟩

theorem computed_tree_depth_bound (N nx : ℕ) (hN : 0 < N) (hnx : nx ≤ N)
    (hell : 200 ≤ inputSmallLog N) :
    intervalTreeDepth (integerParameters N).M nx * inputSmallLog N ≤ 100 * inputHeight N := by
  let k := heightExponent N / 20
  have hbranch := computed_branching_bounds N hN hell
  have hbound : max 1 nx ≤ 2 ^ inputHeight N := by
    apply max_le Nat.one_le_two_pow
    exact hnx.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N))
  have hlog : Nat.clog 2 (max 1 nx) ≤ inputHeight N :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 hbound
  have hdepth : intervalTreeDepth (integerParameters N).M nx =
      (Nat.clog 2 (max 1 nx) + (k - 1)) / k := by
    exact Nat.clog_pow_left 2 k (max 1 nx)
  have hproduct := Nat.div_mul_le_self (Nat.clog 2 (max 1 nx) + (k - 1)) k
  rw [← hdepth] at hproduct
  have hscale := Nat.mul_le_mul_left
    (intervalTreeDepth (integerParameters N).M nx) hbranch.2.1
  change intervalTreeDepth (integerParameters N).M nx * inputSmallLog N ≤
    intervalTreeDepth (integerParameters N).M nx * (50 * k) at hscale
  have hkH : k ≤ inputHeight N := hbranch.2.2
  have hsub : k - 1 ≤ k := Nat.sub_le _ _
  nlinarith

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


end BitQuery
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitQueryKeys
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Key tagging and finite-domain restriction preserve the adaptive
reference program. Executed key tests carry their actual Boolean cost. -/

namespace EditApproximation.BitQuery



theorem mapKeysWithWork_work {ι κ β : Type*} (f : ι → κ × ℕ)
    (program : BitQuery ι β) (oracle : κ → BinaryFraction) (readWork : κ → ℕ) :
    (mapKeysWithWork f program).work oracle readWork =
      program.work (fun key => oracle (f key).1) (fun key => (f key).2 + readWork (f key).1) := by
  induction program with
  | done result => rfl
  | charge steps next ih => exact congrArg (steps + ·) ih
  | read key next ih =>
    simp only [mapKeysWithWork, work, ih, Nat.add_assoc]



end EditApproximation.BitQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitQueryNormalize
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Executed cache normalization charges the actual Boolean rescaling.
Its exact-value premise is checked on the reachable local result. -/

namespace EditApproximation.BitQuery



theorem normalize_work {ι : Type*} (program : BitQuery ι BinaryFraction)
    (base : List Bool) (hbase : 0 < bitWordValue base) (remaining : ℕ)
    (oracle : ι → BinaryFraction) (readWork : ι → ℕ) :
    (normalize program base hbase remaining).work oracle readWork =
      program.work oracle readWork +
        (BinaryFraction.finishCachedWithWork (program.value oracle, 0) base hbase remaining).2 := by
  simp only [normalize, work_bind, compute, work, Nat.add_zero]

end EditApproximation.BitQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitQueryNormalizationCost
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BitQuery

theorem normalize_work_bound {ι : Type*} (program : BitQuery ι BinaryFraction)
    (base : List Bool) (hbase : 0 < bitWordValue base) (remaining A B C : ℕ)
    (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (ha : (program.value oracle).width ≤ A) (hb : base.length ≤ B)
    (hc : program.work oracle readWork ≤ C) :
    (program.normalize base hbase remaining).work oracle readWork ≤
      C + BinaryFraction.powerDenominatorBitBudget remaining A B + 1 := by
  rw [normalize_work]
  have h := BinaryFraction.powerDenominatorWithWork_cost (program.value oracle) base hbase remaining A B ha hb
  change program.work oracle readWork + (0 + _ + 1) ≤ _
  dsimp only
  omega

end EditApproximation.BitQuery

namespace EditApproximation

theorem rankedNormalizeBody_localWork_bound {κ : Type*} (rank : κ → ℕ)
    (raw : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
    (base : List Bool) (hbase : 0 < bitWordValue base) (remaining A C : κ → ℕ)
    (B : ℕ) (hb : base.length ≤ B) (key : κ)
    (ha : ((raw key).value (fun child => rankedBitProgramValue rank
      (rankedNormalizeBody rank raw base hbase remaining) child.val)).width ≤ A key)
    (hc : (raw key).work (fun child => rankedBitProgramValue rank
      (rankedNormalizeBody rank raw base hbase remaining) child.val) (fun _ => 0) ≤ C key) :
    rankedBitLocalWork rank (rankedNormalizeBody rank raw base hbase remaining) key ≤
      C key + BinaryFraction.powerDenominatorBitBudget (remaining key) (A key) B + 1 :=
  BitQuery.normalize_work_bound (raw key) base hbase (remaining key) (A key) B (C key) _ _ ha hb hc

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalValueBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit bit bounds for the actual returned physical table values. -/

namespace EditApproximation

theorem refinement_denominator_base_bits (ell : ℕ) :
    Nat.size (ell ^ 10 + 1) ≤ 10 * Nat.size ell + 3 := by
  have hsum := natural_sum_bit_length (ell ^ 10) 1
  have hpower := natural_power_bit_length ell 10
  norm_num only [Nat.size_one] at hsum
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCacheWords
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
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

theorem computed_refinementBase_length (N : ℕ) (ell : List Bool)
    (hell : bitWordValue ell = inputSmallLog N) :
    (refinementBaseWithWork ell).1.length ≤ 10 * Nat.size (inputSmallLog N) + 3 := by
  rw [refinementBaseWithWork_length, hell]
  exact refinement_denominator_base_bits _

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedNumericalParameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedSourceAddressBits
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySourceWidths
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BitQuery

theorem mapKeysWithWork_value {ι κ β : Type*} (f : ι → κ × ℕ)
    (program : BitQuery ι β) (oracle : κ → BinaryFraction) :
    (mapKeysWithWork f program).value oracle = program.value (fun key => oracle (f key).1) := by
  induction program with
  | done result => rfl
  | charge steps next ih => exact ih
  | read key next ih => exact ih (oracle (f key).1)

end EditApproximation.BitQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryCallbackPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

theorem queryNormalization_fixedPower (n A B X : ℕ) (hX : 2 ≤ X)
    (hn : n ≤ X) (hA : A ≤ X) (hB : B ≤ X) :
    BinaryFraction.powerDenominatorBitBudget n A B ≤ X ^ queryNormalizationBitDegree := by
  have h := normalizationPolynomial.eval_le_pow ![n, A, B, 0, 0, 0] X hX (by
    intro i
    fin_cases i
    · exact hn
    · exact hA
    · exact hB
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · exact Nat.zero_le _)
  exact h

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryRawWidthPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

theorem queryRawWord_fixedPower (M B X : ℕ) (hX : 2 ≤ X) (hM : M ≤ X) (hB : B ≤ X) :
    BinaryFraction.localWarmupWordBudget M B + BinaryFraction.preparedKernelWordBudget M B ≤
      X ^ queryRawWordDegree := by
  exact rawWordPolynomial.eval_le_pow ![M, B] X hX (by
    intro i
    fin_cases i
    · exact hM
    · exact hB)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilySampling
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The finite scalar family is exactly the accepted output of the
independent literal rejection samplers. Only requested coordinates need
be generated; their failure counts have a product law. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Family

variable {α : Type*} {M J R : ℕ} [NeZero M]
  (target : List α) (N P F exponent H Q passes copies : ℕ)





omit [NeZero M] in
 theorem physicalFamilyRange_bits_le (bits : ℕ)
    (hM : M ≤ 2 ^ bits) (hB : localOnlineMassBound M P H ≤ 2 ^ bits)
    (key : PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies) :
    rejectionBitCount (physicalFamilyRange target N P F exponent H Q passes copies key) ≤ bits := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).2
  rcases key with ⟨pass, copy, scalar, index⟩
  cases scalar with
  | inl online =>
    change online.2.val.val ≤ 2 ^ bits
    exact (Nat.le_of_lt_succ online.2.val.isLt).trans hB
  | inr group => exact hM

end Family

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedFamilySampling
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

 theorem computedFamilyRange_bits_le (source target : List ℕ) (N R : ℕ)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (key : ComputedFamilyScalarKey source target N R) :
    rejectionBitCount (physicalFamilyRange target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
      (computedSeedPassCount N) (inputHeight N ^ 2) key) ≤ inputHeight N := by
  apply physicalFamilyRange_bits_le
  · change 2 ^ (heightExponent N / 20) ≤ 2 ^ inputHeight N
    apply Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
    exact (Nat.div_le_self _ _).trans (Nat.lt_two_pow_self.le)
  · exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hB)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedParameterRegisters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedPhysicalUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

theorem two_hundred_le_two_pow_thousand : 200 ≤ (2 : ℕ) ^ 1000 := by
  have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by decide : 8 ≤ 1000)
  exact le_trans (by decide : 200 ≤ (2 : ℕ) ^ 8) h

open MeasureTheory ProbabilityTheory

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryBudgetAlgebra
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

/-- Enlarge the exponent of the common computed kernel scale. -/
theorem computedLocalKernelBudget_mono (N D E : ℕ) (h : D ≤ E) :
    computedLocalKernelBudget D N ≤ computedLocalKernelBudget E N := by
  unfold computedLocalKernelBudget localKernelPowerExponent
  apply Nat.pow_le_pow_right (Nat.two_pow_pos _)
  exact Nat.mul_le_mul_left _ h

theorem computedLocalKernelBudget_three (N D x y z : ℕ) (hH : 3 ≤ inputHeight N)
    (hx : x ≤ computedLocalKernelBudget D N) (hy : y ≤ computedLocalKernelBudget D N)
    (hz : z ≤ computedLocalKernelBudget D N) :
    x + y + z ≤ computedLocalKernelBudget (D + 1) N := by
  let L := (100 * (integerParameters N).M + 100000) * (coarseExponent (inputSmallLog N) + 1)
  let S := inputHeight N ^ L
  have hL : 1 ≤ L := by
    have h := Nat.le_mul_of_pos_right (100 * (integerParameters N).M + 100000)
      (by omega : 0 < coarseExponent (inputSmallLog N) + 1)
    dsimp only [L]
    omega
  have hHS : inputHeight N ≤ S := Nat.le_pow hL
  have hx' : x ≤ S ^ D := by simpa only [S, L, computedLocalKernelBudget, localKernelPowerExponent, ← pow_mul] using hx
  have hy' : y ≤ S ^ D := by simpa only [S, L, computedLocalKernelBudget, localKernelPowerExponent, ← pow_mul] using hy
  have hz' : z ≤ S ^ D := by simpa only [S, L, computedLocalKernelBudget, localKernelPowerExponent, ← pow_mul] using hz
  have hsum : x + y + z ≤ 3 * S ^ D := by omega
  have h3S : 3 ≤ S := hH.trans hHS
  calc
    _ ≤ 3 * S ^ D := hsum
    _ ≤ S * S ^ D := Nat.mul_le_mul_right _ h3S
    _ = S ^ (D + 1) := (pow_succ' S D).symm
    _ = _ := by simp only [S, ← pow_mul]; rfl

/-- The fixed guard overhead at the eight-power word bound. -/
theorem computed_kernel_guard_cost (N : ℕ) (hH : 64 ≤ inputHeight N) :
    50 * inputHeight N ^ 8 + 100 ≤ computedLocalKernelBudget 1 N := by
  let H := inputHeight N
  let L := (100 * (integerParameters N).M + 100000) * (coarseExponent (inputSmallLog N) + 1)
  have hL : 10 ≤ L := by
    have h := Nat.le_mul_of_pos_right (100 * (integerParameters N).M + 100000)
      (by omega : 0 < coarseExponent (inputSmallLog N) + 1)
    dsimp only [L]
    omega
  have hpow : 50 * H ^ 8 + 100 ≤ H ^ 10 := by
    have hone : 1 ≤ H ^ 8 := one_le_pow₀ (by omega)
    have hcoef : 150 ≤ H ^ 2 := by nlinarith only [hH]
    calc
      _ ≤ 150 * H ^ 8 := by omega
      _ ≤ H ^ 2 * H ^ 8 := Nat.mul_le_mul_right _ hcoef
      _ = _ := by rw [← pow_add]
  apply hpow.trans
  change H ^ 10 ≤ H ^ (L * 1)
  simpa only [Nat.mul_one] using Nat.pow_le_pow_right (by omega : 0 < H) hL

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryConstants
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter

theorem computedQueryMass_word :
    ∀ᶠ N : ℕ in atTop, Nat.size (localOnlineMassBound (integerParameters N).M
      (integerParameters N).P (inputHeight N)) ≤ inputHeight N := by
  filter_upwards [computedParameterPower_word,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 64)] with N hp hell
  have hH : 64 ≤ inputHeight N := hell.trans (computed_smallLog_le_height N)
  exact (Nat.size_le_size (computed_localOnlineMassBound_polynomial N hH)).trans
    (hp _ le_rfl)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryNormalizationBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter
attribute [local irreducible] queryRawWordDegree queryNormalizationBitDegree

theorem computedQueryNormalizationBudget_cap (K : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ remaining A B : ℕ, remaining ≤ inputHeight N → B ≤ inputHeight N ^ 3 →
      A ≤ computedLocalKernelBudget K N →
      BinaryFraction.powerDenominatorBitBudget remaining A B ≤
        computedLocalKernelBudget (computedQueryNormalizationDegree K) N := by
  filter_upwards [inputSmallLog_tendsto.eventually (eventually_ge_atTop 64)] with N hell
  intro remaining A B hr hB hA
  let H := inputHeight N
  let L := (100 * (integerParameters N).M + 100000) * (coarseExponent (inputSmallLog N) + 1)
  let S := H ^ L
  let X := S ^ (K + 1)
  have hH : 64 ≤ H := hell.trans (computed_smallLog_le_height N)
  have hp : 0 < H := by omega
  have hL : 3 ≤ L := by
    have h := Nat.le_mul_of_pos_right (100 * (integerParameters N).M + 100000)
      (by omega : 0 < coarseExponent (inputSmallLog N) + 1)
    dsimp only [L]
    omega
  have hHS : H ≤ S := Nat.le_pow (by omega)
  have hSX : S ≤ X := Nat.le_pow (by omega)
  have h3S : H ^ 3 ≤ S := Nat.pow_le_pow_right hp hL
  have hAX : A ≤ X := by
    apply hA.trans
    change H ^ (L * K) ≤ (H ^ L) ^ (K + 1)
    rw [← pow_mul]
    exact Nat.pow_le_pow_right hp (Nat.mul_le_mul_left L (Nat.le_succ K))
  have h := queryNormalization_fixedPower remaining A B X ((by omega : 2 ≤ H).trans (hHS.trans hSX))
    (hr.trans (hHS.trans hSX)) hAX (hB.trans (h3S.trans hSX))
  apply h.trans_eq
  change ((H ^ L) ^ (K + 1)) ^ queryNormalizationBitDegree = H ^ (L * computedQueryNormalizationDegree K)
  rw [← pow_mul, ← pow_mul]
  congr 1

theorem computedQueryRawWidth_cap :
    ∀ᶠ N : ℕ in atTop,
      BinaryFraction.localWarmupWordBudget (integerParameters N).M (inputHeight N ^ 8) +
        BinaryFraction.preparedKernelWordBudget (integerParameters N).M (inputHeight N ^ 8) ≤
        computedLocalKernelBudget queryRawWordDegree N := by
  filter_upwards [inputSmallLog_tendsto.eventually (eventually_ge_atTop 64)] with N hell
  let H := inputHeight N
  let L := (100 * (integerParameters N).M + 100000) * (coarseExponent (inputSmallLog N) + 1)
  let S := H ^ L
  have hH : 64 ≤ H := hell.trans (computed_smallLog_le_height N)
  have hL : 8 ≤ L := by
    have h := Nat.le_mul_of_pos_right (100 * (integerParameters N).M + 100000)
      (by omega : 0 < coarseExponent (inputSmallLog N) + 1)
    dsimp only [L]
    omega
  have hHS : H ≤ S := Nat.le_pow (by omega)
  have hM : (integerParameters N).M ≤ H :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.div_le_self _ _)
  have h8 : H ^ 8 ≤ S := Nat.pow_le_pow_right (by omega) hL
  have h := queryRawWord_fixedPower (integerParameters N).M (H ^ 8) S
    ((by omega : 2 ≤ H).trans hHS) (hM.trans hHS) h8
  simpa only [S, L, computedLocalKernelBudget, localKernelPowerExponent, ← pow_mul] using h

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryRawWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter BinaryFraction
attribute [local instance] queryArityNeZero queryRoundsNeZero
attribute [local irreducible] queryChargedFamilyTable localRequestValue

/-- Every raw body is charged on the actual, proved normalized-child oracle. -/
theorem computedQueryMemoRaw_bounds :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ (input : ComputedFamilyInput source target N)
      (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ),
      symbolBits ≤ inputHeight N ^ 3 → positionBits ≤ inputHeight N ^ 3 →
      (∀ z ∈ source, z < 2 ^ symbolBits) → (∀ z ∈ target, z < 2 ^ symbolBits) →
      target.length ≤ 2 ^ positionBits → occurrence = occurrenceBuild symbolBits positionBits target.zipIdx →
      ∀ key : ComputedFamilyMemoKey source target N,
      let oracle := fun child : {child : ComputedFamilyMemoKey source target N //
          SourceRanked.rank ChargedPhysicalRequest.rank child <
            SourceRanked.rank ChargedPhysicalRequest.rank key} => rankedBitProgramValue (SourceRanked.rank ChargedPhysicalRequest.rank)
        (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input) child.val
      (computedQueryMemoRaw source target N occurrence symbolBits positionBits input key).work oracle (fun _ => 0) ≤
        computedLocalKernelBudget computedQueryRawWorkDegree N ∧
      ((computedQueryMemoRaw source target N occurrence symbolBits positionBits input key).value oracle).width ≤
        computedLocalKernelBudget computedQueryRawWidthDegree N := by
  filter_upwards [computedQueryTable_work_width, computedQueryRawWidth_cap, computedQueryMass_word,
    eventually_ge_atTop 1, inputSmallLog_tendsto.eventually (eventually_ge_atTop (2 ^ 1000))]
    with N htable hraw hmass hN hell
  intro source target hsize input occurrence symbolBits positionBits hsb hpb hs ht hp hoc key
  dsimp only
  have hsmall : 200 ≤ inputSmallLog N := two_hundred_le_two_pow_thousand.trans hell
  have hH : 64 ≤ inputHeight N := (by omega : 64 ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  have hf : 3 ≤ smallLogExponent N := by
    have h := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hell
    omega
  have hg := computed_kernel_guard_cost N hH
  have hsmallBudget : inputHeight N + 3 ≤ computedLocalKernelBudget 1 N := by
    have hpow : inputHeight N ≤ inputHeight N ^ 8 := Nat.le_pow (by decide)
    omega
  have hworkMono := computedLocalKernelBudget_mono N 1 computedQueryRawWorkDegree (Nat.le_max_left _ _)
  have hwidthMono := computedLocalKernelBudget_mono N 1 computedQueryRawWidthDegree (Nat.le_max_left _ _)
  have hrawMono := computedLocalKernelBudget_mono N queryRawWordDegree computedQueryRawWidthDegree
    (Nat.le_max_right _ _)
  have htableMono := computedLocalKernelBudget_mono N computedTableQueryDegree computedQueryRawWorkDegree
    (Nat.le_max_right _ _)
  cases key with
  | inl key =>
    have hr := computedFamilyRange_bits_le source target N (inputHeight N ^ 2) hmass key
    have hc : (input.2 key).val < 2 ^ inputHeight N := (input.2 key).isLt.trans_le
      ((Nat.le_pow_clog (by decide : 1 < 2) _).trans
        (Nat.pow_le_pow_right (by decide : 0 < 2) hr))
    have hb : Nat.size (input.2 key).val ≤ inputHeight N := Nat.size_le.mpr hc
    change Nat.size (input.2 key).val + 3 ≤ _ ∧ (nat (input.2 key).val).width ≤ _
    exact ⟨(by omega : Nat.size (input.2 key).val + 3 ≤ computedLocalKernelBudget 1 N).trans hworkMono,
      (nat_width_le _).trans ((by omega : Nat.size (input.2 key).val + 2 ≤ computedLocalKernelBudget 1 N).trans hwidthMono)⟩
  | inr key =>
    cases key with
    | inl entry =>
      have hb : Nat.size (clampedSeedNat input.1 entry) ≤ inputHeight N :=
        (Nat.size_le_size (Nat.le_of_lt_succ (input.1 entry).isLt)).trans (computed_input_size_le_height N)
      change 0 ≤ _ ∧ (nat (clampedSeedNat input.1 entry)).width ≤ _
      exact ⟨Nat.zero_le _, (nat_width_le _).trans
        ((by omega : Nat.size (clampedSeedNat input.1 entry) + 2 ≤ computedLocalKernelBudget 1 N).trans hwidthMono)⟩
    | inr parent =>
      let oracle := fun child : {child : ComputedFamilyMemoKey source target N //
          SourceRanked.rank ChargedPhysicalRequest.rank child <
            SourceRanked.rank ChargedPhysicalRequest.rank (.inr (.inr parent) : ComputedFamilyMemoKey source target N)} => rankedBitProgramValue (SourceRanked.rank ChargedPhysicalRequest.rank)
        (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input) child.val
      let tableOracle : ComputedQueryTableKey source target N parent → BinaryFraction :=
        fun child => oracle (SourceRanked.child ChargedPhysicalRequest.rank (.inr parent) child)
      have hw (child) : (tableOracle child).width ≤ inputHeight N ^ 3 :=
        computedQueryMemoNormalized_width source target N occurrence symbolBits positionBits input hN hsmall hf
          hsize hmass hs ht hp hoc _
      have hv (child) : (tableOracle (Sum.inr child)).value = computedFamilyTableValue source target N input child.val :=
        (computedQueryMemoNormalized_correct source target N occurrence symbolBits positionBits input hf hs ht hp hoc _).1
      have hb := htable source target hsize input occurrence symbolBits positionBits hsb hpb parent tableOracle hw hv
      change (BitQuery.mapKeysWithWork (fun child =>
          (SourceRanked.child ChargedPhysicalRequest.rank (.inr parent) child, 1))
        (computedQueryTableProgram source target N occurrence symbolBits positionBits parent)).work oracle (fun _ => 0) ≤ _ ∧
        ((BitQuery.mapKeysWithWork (fun child =>
          (SourceRanked.child ChargedPhysicalRequest.rank (.inr parent) child, 1))
          (computedQueryTableProgram source target N occurrence symbolBits positionBits parent)).value oracle).width ≤ _
      constructor
      · exact (BitQuery.mapKeysWithWork_work
          (fun child : ComputedQueryTableKey source target N parent =>
            (SourceRanked.child ChargedPhysicalRequest.rank (.inr parent) child, 1))
          (computedQueryTableProgram source target N occurrence symbolBits positionBits parent)
          oracle (fun _ => 0)).trans_le (hb.1.trans htableMono)
      · exact (congrArg BinaryFraction.width (BitQuery.mapKeysWithWork_value
          (fun child : ComputedQueryTableKey source target N parent =>
            (SourceRanked.child ChargedPhysicalRequest.rank (.inr parent) child, 1))
          (computedQueryTableProgram source target N occurrence symbolBits positionBits parent)
          oracle)).trans_le (hb.2.trans (hraw.trans hrawMono))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter BinaryFraction
attribute [local instance] queryArityNeZero queryRoundsNeZero
attribute [local irreducible] computedQueryRawWorkDegree computedQueryRawWidthDegree

/-- Complete local work, including binary denominator normalization. -/
theorem computedQueryLocalWork_cap_oai :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ (input : ComputedFamilyInput source target N)
      (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ),
      symbolBits ≤ inputHeight N ^ 3 → positionBits ≤ inputHeight N ^ 3 →
      (∀ z ∈ source, z < 2 ^ symbolBits) → (∀ z ∈ target, z < 2 ^ symbolBits) →
      target.length ≤ 2 ^ positionBits → occurrence = occurrenceBuild symbolBits positionBits target.zipIdx →
      ∀ key, computedQueryLocalWork source target N occurrence symbolBits positionBits input key ≤
        computedLocalKernelBudget computedQueryWorkDegree N := by
  filter_upwards [computedQueryMemoRaw_bounds, computedQueryNormalizationBudget_cap computedQueryRawWidthDegree,
    eventually_ge_atTop 1, inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)]
    with N hraw hnorm hN hell
  intro source target hsize input occurrence symbolBits positionBits hsb hpb hs ht hp hoc key
  have hH : 64 ≤ inputHeight N := (by omega : 64 ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  have hJ : intervalTreeDepth (integerParameters N).M source.length ≤ inputHeight N := by
    have h := computed_tree_depth_bound N source.length hN (by omega) hell
    nlinarith only [h, hell]
  have hr : queryFamilyMemoRemaining (R := inputHeight N ^ 2) target N (integerParameters N).P
      (inputSmallLog N) (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80) key ≤ inputHeight N := by
    cases key with
    | inl key => exact Nat.zero_le _
    | inr key =>
      cases key with
      | inl entry => exact Nat.zero_le _
      | inr request => exact (Nat.sub_le _ _).trans hJ
  have hb : (computedQueryBase N).length ≤ inputHeight N ^ 3 := by
    have h := computed_refinementBase_length N (inputSmallLog N).bits (bitWordValue_bits _)
    have hs : Nat.size (inputSmallLog N) ≤ inputHeight N :=
      (Nat.size_le.mpr Nat.lt_two_pow_self).trans (computed_smallLog_le_height N)
    have hp2 : 10 * inputHeight N + 3 ≤ inputHeight N ^ 2 := by nlinarith only [hH]
    have hp3 := Nat.pow_le_pow_right (by omega : 0 < inputHeight N) (by decide : 2 ≤ 3)
    exact h.trans ((show 10 * Nat.size (inputSmallLog N) + 3 ≤ inputHeight N ^ 2 by omega).trans hp3)
  have hraw' := hraw source target hsize input occurrence symbolBits positionBits hsb hpb hs ht hp hoc key
  have hlocal := rankedNormalizeBody_localWork_bound (SourceRanked.rank ChargedPhysicalRequest.rank)
    (computedQueryMemoRaw source target N occurrence symbolBits positionBits input)
    (computedQueryBase N) (computedQueryBase_pos N)
    (queryFamilyMemoRemaining target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80))
    (fun _ => computedLocalKernelBudget computedQueryRawWidthDegree N)
    (fun _ => computedLocalKernelBudget computedQueryRawWorkDegree N)
    (inputHeight N ^ 3) hb key hraw'.2 hraw'.1
  have hn := hnorm _ _ _ hr le_rfl (Nat.le_refl (computedLocalKernelBudget computedQueryRawWidthDegree N))
  let D := max computedQueryRawWorkDegree (computedQueryNormalizationDegree computedQueryRawWidthDegree)
  have hrawD := computedLocalKernelBudget_mono N computedQueryRawWorkDegree D (Nat.le_max_left _ _)
  have hnormD := computedLocalKernelBudget_mono N (computedQueryNormalizationDegree computedQueryRawWidthDegree) D
    (Nat.le_max_right _ _)
  have hone : 1 ≤ computedLocalKernelBudget D N := one_le_pow₀ (by omega)
  exact hlocal.trans (computedLocalKernelBudget_three N D _ _ _ (by omega) hrawD (hn.trans hnormD) hone)

end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.computedQueryLocalWork_cap_oai := @OAI.EditApproximation.computedQueryLocalWork_cap_oai
