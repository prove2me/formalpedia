-- Prove2me | solution 1 for OAI.EditApproximation.BinaryFraction.computedCoarseIndexedInitialWithWork_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:29:37.174123+00:00
-- url     : https://prove2.me/submissions/c5a9379f-bea6-48ed-b123-906623e24315

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
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea002
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_coarseRootReadExtra_bound
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_computedCoarseInitialWithWork_bound

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

theorem coarseExponent_maximal (ell p : ℕ) (hp : p ^ 4 ≤ Nat.log 2 ell) :
    p ≤ coarseExponent ell := by
  apply Nat.le_sqrt'.2
  apply Nat.le_sqrt'.2
  simpa only [← pow_mul] using hp

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseParameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseGlobalSeed
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseIndexedRead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

theorem coarsePaddedRead_value {α : Type*} (n : ℕ) (word : List α) (hn : word.length ≤ n) (i : ℕ) :
    coarsePaddedRead n word i = (coarsePadTo n word)[i]? := by
  unfold coarsePaddedRead coarsePadTo
  by_cases hi : i < word.length
  · rw [ite_eq_left (hi.trans_le hn), List.getElem?_append_left (by simpa using hi),
      List.getElem?_map, List.getElem?_eq_getElem hi]
    rfl
  · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt hi), List.length_map,
      List.getElem?_replicate, List.getElem?_eq_none (Nat.le_of_not_gt hi)]
    by_cases hin : i < n
    · rw [ite_eq_left hin, ite_eq_left (by omega)]
    · rw [ite_eq_right hin, ite_eq_right (by omega)]

theorem coarseFramedRead_value {α : Type*} (k n : ℕ) (word : List α) (hn : word.length ≤ n) (i : ℕ) :
    coarseFramedRead k n word i =
      (coarseTargetFrame k (coarsePadTo n word))[i]?.getD none := by
  have hl : (List.replicate k (none : Option (Option α)) ++
      (coarsePadTo n word).map some).length = k + n := by
    simp only [List.length_append, List.length_replicate, List.length_map, coarsePadTo_length n word hn]
  unfold coarseFramedRead coarseTargetFrame
  by_cases hi : i < k + n
  · rw [List.getElem?_append_left (by simpa only [hl] using hi)]
    by_cases hk : i < k
    · rw [List.getElem?_append_left (by simpa only [List.length_replicate] using hk),
        List.getElem?_replicate_of_lt hk, Option.getD_some, ite_eq_right (by omega)]
    · rw [List.getElem?_append_right (by simpa only [List.length_replicate] using Nat.le_of_not_gt hk),
        List.length_replicate, List.getElem?_map, ← coarsePaddedRead_value n word hn (i - k)]
      simp only [coarsePaddedRead, ite_eq_left (by omega : i - k < n), Option.map_some,
        Option.getD_some, ite_eq_left (by omega : k ≤ i ∧ i < k + n)]
  · rw [List.getElem?_append_right (by simpa only [hl] using Nat.le_of_not_gt hi), hl,
      List.getElem?_replicate, ite_eq_right (by omega : ¬ (k ≤ i ∧ i < k + n))]
    split_ifs <;> rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseIndexedFrameWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

/-- Read the framed target from its original array and three integer indices. -/


theorem coarseFramedReadWithWork_value {α : Type*} (k n : ℕ) (word : List α) (i : ℕ) :
    (coarseFramedReadWithWork k n word i).1 = coarseFramedRead k n word i := by
  unfold coarseFramedReadWithWork coarseFramedRead
  dsimp only
  by_cases hlo : i < k
  · rw [ite_eq_left ((binaryNaturalCompareWithWork_lt i k).mpr hlo), ite_eq_right (by omega)]
  · rw [ite_eq_right (fun h => hlo ((binaryNaturalCompareWithWork_lt i k).mp h))]
    simp only [binaryNaturalAddWithWork_value]
    by_cases hhi : i < k + n
    · rw [ite_eq_left ((binaryNaturalCompareWithWork_lt i (k + n)).mpr hhi),
        ite_eq_left (by omega)]
      simp only [saturatingSubtractWithWork_value]
    · rw [ite_eq_right (fun h => hhi ((binaryNaturalCompareWithWork_lt i (k + n)).mp h)),
        ite_eq_right (by omega)]

theorem coarseFramedReadWithWork_cost {α : Type*} (k n : ℕ) (word : List α) (i A : ℕ)
    (hk : Nat.size k ≤ A) (hn : Nat.size n ≤ A) (hi : Nat.size i ≤ A) :
    (coarseFramedReadWithWork k n word i).2 ≤ 100 * (A + 1) := by
  have hl := binaryNaturalCompareWithWork_cost i k
  have ha := binaryNaturalAddWithWork_cost k n
  have hs := binaryNaturalAdd_size_le k n
  have hmax : max (Nat.size k) (Nat.size n) ≤ A := max_le hk hn
  have hu := binaryNaturalCompareWithWork_cost i (bitWordValue (binaryNaturalAddWithWork k n).1)
  rw [binaryNaturalAddWithWork_value] at hu
  have hd := saturatingSubtractWithWork_cost i k
  unfold coarseFramedReadWithWork
  dsimp only
  simp only [binaryNaturalAddWithWork_value]
  split_ifs <;> dsimp only <;> omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseReadTree
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

theorem coarseReadTree_ext (B d : ℕ) {α : Type*} (read other : ℕ → Option α)
    (heq : ∀ i < B ^ d, read i = other i) :
    coarseReadTree B d read = coarseReadTree B d other := by
  induction d generalizing read other with
  | zero => exact congrArg CoarseSourceTree.leaf (heq 0 (by simp))
  | succ d ih =>
    apply congrArg CoarseSourceTree.branch
    funext i
    apply ih
    intro j hj
    apply heq
    rw [pow_succ]
    have hmul := Nat.mul_le_mul_right (B ^ d) (Nat.succ_le_of_lt i.isLt)
    have hpos : 0 < B ^ d := by omega
    nlinarith

theorem coarseReadTree_list (B d : ℕ) {α : Type*} (source : List α) :
    coarseReadTree B d (fun i => source[i]?) = coarseSourceTreeOfList B d source := by
  induction d generalizing source with
  | zero => simp only [coarseReadTree, coarseSourceTreeOfList, List.head?_eq_getElem?]
  | succ d ih =>
    apply congrArg CoarseSourceTree.branch
    funext i
    rw [← ih]
    apply coarseReadTree_ext
    intro j hj
    simp only [List.getElem?_take_of_lt hj, List.getElem?_drop, Nat.add_comm]

theorem coarseReadTree_shift (B d start : ℕ) {α : Type*} (source : List α) :
    coarseReadTree B d (fun i => source[start + i]?) =
      coarseSourceTreeOfList B d (source.drop start) := by
  rw [← coarseReadTree_list]
  congr 1
  funext i
  simp only [List.getElem?_drop]

theorem coarseReadTree_shift_length (B d start : ℕ) {α : Type*} (source : List α) :
    (coarseReadTree B d (fun i => source[start + i]?)).word.length =
      min (B ^ d) (source.length - start) := by
  rw [coarseReadTree_shift, coarseSourceTreeOfList_word, List.length_take, List.length_drop]

theorem coarseReadTree_padded_length (B d n start : ℕ) {α : Type*}
    (source : List α) (hn : source.length ≤ n) :
    (coarseReadTree B d (fun i => coarsePaddedRead n source (start + i))).word.length =
      coarseDescriptorLength B d n start := by
  have heq : (fun i => coarsePaddedRead n source (start + i)) =
      (fun i => (coarsePadTo n source)[start + i]?) := by
    funext i
    exact coarsePaddedRead_value n source hn _
  rw [heq, coarseReadTree_shift_length, coarsePadTo_length n source hn]
  rfl

theorem coarseReadTree_entry (B d : ℕ) {α : Type*} (source target : List α) :
    coarseReadTree B d (coarsePaddedRead (coarseEntryWidth source target) source) =
      coarseEntryTree B d source target := by
  have heq : coarsePaddedRead (coarseEntryWidth source target) source =
      (fun i => (coarsePadTo (coarseEntryWidth source target) source)[i]?) := by
    funext i
    exact coarsePaddedRead_value _ _ (le_max_left _ _) i
  rw [heq, coarseReadTree_list]
  rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseDescriptorWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

theorem saturatingSubtractWithWork_length (a b : ℕ) :
    (saturatingSubtractWithWork a b).1.length ≤ max (Nat.size a) (Nat.size b) := by
  unfold saturatingSubtractWithWork
  dsimp only
  split_ifs
  · exact Nat.zero_le _
  · simpa only [binaryNaturalSubtractWithWork, bitSubtractWithWork_length,
      Nat.size_eq_bits_len] using (le_refl (max (Nat.size a) (Nat.size b)))

/-- Construct a descriptor's clipped length by Boolean exponentiation,
subtraction and minimum, retaining the resulting bits. -/


theorem coarseDescriptorWithWork_value (B d n start : ℕ) :
    bitWordValue (coarseDescriptorWithWork B d n start).1 = coarseDescriptorLength B d n start := by
  simp only [coarseDescriptorWithWork, wordMinWithWork_value,
    bitPowerWithWork_value, bitWordValue_bits, saturatingSubtractWithWork_value,
    coarseDescriptorLength]

theorem coarseDescriptorWithWork_cost (B d n start A : ℕ)
    (hB : Nat.size B ≤ A) (hn : Nat.size n ≤ A) (hs : Nat.size start ≤ A) :
    (coarseDescriptorWithWork B d n start).2 ≤
      bitPowerBitBudget d A + 100 * (d + 2) * (A + 1) := by
  have hp := bitPowerWithWork_cost B.bits d A (by simpa only [Nat.size_eq_bits_len] using hB)
  have hpl := bitPowerWithWork_length_le B.bits d A (by simpa only [Nat.size_eq_bits_len] using hB)
  have hr := saturatingSubtractWithWork_cost n start
  have hrl := saturatingSubtractWithWork_length n start
  have hm := wordLEWithWork_cost (bitPowerWithWork B.bits d).1
    (saturatingSubtractWithWork n start).1
  have hd : Nat.size d ≤ d := Nat.size_le.mpr (Nat.lt_pow_self (by decide : 1 < (2 : ℕ)))
  simp only [coarseDescriptorWithWork, wordMinWithWork]
  nlinarith only [hp, hpl, hr, hrl, hm, hd, hB, hn, hs,
    max_le hn hs, Nat.zero_le d, Nat.zero_le A]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseIndexedChildren
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- The executable child loop carries indices and cached subtree lengths.
In particular it never flattens a semantic source tree to obtain its length. -/


theorem coarseIndexChildren_eq {B d : ℕ} {α : Type*} (k q L : ℕ) (two : BinaryFraction)
    (width : Fin B → ℕ) (children : Fin B → CoarseSourceTree B α d)
    (evaluate : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ →
      CoarseBinaryArray × ℕ)
    (indexed : Fin B → BinaryFraction → ℕ → CoarseBinaryArray × ℕ)
    (draw : Fin B → Fin B) (below : Fin B → CoarseThresholdDraws B d)
    (hw : ∀ i, width i = (children i).word.length)
    (he : ∀ i a start, indexed i a start = evaluate (children i) (below i) a start)
    (allowance : BinaryFraction) (indices : List (Fin B)) (start : ℕ) :
    coarseIndexChildren k q L two width indexed draw allowance indices start =
      coarseBinaryChildren k q L two evaluate allowance
        (indices.map fun i => (children i, draw i, below i)) start := by
  induction indices generalizing start with
  | nil => rfl
  | cons i rest ih =>
    simp only [coarseIndexChildren, List.map_cons, coarseBinaryChildren, he, hw, ih]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseIndexedCompare
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Local arithmetic depends only on returned arrays, so replacing a child
by a representation-equivalent implementation preserves every parent array. -/
theorem coarseIndexChildren_value_congr {B : ℕ} (k q L : ℕ) (two : BinaryFraction)
    (width : Fin B → ℕ) (draw : Fin B → Fin B)
    (evaluate other : Fin B → BinaryFraction → ℕ → CoarseBinaryArray × ℕ)
    (he : ∀ i a start, (evaluate i a start).1 = (other i a start).1)
    (allowance : BinaryFraction) (indices : List (Fin B)) (start : ℕ) :
    (coarseIndexChildren k q L two width evaluate draw allowance indices start).1 =
      (coarseIndexChildren k q L two width other draw allowance indices start).1 := by
  induction indices generalizing start with
  | nil => rfl
  | cons i rest ih => simp only [coarseIndexChildren, he, ih]


/-- Extra costs compose along the same child traversal; no child arithmetic
or array allocation is charged twice by this comparison. -/
theorem coarseIndexChildren_cost_compare {B : ℕ} (k q L : ℕ) (two : BinaryFraction)
    (width : Fin B → ℕ) (draw : Fin B → Fin B)
    (evaluate other : Fin B → BinaryFraction → ℕ → CoarseBinaryArray × ℕ)
    (extra : Fin B → BinaryFraction → ℕ → ℕ)
    (he : ∀ i a start, (evaluate i a start).1 = (other i a start).1)
    (hc : ∀ i a start, (evaluate i a start).2 ≤ (other i a start).2 + extra i a start)
    (allowance : BinaryFraction) (indices : List (Fin B)) (start : ℕ) :
    (coarseIndexChildren k q L two width evaluate draw allowance indices start).2 ≤
      (coarseIndexChildren k q L two width other draw allowance indices start).2 +
        coarseIndexAdditionalWork q L width draw extra allowance indices start := by
  induction indices generalizing start with
  | nil => simp only [coarseIndexChildren, coarseIndexAdditionalWork, Nat.add_zero, le_refl]
  | cons i rest ih =>
    let childAllowance := (coarseChildAllowanceWithWork L
      (coarseChildThresholdWithWork B q allowance (draw i)).1).1
    have hi := hc i childAllowance start
    have hr := ih (start + width i)
    have hechild := he i childAllowance start
    have herest := coarseIndexChildren_value_congr k q L two width draw evaluate other he
      allowance rest (start + width i)
    simp only [coarseIndexChildren, coarseIndexAdditionalWork]
    dsimp only [childAllowance] at hi hechild
    rw [hechild, herest]
    omega


theorem arithmeticMapWithWork_add_cost {α β : Type*} (f : α → β × ℕ)
    (extra : α → ℕ) (xs : List α) :
    (arithmeticMapWithWork (fun x => ((f x).1, (f x).2 + extra x)) xs).2 =
      (arithmeticMapWithWork f xs).2 + (xs.map extra).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [arithmeticMapWithWork, List.map_cons, List.sum_cons, ih]
    omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseReadAccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

/-- A padded-source lookup tests its virtual endpoint and then reads the
original symbol array. Padding is represented by `none`. -/


theorem coarsePaddedReadWithWork_value {α : Type*} (n : ℕ) (source : List α) (offset : ℕ) :
    (coarsePaddedReadWithWork n source offset).1 = coarsePaddedRead n source offset := by
  unfold coarsePaddedReadWithWork coarsePaddedRead
  dsimp only
  simp only [binaryNaturalCompareWithWork_lt]

theorem coarsePaddedReadWithWork_cost {α : Type*} (n : ℕ) (source : List α)
    (offset A : ℕ) (hn : Nat.size n ≤ A) (ho : Nat.size offset ≤ A) :
    (coarsePaddedReadWithWork n source offset).2 ≤ 12 * (A + 1) := by
  have h := binaryNaturalCompareWithWork_cost offset n
  change (binaryNaturalCompareWithWork offset n).2 + Nat.size n + Nat.size offset + 2 ≤ _
  omega

theorem coarsePaddedRead_symbol_mem (n : ℕ) (source : List ℕ) (offset a : ℕ)
    (h : coarsePaddedRead n source offset = some (some a)) : a ∈ source := by
  unfold coarsePaddedRead at h
  split_ifs at h
  exact List.mem_of_getElem? (Option.some.inj h)

/-- Child offsets are formed by literal multiplication and addition. -/


theorem coarseChildOffsetWithWork_value (offset capacity index : ℕ) :
    bitWordValue (coarseChildOffsetWithWork offset capacity index).1 = offset + index * capacity := by
  simp only [coarseChildOffsetWithWork, binaryNaturalAddWithWork_value, binaryNaturalMulWithWork_value]

theorem coarseChildOffsetWithWork_cost (offset capacity index A : ℕ)
    (ho : Nat.size offset ≤ A) (hc : Nat.size capacity ≤ A) (hi : Nat.size index ≤ A) :
    (coarseChildOffsetWithWork offset capacity index).2 ≤ 200 * (A + 1) ^ 2 := by
  have hm := binaryNaturalMulWithWork_cost index capacity
  have ha := binaryNaturalAddWithWork_cost offset (index * capacity)
  have hp := natural_product_bit_length index capacity
  simp only [coarseChildOffsetWithWork, binaryNaturalMulWithWork_value]
  have hmax : max (Nat.size offset) (Nat.size (index * capacity)) ≤ 2 * A + 1 := by
    apply max_le <;> omega
  nlinarith only [hm, ha, hp, ho, hc, hi, hmax, Nat.zero_le A]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseReadCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

theorem coarseReadShiftCost_eq {B : ℕ} {α : Type*} [DecidableEq α]
    (k n : ℕ) (target : List α) (hn : target.length ≤ n)
    (letter : Option (Option α)) (start : ℕ) (shift : Fin (2 * k + 1)) :
    coarseShiftCost k (coarseTargetFrame k (coarsePadTo n target))
      (.leaf (B := B) letter) start shift = coarseReadShiftCost k n target letter start shift := by
  cases letter with
  | none => rfl
  | some letter =>
    unfold coarseShiftCost coarseReadShiftCost
    rw [coarseFramedRead_value k n target hn]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseReadEvaluation
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

attribute [local irreducible] coarseReadCore coarseBinaryEval

theorem coarseReadCore_eq {B : ℕ} {α : Type*} [DecidableEq α]
    (k q L n : ℕ) (source target : List α) (hs : source.length ≤ n) (ht : target.length ≤ n)
    (two : BinaryFraction) (d offset : ℕ) (draws : CoarseThresholdDraws B d)
    (allowance : BinaryFraction) (start : ℕ) :
    coarseReadCore k q L n source target two d offset draws allowance start =
      coarseBinaryEval k q L (coarseTargetFrame k (coarsePadTo n target)) two
        (coarseReadTree B d (fun i => coarsePaddedRead n source (offset + i))) draws allowance start := by
  induction d generalizing offset allowance start with
  | zero =>
    have hlen := coarseReadTree_padded_length B 0 n offset source hs
    simp only [coarseReadTree, Nat.add_zero] at hlen ⊢
    rw [coarseReadCore, coarseBinaryEval, hlen]
    simp only [coarseReadShiftCost_eq k n target ht]
  | succ d ih =>
    obtain ⟨draws, below⟩ := draws
    let children := fun i : Fin B => coarseReadTree B d
      (fun j => coarsePaddedRead n source (offset + i.val * B ^ d + j))
    have htree : coarseReadTree B (d + 1) (fun i => coarsePaddedRead n source (offset + i)) =
        CoarseSourceTree.branch children := by
      simp only [coarseReadTree, children, Nat.add_assoc]
    have hlen : (CoarseSourceTree.branch children).word.length =
        coarseDescriptorLength B (d + 1) n offset := by
      rw [← htree]
      exact coarseReadTree_padded_length B (d + 1) n offset source hs
    have hloop : coarseIndexChildren k q L two
        (fun i => coarseDescriptorLength B d n (offset + i.val * B ^ d))
        (fun i => coarseReadCore k q L n source target two d (offset + i.val * B ^ d) (below i))
        draws allowance (List.finRange B) start =
      coarseBinaryChildren k q L two
        (fun child => coarseBinaryEval k q L (coarseTargetFrame k (coarsePadTo n target)) two child)
        allowance (List.ofFn fun i => (children i, draws i, below i)) start := by
      simpa only [List.ofFn_eq_map] using coarseIndexChildren_eq k q L two _ children _ _ draws below
        (fun i => (coarseReadTree_padded_length B d n (offset + i.val * B ^ d) source hs).symm)
        (fun i a s => ih (offset + i.val * B ^ d) (below i) a s) allowance (List.finRange B) start
    erw [htree, coarseReadCore, coarseBinaryEval, hlen]
    simp only [hloop]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseReadLeafWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

/-- Compare one tagged source letter with a framed target lookup. -/


theorem coarseLetterMatchWithWork_value (actual : Option (Option ℕ)) (wanted : Option ℕ) :
    (coarseLetterMatchWithWork actual wanted).1 = true ↔ actual = some wanted := by
  cases actual with
  | none => cases wanted <;> simp only [coarseLetterMatchWithWork, Bool.false_eq_true, reduceCtorEq]
  | some actual =>
    cases actual <;> cases wanted <;>
      simp only [coarseLetterMatchWithWork, naturalEqualWithWork_value, Option.some.injEq,
        Bool.false_eq_true, reduceCtorEq, iff_self]

theorem coarseLetterMatchWithWork_cost (actual : Option (Option ℕ)) (wanted : Option ℕ)
    (S : ℕ) (ha : ∀ a, actual = some (some a) → Nat.size a ≤ S)
    (hw : ∀ b, wanted = some b → Nat.size b ≤ S) :
    (coarseLetterMatchWithWork actual wanted).2 ≤ 8 * S + 2 := by
  cases actual with
  | none => cases wanted <;> simp only [coarseLetterMatchWithWork] <;> omega
  | some actual =>
    cases actual with
    | none => cases wanted <;> simp only [coarseLetterMatchWithWork] <;> omega
    | some a =>
      cases wanted with
      | none => simp only [coarseLetterMatchWithWork]; omega
      | some b => exact naturalEqualWithWork_cost a b S (ha a rfl) (hw b rfl)

theorem coarseFramedRead_symbol_mem (k n : ℕ) (target : List ℕ) (i a : ℕ)
    (h : coarseFramedRead k n target i = some (some a)) : a ∈ target := by
  unfold coarseFramedRead at h
  split_ifs at h
  · exact List.mem_of_getElem? (Option.some.inj h)

namespace BinaryFraction

/-- The leaf lookup explicitly adds the shift, reads the indexed frame and
compares the stored symbol bits. -/


theorem coarseReadShiftWithWork_value (k n : ℕ) (target : List ℕ)
    (letter : Option (Option ℕ)) (start : ℕ) (shift : Fin (2 * k + 1)) :
    (coarseReadShiftWithWork k n target letter start shift).1 =
      coarseReadShiftCost k n target letter start shift := by
  cases letter with
  | none => rfl
  | some letter =>
    simp only [coarseReadShiftWithWork, binaryNaturalAddWithWork_value,
      coarseFramedReadWithWork_value, coarseReadShiftCost,
      coarseLetterMatchWithWork_value]

theorem coarseReadShiftWithWork_cost (k n : ℕ) (target : List ℕ)
    (letter : Option (Option ℕ)) (start : ℕ) (shift : Fin (2 * k + 1)) (A S : ℕ)
    (hk : Nat.size k ≤ A) (hn : Nat.size n ≤ A) (hs : Nat.size start ≤ A)
    (hi : Nat.size shift.val ≤ A) (ht : ∀ a ∈ target, Nat.size a ≤ S)
    (hl : ∀ a, letter = some (some a) → Nat.size a ≤ S) :
    (coarseReadShiftWithWork k n target letter start shift).2 ≤ 200 * (A + 3) + 8 * S := by
  cases letter with
  | none => simp only [coarseReadShiftWithWork]; omega
  | some letter =>
    have hp := binaryNaturalAdd_size_le start shift.val
    have hpos : Nat.size (start + shift.val) ≤ A + 2 := hp.trans (Nat.add_le_add_right (max_le hs hi) 2)
    have hf := coarseFramedReadWithWork_cost k n target (start + shift.val) (A + 2)
      (by omega) (by omega) hpos
    have hm := coarseLetterMatchWithWork_cost
      (coarseFramedReadWithWork k n target (start + shift.val)).1 letter S
      (fun a ha => ht a (coarseFramedRead_symbol_mem k n target (start + shift.val) a
        ((coarseFramedReadWithWork_value k n target _).symm.trans ha)))
      (fun a ha => hl a (congrArg some ha))
    have ha := binaryNaturalAddWithWork_cost start shift.val
    simp only [coarseReadShiftWithWork, binaryNaturalAddWithWork_value]
    omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseIndexedValue
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

attribute [local irreducible] coarseIndexedWithWork coarseReadCore

/-- Charging descriptor/read operations leaves the indexed arithmetic
result unchanged, on every draw and every pruning branch. -/
theorem coarseIndexedWithWork_value {B : ℕ} (k q L n : ℕ) (source target : List ℕ)
    (two : BinaryFraction) (d offset : ℕ) (draws : CoarseThresholdDraws B d)
    (allowance : BinaryFraction) (start : ℕ) :
    (coarseIndexedWithWork k q L n source target two d offset draws allowance start).1 =
      (coarseReadCore k q L n source target two d offset draws allowance start).1 := by
  induction d generalizing offset allowance start with
  | zero =>
    rw [coarseIndexedWithWork, coarseReadCore]
    simp only [coarseDescriptorWithWork_value, coarsePaddedReadWithWork_value]
    split_ifs
    · rfl
    · simp only [arithmeticMapWithWork_value, coarseReadShiftWithWork_value]
  | succ d ih =>
    obtain ⟨draws, below⟩ := draws
    have hloop := coarseIndexChildren_value_congr k q L two
      (fun i : Fin B => coarseDescriptorLength B d n (offset + i.val * B ^ d)) draws
      (fun i a s =>
        let childOffset := coarseChildOffsetWithWork offset (bitWordValue (bitPowerWithWork B.bits d).1) i.val
        let childSize := coarseDescriptorWithWork B d n (bitWordValue childOffset.1)
        let evaluated := coarseIndexedWithWork k q L n source target two d
          (bitWordValue childOffset.1) (below i) a s
        let next := binaryNaturalAddWithWork s (bitWordValue childSize.1)
        (evaluated.1, evaluated.2 + 3 * (childOffset.2 + childSize.2 + next.2 + 3)))
      (fun i => coarseReadCore k q L n source target two d (offset + i.val * B ^ d) (below i))
      (by
        intro i a s
        simp only [coarseChildOffsetWithWork_value, bitPowerWithWork_value, bitWordValue_bits]
        exact ih (offset + i.val * B ^ d) (below i) a s)
      allowance (List.finRange B) start
    erw [coarseIndexedWithWork, coarseReadCore]
    simp only [coarseDescriptorWithWork_value, coarseChildOffsetWithWork_value,
      bitPowerWithWork_value, bitWordValue_bits]
    split_ifs
    · rfl
    · simpa only [coarseChildOffsetWithWork_value, bitPowerWithWork_value, bitWordValue_bits,
        coarseDescriptorWithWork_value] using hloop

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseIndexedCostComparison
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

attribute [local irreducible] coarseIndexedWithWork coarseReadCore coarseIndexedExtra

theorem coarseIndexedWithWork_cost_compare {B : ℕ} (k q L n : ℕ) (source target : List ℕ)
    (two : BinaryFraction) (d offset : ℕ) (draws : CoarseThresholdDraws B d)
    (allowance : BinaryFraction) (start : ℕ) :
    (coarseIndexedWithWork k q L n source target two d offset draws allowance start).2 ≤
      (coarseReadCore k q L n source target two d offset draws allowance start).2 +
        coarseIndexedExtra k q L n source target two d offset draws allowance start := by
  induction d generalizing offset allowance start with
  | zero =>
    let f := fun shift : Fin (2 * k + 1) =>
      coarseGridNatWithWork allowance.denominator allowance.denominator_pos
        (coarseReadShiftCost k n target (coarsePaddedRead n source offset) start shift)
    let extra := fun shift : Fin (2 * k + 1) =>
      (coarseReadShiftWithWork k n target (coarsePaddedRead n source offset) start shift).2
    have hc := arithmeticMapWithWork_add_cost f extra (List.finRange (2 * k + 1))
    rw [coarseIndexedWithWork, coarseReadCore, coarseIndexedExtra]
    simp only [coarseDescriptorWithWork_value, coarsePaddedReadWithWork_value]
    split_ifs
    · omega
    · simp only [f, extra] at hc
      simp only [coarseReadShiftWithWork_value]
      omega
  | succ d ih =>
    obtain ⟨draws, below⟩ := draws
    let capacity := bitPowerWithWork B.bits d
    let childOffset := fun i : Fin B => coarseChildOffsetWithWork offset (bitWordValue capacity.1) i.val
    let childSize := fun i : Fin B => coarseDescriptorWithWork B d n (bitWordValue (childOffset i).1)
    let overhead := fun i : Fin B => fun s : ℕ =>
      3 * ((childOffset i).2 + (childSize i).2 +
        (binaryNaturalAddWithWork s (bitWordValue (childSize i).1)).2 + 3)
    let actual := fun i : Fin B => fun a s =>
      let evaluated := coarseIndexedWithWork k q L n source target two d
        (bitWordValue (childOffset i).1) (below i) a s
      (evaluated.1, evaluated.2 + overhead i s)
    let reference := fun i : Fin B =>
      coarseReadCore k q L n source target two d (offset + i.val * B ^ d) (below i)
    let extra := fun i : Fin B => fun a s =>
      coarseIndexedExtra k q L n source target two d (offset + i.val * B ^ d) (below i) a s + overhead i s
    have hv : ∀ i a s, (actual i a s).1 = (reference i a s).1 := by
      intro i a s
      simp only [actual, reference, childOffset, capacity, coarseChildOffsetWithWork_value,
        bitPowerWithWork_value, bitWordValue_bits]
      exact coarseIndexedWithWork_value k q L n source target two d _ _ a s
    have hw : ∀ i a s, (actual i a s).2 ≤ (reference i a s).2 + extra i a s := by
      intro i a s
      simp only [actual, reference, extra, childOffset, capacity, coarseChildOffsetWithWork_value,
        bitPowerWithWork_value, bitWordValue_bits]
      have h := ih (offset + i.val * B ^ d) (below i) a s
      omega
    have hloop := coarseIndexChildren_cost_compare k q L two
      (fun i => coarseDescriptorLength B d n (offset + i.val * B ^ d)) draws actual reference extra
      hv hw allowance (List.finRange B) start
    erw [coarseIndexedWithWork, coarseReadCore, coarseIndexedExtra]
    simp only [coarseDescriptorWithWork_value]
    split_ifs
    · omega
    · simp only [actual, reference, extra, overhead, childOffset, childSize, capacity,
        coarseDescriptorWithWork_value, coarseChildOffsetWithWork_value,
        bitPowerWithWork_value, bitWordValue_bits] at hloop ⊢
      omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseInitialExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
namespace BinaryFraction



 theorem naturalListEqualWithWork_value (x y : List ℕ) :
    (naturalListEqualWithWork x y).1 = true ↔ x = y := by
  induction x generalizing y with
  | nil => cases y <;> simp [naturalListEqualWithWork]
  | cons a left ih =>
    cases y with
    | nil => simp [naturalListEqualWithWork]
    | cons b right =>
      simp only [naturalListEqualWithWork]
      by_cases hab : a = b
      · rw [ite_eq_left ((naturalEqualWithWork_value a b).mpr hab), ih]
        simp only [List.cons.injEq, hab, true_and]
      · have ht : ¬ (naturalEqualWithWork a b).1 = true :=
          fun h => hab ((naturalEqualWithWork_value a b).mp h)
        simp only [ite_eq_right ht, Bool.false_eq_true, List.cons.injEq, hab, false_and]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseIndexedInitial
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
namespace BinaryFraction



theorem coarseIndexedRootWithWork_value {B d : ℕ} (k q L : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : CoarseThresholdDraws B d) :
    (coarseIndexedRootWithWork k q L hB hq hL x y draws).1 =
      (coarseRootWithWork k q L hB hq hL
        (coarseTargetFrame k (coarsePadTo (coarseEntryWidth x y) y))
        (coarseEntryTree B d x y) draws 0 (coarseRootShift k)).1 := by
  unfold coarseIndexedRootWithWork coarseRootWithWork
  dsimp only
  rw [coarseIndexedWithWork_value, coarseReadCore_eq k q L (coarseEntryWidth x y) x y
    (le_max_left _ _) (le_max_right _ _)]
  simp only [Nat.zero_add, coarseReadTree_entry]



theorem coarseIndexedCandidateWithWork_value {B d : ℕ} (q L : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (i : CoarseGuessIndex (coarseEntryWidth x y)) (draws : CoarseThresholdDraws B d) :
    (coarseIndexedCandidateWithWork q L hB hq hL x y i draws).1 =
      (coarseCandidateWithWork q L hB hq hL x y i draws).1 := by
  simp only [coarseIndexedCandidateWithWork, coarseCandidateWithWork, coarseIndexedRootWithWork_value]

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

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseReadNumericalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

/-- The same small numerical envelope covers constructing a node's length. -/
theorem coarseDescriptorWithWork_height_bound (B d n offset H : ℕ)
    (hH : 10 ≤ H) (hd : d ≤ H) (hB : Nat.size B ≤ H ^ 3)
    (hn : Nat.size n ≤ H ^ 3) (ho : Nat.size offset ≤ H ^ 3) :
    (coarseDescriptorWithWork B d n offset).2 ≤ H ^ 30 := by
  have hc := coarseDescriptorWithWork_cost B d n offset (H ^ 3) hB hn ho
  have hp := BinaryFraction.bitPowerBitBudget_mono d H (H ^ 3) (7 * H ^ 3 + 3) hd (by omega)
  let W := 10 * (H + 2) * (H ^ 3 + 1) + 1
  have hw : (d + 2) * (H ^ 3 + 1) ≤ W := by
    have hm := Nat.mul_le_mul_right (H ^ 3 + 1) (show d + 2 ≤ H + 2 by omega)
    dsimp only [W]
    nlinarith only [hm, Nat.zero_le ((H + 2) * (H ^ 3 + 1))]
  have hl : 100 * (d + 2) * (H ^ 3 + 1) ≤ 1000 * W ^ 2 := by
    have hW : 1 ≤ W := by dsimp only [W]; omega
    nlinarith only [hw, hW]
  have hunit : (coarseDescriptorWithWork B d n offset).2 ≤ BinaryFraction.coarseNumericalUnit H := by
    unfold BinaryFraction.coarseNumericalUnit
    change _ ≤ bitPowerBitBudget H (7 * H ^ 3 + 3) + 1000 * W ^ 2 + _
    omega
  exact hunit.trans (BinaryFraction.coarseNumericalUnit_le_power H hH)

theorem coarseChildOffsetWithWork_height_bound (offset capacity index H : ℕ)
    (hH : 10 ≤ H) (ho : Nat.size offset ≤ H ^ 3)
    (hc : Nat.size capacity ≤ H ^ 3) (hi : Nat.size index ≤ H ^ 3) :
    (coarseChildOffsetWithWork offset capacity index).2 ≤ H ^ 30 := by
  have h := coarseChildOffsetWithWork_cost offset capacity index (H ^ 3) ho hc hi
  have hu : 200 * (H ^ 3 + 1) ^ 2 ≤ BinaryFraction.coarseNumericalUnit H := by
    unfold BinaryFraction.coarseNumericalUnit
    omega
  exact h.trans (hu.trans (BinaryFraction.coarseNumericalUnit_le_power H hH))

theorem coarseReadShiftWithWork_height_bound (k n : ℕ) (target : List ℕ)
    (letter : Option (Option ℕ)) (start : ℕ) (shift : Fin (2 * k + 1)) (H : ℕ)
    (hH : 10 ≤ H) (hk : Nat.size k ≤ H ^ 3) (hn : Nat.size n ≤ H ^ 3)
    (hs : Nat.size start ≤ H ^ 3) (hi : Nat.size shift.val ≤ H ^ 3)
    (ht : ∀ a ∈ target, Nat.size a ≤ H ^ 3)
    (hl : ∀ a, letter = some (some a) → Nat.size a ≤ H ^ 3) :
    (BinaryFraction.coarseReadShiftWithWork k n target letter start shift).2 ≤ H ^ 30 := by
  have h := BinaryFraction.coarseReadShiftWithWork_cost k n target letter start shift
    (H ^ 3) (H ^ 3) hk hn hs hi ht hl
  have hh : 1 ≤ H ^ 3 := one_le_pow₀ (by omega)
  have hc : 200 * (H ^ 3 + 3) + 8 * H ^ 3 ≤ 100001000 * (H ^ 3 + 1) ^ 2 := by
    nlinarith only [hh]
  have hu : 100001000 * (H ^ 3 + 1) ^ 2 ≤ BinaryFraction.coarseNumericalUnit H := by
    unfold BinaryFraction.coarseNumericalUnit
    omega
  exact h.trans (hc.trans (hu.trans (BinaryFraction.coarseNumericalUnit_le_power H hH)))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseReadBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

theorem coarseReadBudget_height (B R k n H : ℕ) (source target : List ℕ)
    (hH : 10 ≤ H) (hR : R ≤ H) (hBpos : 1 ≤ B)
    (hB : Nat.size B ≤ H ^ 3) (hcap : Nat.size (B ^ R) ≤ H ^ 3)
    (hn : Nat.size n ≤ H ^ 3) (hk : Nat.size (2 * k + 1) ≤ H ^ 3)
    (hsymbol : ∀ a ∈ source ++ target, Nat.size a ≤ H ^ 3) :
    CoarseReadBudget B R k n source target (H ^ 30) := by
  have hoff (offset : ℕ) (ho : offset ≤ B ^ R) : Nat.size offset ≤ H ^ 3 :=
    (Nat.size_le_size ho).trans hcap
  have hpow (d : ℕ) (hd : d ≤ R) : Nat.size (B ^ d) ≤ H ^ 3 :=
    (Nat.size_le_size (Nat.pow_le_pow_right hBpos hd)).trans hcap
  have hsmall : 20 * (H ^ 3 + 1) ≤ H ^ 30 := by
    have hu : 20 * (H ^ 3 + 1) ≤ BinaryFraction.coarseNumericalUnit H := by
      unfold BinaryFraction.coarseNumericalUnit
      nlinarith only [Nat.zero_le (bitPowerBitBudget H (7 * H ^ 3 + 3)),
        Nat.zero_le (1000 * (10 * (H + 2) * (H ^ 3 + 1) + 1) ^ 2),
        Nat.zero_le (H ^ 3)]
    exact hu.trans (BinaryFraction.coarseNumericalUnit_le_power H hH)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd offset ho
    exact coarseDescriptorWithWork_height_bound B d n offset H hH (hd.trans hR) hB hn (hoff _ ho)
  · intro d hd
    have hc := bitPowerWithWork_cost B.bits d (H ^ 3) (by simpa only [← Nat.size_eq_bits_len] using hB)
    have hm := BinaryFraction.bitPowerBitBudget_mono d H (H ^ 3) (7 * H ^ 3 + 3)
      (hd.trans hR) (by omega)
    have hu : bitPowerBitBudget H (7 * H ^ 3 + 3) ≤ BinaryFraction.coarseNumericalUnit H := by
      unfold BinaryFraction.coarseNumericalUnit
      omega
    exact hc.trans (hm.trans (hu.trans (BinaryFraction.coarseNumericalUnit_le_power H hH)))
  · intro offset ho i d hd
    exact coarseChildOffsetWithWork_height_bound offset (B ^ d) i.val H hH (hoff _ ho)
      (hpow _ hd) ((Nat.size_le_size (Nat.le_of_lt i.isLt)).trans hB)
  · intro s hs width hw
    have hc := binaryNaturalAddWithWork_cost s width
    have hb1 := (Nat.size_le_size hs).trans hn
    have hb2 := (Nat.size_le_size hw).trans hn
    omega
  · intro offset ho
    have hc := coarsePaddedReadWithWork_cost n source offset (H ^ 3) hn (hoff _ ho)
    omega
  · intro offset ho s hs shift
    exact coarseReadShiftWithWork_height_bound k n target (coarsePaddedRead n source offset)
      s shift H hH ((Nat.size_le_size (by omega : k ≤ 2 * k + 1)).trans hk) hn
      ((Nat.size_le_size hs).trans hn) ((Nat.size_le_size (Nat.le_of_lt shift.isLt)).trans hk)
      (fun a ha => hsymbol a (List.mem_append_right source ha))
      (fun a ha => hsymbol a (List.mem_append_left target (coarsePaddedRead_symbol_mem n source offset a ha)))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseIndexedRootCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

theorem coarseIndexedRootWithWork_cost_compare {B d : ℕ} (k q L : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : CoarseThresholdDraws B d) :
    (coarseIndexedRootWithWork k q L hB hq hL x y draws).2 ≤
      (coarseRootWithWork k q L hB hq hL
        (coarseTargetFrame k (coarsePadTo (coarseEntryWidth x y) y))
        (coarseEntryTree B d x y) draws 0 (coarseRootShift k)).2 +
        coarseRootReadExtra k q L hB hq hL x y draws := by
  let den := coarseRootDenominator B q L d
  let denPos := coarseRootDenominator_pos B q L d hB hq hL
  let two := coarseGridNatWithWork den.1 denPos 2
  let allowance := coarseGridNatWithWork den.1 denPos k
  have h := coarseIndexedWithWork_cost_compare k q L (coarseEntryWidth x y) x y
    two.1 d 0 draws allowance.1 0
  rw [coarseReadCore_eq k q L (coarseEntryWidth x y) x y (le_max_left _ _) (le_max_right _ _)] at h
  simp only [Nat.zero_add, coarseReadTree_entry] at h
  unfold coarseIndexedRootWithWork coarseRootWithWork coarseRootReadExtra
  change den.2 + two.2 + allowance.2 + _ + 1 ≤ den.2 + two.2 + allowance.2 + _ + 1 + _
  dsimp only [den, denPos, two, allowance] at h ⊢
  omega

theorem coarseIndexedCandidateWithWork_cost_compare {B d : ℕ} (q L : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (i : CoarseGuessIndex (coarseEntryWidth x y)) (draws : CoarseThresholdDraws B d) :
    (coarseIndexedCandidateWithWork q L hB hq hL x y i draws).2 ≤
      (coarseCandidateWithWork q L hB hq hL x y i draws).2 +
        coarseRootReadExtra (coarseGuess (coarseEntryWidth x y) i) q L hB hq hL x y draws := by
  have h := coarseIndexedRootWithWork_cost_compare
    (coarseGuess (coarseEntryWidth x y) i) q L hB hq hL x y draws
  unfold coarseIndexedCandidateWithWork coarseCandidateWithWork
  simp only [coarseIndexedRootWithWork_value]
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseIndexedInitialCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

attribute [local irreducible] coarseIndexedCandidateWithWork coarseCandidateWithWork coarseRootReadExtra
  arithmeticMapWithWork coarseMinimumWithWork naturalCeilingWithWork wordMinWithWork

theorem arithmeticMapWithWork_cost_compare {α β : Type*} (f g : α → β × ℕ)
    (extra : α → ℕ) (xs : List α) (hc : ∀ a ∈ xs, (f a).2 ≤ (g a).2 + extra a) :
    (arithmeticMapWithWork f xs).2 ≤ (arithmeticMapWithWork g xs).2 + (xs.map extra).sum := by
  induction xs with
  | nil => simp only [arithmeticMapWithWork, List.map_nil, List.sum_nil, Nat.add_zero, le_refl]
  | cons a xs ih =>
    have ha := hc a List.mem_cons_self
    have hr := ih (fun a ha => hc a (List.mem_cons_of_mem _ ha))
    simp only [arithmeticMapWithWork, List.map_cons, List.sum_cons]
    omega

theorem coarseIndexedInitialWithWork_cost_compare {B d : ℕ} (q L N : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d) :
    (coarseIndexedInitialWithWork q L N hB hq hL x y draws).2 ≤
      (coarseInitialWithWork q L N hB hq hL x y draws).2 +
        coarseInitialReadExtra q L hB hq hL x y draws := by
  let indices := List.finRange (Nat.clog 2 (coarseEntryWidth x y) + 1)
  let f := fun i => coarseIndexedCandidateWithWork q L hB hq hL x y i (draws i)
  let g := fun i => coarseCandidateWithWork q L hB hq hL x y i (draws i)
  let extra := fun i => coarseRootReadExtra (coarseGuess (coarseEntryWidth x y) i)
    q L hB hq hL x y (draws i)
  have hc := arithmeticMapWithWork_cost_compare f g extra indices
    (fun i _ => coarseIndexedCandidateWithWork_cost_compare q L hB hq hL x y i (draws i))
  have hv : (arithmeticMapWithWork f indices).1 = (arithmeticMapWithWork g indices).1 := by
    simp only [arithmeticMapWithWork_value, f, g, coarseIndexedCandidateWithWork_value]
  unfold coarseIndexedInitialWithWork coarseInitialWithWork coarseInitialReadExtra
  dsimp only
  split_ifs
  · omega
  · omega
  · dsimp only [f, g, extra, indices] at hc hv
    rw [hv]
    omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedParameterRegisters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter

 theorem inputLength_register_word (N : ℕ) : Nat.size (N + 2) ≤ inputHeight N + 1 :=
  input_length_bits_le N

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCoarseCandidateWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
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

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCoarseReadBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter

/-- Every descriptor, stored-symbol comparison and frame operation used by a
computed coarse root has a uniform fixed-power bit budget. -/
theorem computedCoarseReadBudget :
    ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N → (∀ a ∈ x ++ y, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ i : CoarseGuessIndex (coarseEntryWidth x y),
      CoarseReadBudget B d (coarseGuess (coarseEntryWidth x y) i) (coarseEntryWidth x y)
        x y (inputHeight N ^ 30) := by
  filter_upwards [eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)] with N hN hell
  intro B d x y hBdef hddef hsize hsymbol i
  let H := inputHeight N
  let k := coarseGuess (coarseEntryWidth x y) i
  have hH : 256 ≤ H := computed_coarse_height_large N (by omega) hell
  have hdepth : d ≤ H := hddef.symm ▸ (computed_coarse_depth N _ (by omega) hsize hell).2
  have hBpos : 1 ≤ B := by
    rw [hBdef]
    change 1 ≤ inputHeight N ^ coarseExponent (inputSmallLog N)
    exact one_le_pow₀ (Nat.succ_le_of_lt (Nat.two_pow_pos _))
  have hb : Nat.size B ≤ 2 * H := by
    have h := Nat.size_le_size (computed_coarse_B_upper N (by omega) hell)
    rw [← hBdef] at h
    simp only [Nat.size_pow] at h
    exact h.trans (by dsimp only [H]; omega)
  have hcube : 100 * H ^ 2 ≤ H ^ 3 := by
    have h := Nat.mul_le_mul_right (H ^ 2) (show 100 ≤ H by omega)
    nlinarith only [h]
  have hp : Nat.size (B ^ d) ≤ H ^ 3 := by
    have h := natural_power_bit_length B d
    have hh := Nat.mul_le_mul hdepth hb
    have hsq := Nat.mul_le_mul_right (H ^ 2) (show 3 ≤ H by omega)
    nlinarith only [h, hh, hsq, hH]
  have hn : Nat.size (coarseEntryWidth x y) ≤ H ^ 3 := by
    have h := (Nat.size_le_size hsize).trans
      ((Nat.size_le_size (Nat.le_add_right N 2)).trans (inputLength_register_word N))
    change Nat.size (coarseEntryWidth x y) ≤ H + 1 at h
    have hpow : H ≤ H ^ 3 := Nat.le_pow (by decide)
    have hsq := Nat.mul_le_mul_right (H ^ 2) (show 3 ≤ H by omega)
    nlinarith only [h, hpow, hsq, hH, hcube]
  have hk : Nat.size (2 * k + 1) ≤ H ^ 3 := by
    have hkn : k ≤ 2 * (N + 2) := (BinaryFraction.coarseGuess_le _ i).trans (by omega)
    have hks := (Nat.size_le_size hkn).trans (natural_product_bit_length 2 (N + 2))
    have hn' := inputLength_register_word N
    change Nat.size (N + 2) ≤ H + 1 at hn'
    have hs := natural_sum_bit_length (2 * k) 1
    have hm := natural_product_bit_length 2 k
    norm_num only [show Nat.size 2 = 2 by decide, show Nat.size 1 = 1 by decide] at hks hs hm
    have hsq := Nat.mul_le_mul_right (H ^ 2) (show 3 ≤ H by omega)
    nlinarith only [hks, hn', hs, hm, hsq, hH, hcube]
  exact coarseReadBudget_height B d k (coarseEntryWidth x y) H x y (by omega) hdepth hBpos
    (by have hpow : H ≤ H ^ 2 := Nat.le_pow (by decide); nlinarith only [hb, hpow, hH, hcube]) hp hn hk hsymbol

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCoarseIndexedWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter
namespace BinaryFraction

attribute [local irreducible] coarseRootReadExtra coarseInitialReadExtra
  coarseIndexedInitialWithWork coarseInitialWithWork

theorem computedCoarseRootReadExtra_bound :
    ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N → (∀ a ∈ x ++ y, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ (hB : 0 < B) (hq : 0 < inputHeight N ^ 4) (hL : 0 < 64 * inputHeight N)
      (i : CoarseGuessIndex (coarseEntryWidth x y)) (draws : CoarseThresholdDraws B d),
      coarseRootReadExtra (coarseGuess (coarseEntryWidth x y) i)
        (inputHeight N ^ 4) (64 * inputHeight N) hB hq hL x y draws ≤
        inputHeight N ^ 32 * (coarseActiveArrayWork (coarseGuess (coarseEntryWidth x y) i)
          (initialThresholdQ N) (initialLambda N) (coarseEntryTree B d x y) draws
          (coarseGuess (coarseEntryWidth x y) i) + 1) := by
  filter_upwards [computedCoarseReadBudget, eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)] with N hbudget hN hell
  intro B d x y hBdef hddef hsize hsymbol hB hq hL i draws
  let H := inputHeight N
  have hH : 100 ≤ H := (by decide : 100 ≤ 256).trans
    (computed_coarse_height_large N (by omega) hell)
  have hc := coarseRootReadExtra_bound (coarseGuess (coarseEntryWidth x y) i)
    (H ^ 4) (64 * H) (H ^ 30) hB hq hL (one_le_pow₀ (by omega)) x y draws
    (hbudget B d x y hBdef hddef hsize hsymbol i)
  have hscale : 64 * H ^ 30 ≤ H ^ 32 := by
    calc
      _ ≤ H ^ 2 * H ^ 30 := Nat.mul_le_mul_right _ (by nlinarith only [hH])
      _ = _ := by rw [← pow_add]
  have hs := Nat.mul_le_mul_right
    (coarseActiveArrayWork (coarseGuess (coarseEntryWidth x y) i) (initialThresholdQ N)
      (initialLambda N) (coarseEntryTree B d x y) draws (coarseGuess (coarseEntryWidth x y) i) + 1) hscale
  simp only [H, initialThresholdQ, initialLambda, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at hc hs ⊢
  nlinarith only [hc, hs]

theorem computedCoarseInitialReadExtra_bound :
    ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N → (∀ a ∈ x ++ y, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ (hB : 0 < B) (hq : 0 < inputHeight N ^ 4) (hL : 0 < 64 * inputHeight N)
      (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d),
      coarseInitialReadExtra (inputHeight N ^ 4) (64 * inputHeight N) hB hq hL x y draws ≤
        inputHeight N ^ 34 * (coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N)
          x y draws + 1) := by
  filter_upwards [computedCoarseRootReadExtra_bound, eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)] with N hroot hN hell
  intro B d x y hBdef hddef hsize hsymbol hB hq hL draws
  let H := inputHeight N
  have hH : 100 ≤ H := (by decide : 100 ≤ 256).trans
    (computed_coarse_height_large N (by omega) hell)
  unfold coarseInitialReadExtra
  split_ifs with hlong hequal
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · have hlong' : ¬ 2 * x.length < y.length :=
      fun h => hlong ((binaryNaturalCompareWithWork_lt _ _).mpr h)
    have hequal' : x ≠ y := fun h => hequal ((naturalListEqualWithWork_value x y).mpr h)
    have hclog : Nat.clog 2 (coarseEntryWidth x y) ≤ H :=
      (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).mpr
        (hsize.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N)))
    have hsum : ((List.finRange (Nat.clog 2 (coarseEntryWidth x y) + 1)).map fun i =>
        coarseRootReadExtra (coarseGuess (coarseEntryWidth x y) i) (inputHeight N ^ 4)
          (64 * inputHeight N) hB hq hL x y (draws i)).sum ≤
        H ^ 32 * (coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N)
          x y draws + (Nat.clog 2 (coarseEntryWidth x y) + 1)) := by
      rw [← List.ofFn_eq_map, List.sum_ofFn]
      calc
        _ ≤ ∑ i : CoarseGuessIndex (coarseEntryWidth x y), H ^ 32 *
            (coarseActiveArrayWork (coarseGuess (coarseEntryWidth x y) i)
              (initialThresholdQ N) (initialLambda N) (coarseEntryTree B d x y) (draws i)
              (coarseGuess (coarseEntryWidth x y) i) + 1) :=
          Finset.sum_le_sum (fun i _ => hroot B d x y hBdef hddef hsize hsymbol hB hq hL i (draws i))
        _ = _ := by
          simp only [coarseInitialArrayWork, ite_eq_right hlong', ite_eq_right hequal',
            ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, smul_eq_mul, mul_one]
    have ha : coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N) x y draws +
        (Nat.clog 2 (coarseEntryWidth x y) + 1) ≤
        H ^ 2 * (coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N) x y draws + 1) := by
      have hs : H + 1 ≤ H ^ 2 := by nlinarith only [hH]
      have hm := Nat.mul_le_mul_right
        (coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N) x y draws)
        (show 1 ≤ H ^ 2 from one_le_pow₀ (by omega))
      nlinarith only [hs, hm, hclog]
    calc
      _ ≤ _ := hsum
      _ ≤ H ^ 32 * (H ^ 2 * (coarseInitialArrayWork B d (initialThresholdQ N)
        (initialLambda N) x y draws + 1)) := Nat.mul_le_mul_left _ ha
      _ = _ := by ring

theorem computedCoarseIndexedInitialWithWork_bound_oai :
    ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N → (∀ a ∈ x ++ y, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ (hB : 0 < B) (hq : 0 < inputHeight N ^ 4) (hL : 0 < 64 * inputHeight N)
      (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d),
      (coarseIndexedInitialWithWork (inputHeight N ^ 4) (64 * inputHeight N) N hB hq hL x y draws).2 ≤
        inputHeight N ^ 40 * (coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N)
          x y draws + x.length + 1) := by
  filter_upwards [computedCoarseInitialWithWork_bound, computedCoarseInitialReadExtra_bound,
    eventually_ge_atTop 1, inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)]
    with N hold hextra hN hell
  intro B d x y hBdef hddef hsize hsymbol hB hq hL draws
  have h1 := hold B d x y hBdef hddef hsize hsymbol hB hq hL draws
  have h2 := hextra B d x y hBdef hddef hsize hsymbol hB hq hL draws
  have hc := coarseIndexedInitialWithWork_cost_compare (inputHeight N ^ 4) (64 * inputHeight N)
    N hB hq hL x y draws
  let H := inputHeight N
  have hH : 100 ≤ H := (by decide : 100 ≤ 256).trans
    (computed_coarse_height_large N (by omega) hell)
  have hp : H ^ 34 ≤ H ^ 36 := Nat.pow_le_pow_right (by omega) (by decide)
  have hs : 2 * H ^ 36 ≤ H ^ 40 := by
    calc
      _ ≤ H ^ 4 * H ^ 36 := Nat.mul_le_mul_right _
        ((by omega : 2 ≤ H).trans (Nat.le_pow (by decide)))
      _ = _ := by rw [← pow_add]
  have hm := Nat.mul_le_mul_right
    (coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N) x y draws + x.length + 1) hs
  have he := Nat.mul_le_mul hp
    (show coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N) x y draws + 1 ≤
      coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N) x y draws + x.length + 1 by omega)
  dsimp only [H] at hm he
  nlinarith only [h1, h2, hc, hm, he]

end BinaryFraction
end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.BinaryFraction.computedCoarseIndexedInitialWithWork_bound_oai := @OAI.EditApproximation.BinaryFraction.computedCoarseIndexedInitialWithWork_bound_oai
