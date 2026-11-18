-- Prove2me | solution 1 for OAI.EditApproximation.BinaryFraction.queryEarlierInputsWithWork_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:33:30.633073+00:00
-- url     : https://prove2.me/submissions/dd281f03-ab7c-4aef-8a49-337e7e3a5915

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
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_queryEarlierRepresentativesWithWork_bounds

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
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
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

theorem gridPointsWithWork_cost (g lo hi B : ℕ) (hg : 0 < g)
    (hgs : Nat.size g ≤ B) (hlo : Nat.size lo ≤ B) (hhi : Nat.size hi ≤ B) :
    (gridPointsWithWork g lo hi).2 ≤ gridPointsBitBudget (gridPointsBetween g lo hi).length B := by
  let lower := bitCeilDivWithWork g.bits lo.bits
  let upper := binaryNaturalDivModWithWork hi g
  let stop := binaryNaturalAddWithWork (bitWordValue upper.1) 1
  let count := saturatingSubtractWithWork (bitWordValue stop.1) (bitWordValue lower.1)
  let indices := List.range' (bitWordValue lower.1) (bitWordValue count.1)
  have hlowers : Nat.size (bitWordValue lower.1) ≤ B + 2 := by
    have h := (wordValue_size_le lower.1).trans (bitCeilDivWithWork_length g.bits lo.bits)
    exact h.trans (by simpa only [Nat.size_eq_bits_len] using Nat.add_le_add_right hlo 2)
  have huppers : Nat.size (bitWordValue upper.1) ≤ B := by
    rw [(binaryNaturalDivModWithWork_spec hi g hg).1]
    exact (Nat.size_le_size (Nat.div_le_self hi g)).trans hhi
  have hstops : Nat.size (bitWordValue stop.1) ≤ B + 3 := by
    rw [binaryNaturalAddWithWork_value]
    have h := binaryNaturalAdd_size_le (bitWordValue upper.1) 1
    have hone : Nat.size 1 = 1 := by decide
    rw [hone] at h
    omega
  have hindex (i : ℕ) (hi' : i ∈ indices) : Nat.size i ≤ B + 3 := by
    have hmem := List.mem_range'.mp hi'
    have hcount : bitWordValue count.1 = bitWordValue stop.1 - bitWordValue lower.1 :=
      saturatingSubtractWithWork_value _ _
    obtain ⟨j, hj, hij⟩ := hmem
    have hle : i ≤ bitWordValue stop.1 := by omega
    exact (Nat.size_le_size hle).trans hstops
  let points := arithmeticMapWithWork (fun i =>
    let product := binaryNaturalMulWithWork g i
    (bitWordValue product.1, product.2 + Nat.size i + 2)) indices
  have hmap := arithmeticMapWithWork_cost (fun i =>
    let product := binaryNaturalMulWithWork g i
    (bitWordValue product.1, product.2 + Nat.size i + 2)) indices
    (100 * (B + 3) ^ 2 + 2) (by
      intro i hi'
      have hcost := binaryNaturalMulWithWork_cost g i
      have his := hindex i hi'
      change (binaryNaturalMulWithWork g i).2 + Nat.size i + 2 ≤ _
      nlinarith only [hcost, hgs, his, Nat.zero_le B])
  have hlength : indices.length = (gridPointsBetween g lo hi).length := by
    have hl : bitWordValue lower.1 = lo ⌈/⌉ g := by
      -- The ceiling start is independent of the upper endpoint.
      rw [bitCeilDivWithWork_value _ _ (by simpa only [bitWordValue_bits] using hg),
        bitWordValue_bits, bitWordValue_bits]
      exact naturalCeiling_div_eq_ceilDiv lo g hg
    simp only [indices, List.length_range', count, saturatingSubtractWithWork_value,
      stop, binaryNaturalAddWithWork_value, upper,
      (binaryNaturalDivModWithWork_spec hi g hg).1, hl, gridPointsBetween_length]
  rw [hlength] at hmap
  change points.2 ≤ _ at hmap
  simp only [Nat.add_assoc, Nat.reduceAdd] at hmap
  have hlcost := bitCeilDivWithWork_cost g.bits lo.bits
  have hucost := binaryNaturalDivModWithWork_cost hi g
  have hscost := binaryNaturalAddWithWork_cost (bitWordValue upper.1) 1
  have hccost := saturatingSubtractWithWork_cost (bitWordValue stop.1) (bitWordValue lower.1)
  simp only [Nat.size_eq_bits_len] at hlcost
  change lower.2 + upper.2.2 + stop.2 + count.2 +
    points.2 + Nat.size g + Nat.size lo + Nat.size hi + 5 ≤ _
  change lower.2 ≤ _ at hlcost
  change upper.2.2 ≤ _ at hucost
  change stop.2 ≤ _ at hscost
  change count.2 ≤ _ at hccost
  have hlpow := Nat.pow_le_pow_left (show Nat.size lo + Nat.size g + 1 ≤ 2 * B + 1 by omega) 2
  have huprod := Nat.mul_le_mul (show Nat.size hi + 1 ≤ B + 1 by omega)
    (show Nat.size hi + Nat.size g + 1 ≤ 2 * B + 1 by omega)
  simp only [Nat.size_one] at hscost
  have hsetup : lower.2 + upper.2.2 + stop.2 + count.2 +
      Nat.size g + Nat.size lo + Nat.size hi + 5 ≤ 1000 * (B + 2) ^ 2 := by
    nlinarith only [hlcost, hucost, hscost, hccost, hlpow, huprod, hgs, hlo, hhi,
      hlowers, huppers, hstops, Nat.zero_le B]
  unfold gridPointsBitBudget
  omega

theorem makeStateWithWork_cost (n lo hi B : ℕ)
    (hn : Nat.size n ≤ B) (hl : Nat.size lo ≤ B) (hh : Nat.size hi ≤ B) :
    (makeStateWithWork n lo hi).2 ≤ 16 * B + 8 := by
  have hfirst := wordLEWithWork_cost lo.bits hi.bits
  have hsecond := wordLEWithWork_cost hi.bits n.bits
  simp only [Nat.size_eq_bits_len] at hfirst hsecond
  unfold makeStateWithWork
  dsimp only
  split_ifs <;> omega

theorem gridStateBoxWithWork_cost (n g radius lo hi B : ℕ) (hg : 0 < g)
    (hn : Nat.size n ≤ B) (hgs : Nat.size g ≤ B) (hr : Nat.size radius ≤ B)
    (hl : Nat.size lo ≤ B) (hh : Nat.size hi ≤ B) :
    (gridStateBoxWithWork n g radius lo hi).2 ≤
      gridStateBoxBitBudget (2 * radius / g + 2) B := by
  let leftLow := saturatingSubtractWithWork lo radius
  let leftHigh := binaryNaturalAddWithWork lo radius
  let rightLow := saturatingSubtractWithWork hi radius
  let rightHigh := binaryNaturalAddWithWork hi radius
  let left := gridPointsWithWork g (bitWordValue leftLow.1) (bitWordValue leftHigh.1)
  let right := gridPointsWithWork g (bitWordValue rightLow.1) (bitWordValue rightHigh.1)
  let count := 2 * radius / g + 2
  have hleft : left.1 = gridPointsBetween g (lo - radius) (lo + radius) := by
    simp only [left, leftLow, leftHigh, gridPointsWithWork_value _ _ _ hg,
      saturatingSubtractWithWork_value, binaryNaturalAddWithWork_value]
  have hright : right.1 = gridPointsBetween g (hi - radius) (hi + radius) := by
    simp only [right, rightLow, rightHigh, gridPointsWithWork_value _ _ _ hg,
      saturatingSubtractWithWork_value, binaryNaturalAddWithWork_value]
  have hlen (p : ℕ) : (gridPointsBetween g (p - radius) (p + radius)).length ≤ count := by
    have h := gridPointsBetween_length_le g (p - radius) (p + radius) hg
    have hsub : p + radius - (p - radius) ≤ 2 * radius := by omega
    exact h.trans (Nat.add_le_add_right (Nat.div_le_div_right hsub) 2)
  have hllen : left.1.length ≤ count := by rw [hleft]; exact hlen lo
  have hrlen : right.1.length ≤ count := by rw [hright]; exact hlen hi
  have hleftWidth (s : ℕ) (hs : s ∈ left.1) : Nat.size s ≤ B + 2 := by
    have hp := (gridPointsBetween_sound hg (hleft ▸ hs)).2.1
    exact (Nat.size_le_size hp).trans ((binaryNaturalAdd_size_le lo radius).trans (by omega))
  have hrightWidth (s : ℕ) (hs : s ∈ right.1) : Nat.size s ≤ B + 2 := by
    have hp := (gridPointsBetween_sound hg (hright ▸ hs)).2.1
    exact (Nat.size_le_size hp).trans ((binaryNaturalAdd_size_le hi radius).trans (by omega))
  have hstate (s : ℕ) (hs : s ∈ left.1) :
      (filterMapWithWork (makeStateWithWork n s) right.1).2 ≤
        count * (16 * (B + 2) + 11) := by
    have h := filterMapWithWork_cost (makeStateWithWork n s) right.1 (16 * (B + 2) + 8)
      (fun t ht => makeStateWithWork_cost n s t (B + 2) (by omega) (hleftWidth s hs) (hrightWidth t ht))
    exact h.trans (Nat.mul_le_mul_right _ hrlen)
  have hstateLen (s : ℕ) : (filterMapWithWork (makeStateWithWork n s) right.1).1.length ≤ count := by
    rw [filterMapWithWork_value]
    exact (List.length_filterMap_le _ _).trans hrlen
  have hflat := arithmeticFlatMapWithWork_cost
    (fun s => filterMapWithWork (makeStateWithWork n s) right.1) left.1
    (count * (16 * (B + 2) + 11)) count hstate (fun s _ => hstateLen s)
  have hflat' := hflat.trans (Nat.mul_le_mul_right _ hllen)
  have hlc := gridPointsWithWork_cost g (bitWordValue leftLow.1) (bitWordValue leftHigh.1) (B + 2) hg
    (by omega) (by rw [saturatingSubtractWithWork_value]; exact (Nat.size_le_size (Nat.sub_le _ _)).trans (by omega))
    (by rw [binaryNaturalAddWithWork_value]; exact (binaryNaturalAdd_size_le lo radius).trans (by omega))
  have hrc := gridPointsWithWork_cost g (bitWordValue rightLow.1) (bitWordValue rightHigh.1) (B + 2) hg
    (by omega) (by rw [saturatingSubtractWithWork_value]; exact (Nat.size_le_size (Nat.sub_le _ _)).trans (by omega))
    (by rw [binaryNaturalAddWithWork_value]; exact (binaryNaturalAdd_size_le hi radius).trans (by omega))
  conv_rhs at hlc =>
    simp only [leftLow, leftHigh, saturatingSubtractWithWork_value, binaryNaturalAddWithWork_value]
  conv_rhs at hrc =>
    simp only [rightLow, rightHigh, saturatingSubtractWithWork_value, binaryNaturalAddWithWork_value]
  have hlc' : left.2 ≤ gridPointsBitBudget count (B + 2) := by
    apply hlc.trans
    unfold gridPointsBitBudget
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (hlen lo)) _
  have hrc' : right.2 ≤ gridPointsBitBudget count (B + 2) := by
    apply hrc.trans
    unfold gridPointsBitBudget
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (hlen hi)) _
  have hll := saturatingSubtractWithWork_cost lo radius
  have hlh := binaryNaturalAddWithWork_cost lo radius
  have hrl := saturatingSubtractWithWork_cost hi radius
  have hrh := binaryNaturalAddWithWork_cost hi radius
  change leftLow.2 ≤ _ at hll
  change leftHigh.2 ≤ _ at hlh
  change rightLow.2 ≤ _ at hrl
  change rightHigh.2 ≤ _ at hrh
  let states := arithmeticFlatMapWithWork (fun s => filterMapWithWork (makeStateWithWork n s) right.1) left.1
  change states.2 ≤ _ at hflat'
  change leftLow.2 + leftHigh.2 + rightLow.2 + rightHigh.2 + left.2 + right.2 + states.2 + 6 ≤ _
  unfold gridStateBoxBitBudget
  change _ ≤ 96 * (B + 1) + 2 * gridPointsBitBudget count (B + 2) +
    count * (count * (16 * (B + 2) + 11) + count + 3) + 6
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryWideGridWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial per-child bit work before the explicitly counted Cartesian
product. All interval endpoints and arities are bounded by their input
word sizes; no good-seed premise occurs in these bounds. -/

namespace EditApproximation

theorem balancedCutWithWork_cost (lo width M i B : ℕ) (hM : 0 < M)
    (hl : Nat.size lo ≤ B) (hw : Nat.size width ≤ B)
    (hm : Nat.size M ≤ B) (hi : Nat.size i ≤ B) :
    (balancedCutWithWork lo width M i).2 ≤ 1000 * (B + 1) ^ 2 := by
  let product := binaryNaturalMulWithWork i width
  let quotient := binaryNaturalDivModWithWork (bitWordValue product.1) M
  have hp := binaryNaturalMulWithWork_cost i width
  have hpl := bitMulWithWork_length i.bits width.bits
  have hps : Nat.size (bitWordValue product.1) ≤ 3 * B + 1 := by
    have hv : Nat.size (bitWordValue product.1) ≤ product.1.length :=
      Nat.size_le.mpr (bitWordValue_lt_pow_length _)
    change product.1.length ≤ _ at hpl
    simp only [Nat.size_eq_bits_len] at hpl
    omega
  have hq := binaryNaturalDivModWithWork_cost (bitWordValue product.1) M
  have hqs : Nat.size (bitWordValue quotient.1) ≤ 3 * B + 1 := by
    rw [(binaryNaturalDivModWithWork_spec _ M hM).1]
    exact (Nat.size_le_size (Nat.div_le_self _ _)).trans hps
  have ha := binaryNaturalAddWithWork_cost lo (bitWordValue quotient.1)
  change product.2 + quotient.2.2 + (binaryNaturalAddWithWork lo (bitWordValue quotient.1)).2 + 2 ≤ _
  nlinarith only [hp, hq, ha, hps, hqs, hl, hw, hm, hi, Nat.zero_le B]

theorem sourceChildWithWork_cost {n M : ℕ} (parent : TargetInterval n) (i : Fin M)
    (B : ℕ) (hn : Nat.size n ≤ B) (hm : Nat.size M ≤ B) :
    (sourceChildWithWork parent i).2 ≤ 2200 * (B + 3) ^ 2 := by
  have hlo := (Nat.size_le_size (parent.ordered.trans parent.valid)).trans hn
  have hhi := (Nat.size_le_size parent.valid).trans hn
  have hi := (Nat.size_le_size i.isLt.le).trans hm
  let width := saturatingSubtractWithWork parent.hi parent.lo
  let next := binaryNaturalAddWithWork i.val 1
  have hwidth : Nat.size (bitWordValue width.1) ≤ B := by
    rw [saturatingSubtractWithWork_value]
    exact (Nat.size_le_size (Nat.sub_le _ _)).trans hhi
  have hnext : Nat.size (bitWordValue next.1) ≤ B + 2 := by
    rw [binaryNaturalAddWithWork_value]
    have h := binaryNaturalAdd_size_le i.val 1
    simp only [Nat.size_one] at h
    have hMpos : 1 ≤ Nat.size M := Nat.size_pos.mpr (Nat.zero_lt_of_lt i.isLt)
    omega
  have hleft := balancedCutWithWork_cost parent.lo (bitWordValue width.1) M i.val (B + 2)
    (Nat.zero_lt_of_lt i.isLt) (by omega) (by omega) (by omega) (by omega)
  have hright := balancedCutWithWork_cost parent.lo (bitWordValue width.1) M
    (bitWordValue next.1) (B + 2) (Nat.zero_lt_of_lt i.isLt)
    (by omega) (by omega) (by omega) hnext
  have hsub := saturatingSubtractWithWork_cost parent.hi parent.lo
  have hadd := binaryNaturalAddWithWork_cost i.val 1
  change width.2 + next.2 + _ + _ + 4 ≤ _
  change width.2 ≤ _ at hsub
  change next.2 ≤ _ at hadd
  simp only [Nat.size_one] at hadd
  nlinarith only [hleft, hright, hsub, hadd, hlo, hhi, hi, Nat.zero_le B]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryWideChildWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
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

theorem gridStateBoxBitBudget_mono_count (k l B : ℕ) (h : k ≤ l) :
    gridStateBoxBitBudget k B ≤ gridStateBoxBitBudget l B := by
  unfold gridStateBoxBitBudget gridPointsBitBudget
  gcongr

theorem wideChildGridWithWork_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P B : ℕ) (i : Fin M) (hPpos : 0 < P)
    (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (hM : Nat.size M ≤ B) (hb : Nat.size b ≤ B) (hP : Nat.size P ≤ B) :
    (wideChildGridWithWork parent r b P i).2 ≤ wideChildGridBitBudget P B := by
  let child := sourceChildWithWork parent i
  let spacing := seedGridSpacingWithWork b P
  let radius := binaryNaturalMulWithWork 10 b
  let leftOffset := saturatingSubtractWithWork child.1.lo parent.lo
  let rightOffset := saturatingSubtractWithWork child.1.hi parent.lo
  let left := binaryNaturalAddWithWork r.lo (bitWordValue leftOffset.1)
  let right := binaryNaturalAddWithWork r.lo (bitWordValue rightOffset.1)
  have hparent : Nat.size parent.lo ≤ B :=
    (Nat.size_le_size (parent.ordered.trans parent.valid)).trans hnx
  have hcl : Nat.size child.1.lo ≤ B :=
    (Nat.size_le_size (child.1.ordered.trans child.1.valid)).trans hnx
  have hch : Nat.size child.1.hi ≤ B := (Nat.size_le_size child.1.valid).trans hnx
  have hrlo : Nat.size r.lo ≤ B := (Nat.size_le_size (r.ordered.trans r.valid)).trans hny
  have hlo : Nat.size (bitWordValue leftOffset.1) ≤ B := by
    rw [saturatingSubtractWithWork_value]
    exact (Nat.size_le_size (Nat.sub_le _ _)).trans hcl
  have hro : Nat.size (bitWordValue rightOffset.1) ≤ B := by
    rw [saturatingSubtractWithWork_value]
    exact (Nat.size_le_size (Nat.sub_le _ _)).trans hch
  have hleft : Nat.size (bitWordValue left.1) ≤ B + 2 := by
    rw [binaryNaturalAddWithWork_value]
    exact (binaryNaturalAdd_size_le _ _).trans (by omega)
  have hright : Nat.size (bitWordValue right.1) ≤ B + 2 := by
    rw [binaryNaturalAddWithWork_value]
    exact (binaryNaturalAdd_size_le _ _).trans (by omega)
  have hspacing := seedGridSpacingWithWork_bounds b P B hb hP
  have hspacingCost : spacing.2 ≤ 100 * (B + 2) ^ 2 := hspacing.2
  have hgs : Nat.size (bitWordValue spacing.1) ≤ B + 1 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length spacing.1)).trans hspacing.1
  have hrl := bitMulWithWork_length (10 : ℕ).bits b.bits
  change radius.1.length ≤ _ at hrl
  simp only [Nat.size_eq_bits_len] at hrl
  have hten : Nat.size 10 = 4 := by decide
  rw [hten] at hrl
  have hrs : Nat.size (bitWordValue radius.1) ≤ B + 9 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length radius.1)).trans (by omega)
  have hg := seedGridSpacingWithWork_pos b P hPpos
  have hgrid := gridStateBoxWithWork_cost ny (bitWordValue spacing.1) (bitWordValue radius.1)
    (bitWordValue left.1) (bitWordValue right.1) (B + 12) hg
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have hcount : 2 * bitWordValue radius.1 / bitWordValue spacing.1 + 2 ≤ 40 * P + 2 := by
    rw [binaryNaturalMulWithWork_value, seedGridSpacingWithWork_value b P hPpos]
    simpa only [show 2 * (10 * b) = 20 * b by omega] using seedGridSpacing_radius_count b P hPpos
  have hgrid' := hgrid.trans (gridStateBoxBitBudget_mono_count _ _ (B + 12) hcount)
  have hc := sourceChildWithWork_cost parent i B hnx hM
  have hrad := binaryNaturalMulWithWork_cost 10 b
  have hol := saturatingSubtractWithWork_cost child.1.lo parent.lo
  have hor := saturatingSubtractWithWork_cost child.1.hi parent.lo
  have hal := binaryNaturalAddWithWork_cost r.lo (bitWordValue leftOffset.1)
  have har := binaryNaturalAddWithWork_cost r.lo (bitWordValue rightOffset.1)
  change child.2 ≤ _ at hc
  change radius.2 ≤ _ at hrad
  change leftOffset.2 ≤ _ at hol
  change rightOffset.2 ≤ _ at hor
  change left.2 ≤ _ at hal
  change right.2 ≤ _ at har
  rw [hten] at hrad
  change child.2 + spacing.2 + radius.2 + leftOffset.2 + rightOffset.2 + left.2 + right.2 + _ + 8 ≤ _
  unfold wideChildGridBitBudget
  nlinarith only [hc, hspacingCost, hrad, hol, hor, hal, har, hgrid', hcl, hch, hparent,
    hrlo, hlo, hro, hb, Nat.zero_le B]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_CurrentQueryInputs
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Distinct current-index inputs of the bounded query loops. The cover
includes all whole-cell shared estimates, selected cell actions, and
online actions; repeated uses do not add recursive calls. -/

namespace EditApproximation

open Finset



theorem localGroupQueryKeys_scale {n N F exponent : ℕ} {a : ℚ}
    {initial : TargetInterval n → ℚ} {q : TargetInterval n} {key : ℕ × (ℕ × ℕ)}
    (hkey : key ∈ localGroupQueryKeys N F exponent a initial q) :
    key.1 ∈ dyadicScales N := by
  obtain ⟨b, hb, hcell⟩ := List.mem_flatMap.mp hkey
  obtain ⟨cell, _, rfl⟩ := List.mem_map.mp hcell
  exact (List.mem_filter.mp hb).1

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

theorem arithmeticFlatMapWithWork_factor {α β : Type*} (read plain : α → List β × ℕ)
    (xs : List α) (K : ℕ) (hK : 1 ≤ K)
    (hvalue : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hcost : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 * K) :
    (arithmeticFlatMapWithWork read xs).1 = (arithmeticFlatMapWithWork plain xs).1 ∧
      (arithmeticFlatMapWithWork read xs).2 ≤ (arithmeticFlatMapWithWork plain xs).2 * K := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [arithmeticFlatMapWithWork, Nat.zero_mul, le_refl]⟩
  | cons x xs ih =>
    have hv := hvalue x List.mem_cons_self
    have hc := hcost x List.mem_cons_self
    have ht := ih (fun y hy => hvalue y (List.mem_cons_of_mem _ hy))
      (fun y hy => hcost y (List.mem_cons_of_mem _ hy))
    constructor
    · simp only [arithmeticFlatMapWithWork, hv, ht.1]
    · simp only [arithmeticFlatMapWithWork, hv]
      have hl : (plain x).1.length ≤ (plain x).1.length * K := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (plain x).1.length hK
      nlinarith only [hc, ht.2, hl, hK]

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCellReads
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalUniformLaw_probability
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

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRepresentativeReads
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalUniformLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Query-local representative construction reads its finite initial
table explicitly. Each center lookup is charged before testing it. -/

namespace EditApproximation
namespace BinaryFraction



theorem representativeScaleReadWithWork_eq_cost {n : ℕ} (P F : ℕ) (a : BinaryFraction)
    (read : TargetInterval n → BinaryFraction × ℕ) (radius : List Bool)
    (query : TargetInterval n) (e R : ℕ) (hR : ∀ r, (read r).2 ≤ R) :
    (representativeScaleReadWithWork P F a read radius query e).1 =
      (representativeScalePlainWithWork P F a (fun r => (read r).1) radius query e).1 ∧
    (representativeScaleReadWithWork P F a read radius query e).2 ≤
      (representativeScalePlainWithWork P F a (fun r => (read r).1) radius query e).2 * (R + 1) := by
  let spacing := seedGridSpacingWithWork (2 ^ e) P
  let points := gridStateBoxWithWork n (bitWordValue spacing.1) (bitWordValue radius) query.lo query.hi
  have h := filterWithWork_add_read (fun r => centerEligibilityWithWork (2 ^ e) F a (read r).1)
    (fun r => (read r).2) points.1 R (fun r _ => hR r)
  constructor
  · simp only [representativeScaleReadWithWork, representativeScalePlainWithWork, spacing, points, h.1]
  · unfold representativeScaleReadWithWork representativeScalePlainWithWork
    change spacing.2 + points.2 + _ + _ + e + 5 ≤ (spacing.2 + points.2 + _ + _ + e + 5) * _
    rw [h.1]
    nlinarith only [h.2]



theorem localRepresentativeReadWithWork_eq_cost {n : ℕ} (N P F : ℕ) (a : BinaryFraction)
    (read : TargetInterval n → BinaryFraction × ℕ) (query : TargetInterval n)
    (R : ℕ) (hR : ∀ r, (read r).2 ≤ R) :
    (localRepresentativeReadWithWork N P F a read query).1 =
      (localRepresentativesWithWork N P F a (fun r => (read r).1) query).1 ∧
    (localRepresentativeReadWithWork N P F a read query).2 ≤
      (localRepresentativesWithWork N P F a (fun r => (read r).1) query).2 * (R + 2) := by
  let scales := queryExponentsWithWork N F a (read query).1
  let radius := naturalCeilingWithWork (read query).1
  let plain := representativeScalePlainWithWork P F a (fun r => (read r).1) radius.1 query
  let withRead := representativeScaleReadWithWork P F a read radius.1 query
  have h := arithmeticFlatMapWithWork_factor withRead plain scales.1 (R + 1) (by omega)
    (fun e _ => (representativeScaleReadWithWork_eq_cost P F a read radius.1 query e R hR).1)
    (fun e _ => (representativeScaleReadWithWork_eq_cost P F a read radius.1 query e R hR).2)
  have hquery := hR query
  constructor
  · exact h.1
  · change (read query).2 + scales.2 + radius.2 +
      (arithmeticFlatMapWithWork withRead scales.1).2 + 3 ≤
      (scales.2 + radius.2 + (arithmeticFlatMapWithWork plain scales.1).2 + 3) * (R + 2)
    nlinarith only [h.2, hquery]

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
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value
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
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value
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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInitialSupport
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryOrderedChildInputsWithWork_value _root_.OAI.EditApproximation.queryOrderedHistoryInputsWithWork_value _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.triangularMassWithWork_value
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
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
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



theorem queryEarlierRepresentativesWithWork_value {n : ℕ} (N P F exponent : ℕ)
    (hP : 0 < P) (a : BinaryFraction) (initial : TargetInterval n → BinaryFraction × ℕ)
    (q : TargetInterval n) (R : ℕ) (hR : ∀ r, (initial r).2 ≤ R) :
    (queryEarlierRepresentativesWithWork N P F exponent hP a initial q).1 =
      queryEarlierRepresentatives N P F exponent a.value (fun r => (initial r).1.value) q := by
  have hl := (localRepresentativeReadWithWork_eq_cost N P F a initial q R hR).1
  have hc (b : ℕ) (cell : ℕ × ℕ) :=
    (cellCentersReadWithWork_eq_cost P F b a (inversePowerTwo exponent) initial cell R hR).1
  simp only [queryEarlierRepresentativesWithWork, hl, hc, localRepresentativesWithWork_value _ _ _ hP,
    arithmeticFlatMapWithWork_value, arithmeticMapWithWork_value,
    cellCentersWithWork_value _ _ _ _ _ _ _ hP, inversePowerTwo_value,
    queryGroupKeysWithWork_value, queryOnlineKeysWithWork_value,
    queryEarlierRepresentatives, localGroupQueryKeys, localOnlineSourceKeys]



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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryHistoryBounds
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cost of generating the earlier-history input list from child grids.
The bound counts the actual nested lists before duplicate removal. -/

namespace EditApproximation

theorem arithmeticFlatMapWithWork_length {α β : Type*} (f : α → List β × ℕ)
    (xs : List α) (L : ℕ) (hL : ∀ x ∈ xs, (f x).1.length ≤ L) :
    (arithmeticFlatMapWithWork f xs).1.length ≤ xs.length * L := by
  induction xs with
  | nil => simp only [arithmeticFlatMapWithWork, List.length_nil, Nat.zero_mul, le_rfl]
  | cons x xs ih =>
    have hx := hL x List.mem_cons_self
    have ht := ih (fun y hy => hL y (List.mem_cons_of_mem _ hy))
    simp only [arithmeticFlatMapWithWork, List.length_append, List.length_cons,
      Nat.add_mul, Nat.one_mul]
    omega

namespace BinaryFraction

section History
variable {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx) (P history : ℕ)
  (representatives : List (ℕ × TargetInterval ny)) (G C : ℕ)
  (hgrid : ∀ br ∈ representatives, ∀ i : Fin M,
    (wideChildGridWithWork parent br.2 br.1 P i).1.length ≤ G)
  (hwork : ∀ br ∈ representatives, ∀ i : Fin M,
    (wideChildGridWithWork parent br.2 br.1 P i).2 ≤ C)

include hgrid hwork in
private theorem historyChildRun_bounds (br : ℕ × TargetInterval ny) (hbr : br ∈ representatives)
    (i : Fin M) :
    (historyChildRun M parent P history br i).1.length ≤ history * G ∧
    (historyChildRun M parent P history br i).2 ≤ C + history * (5 * G + 3) + history + 2 := by
  let states := wideChildGridWithWork parent br.2 br.1 P i
  have hs : states.1.length ≤ G := hgrid br hbr i
  have hc : states.2 ≤ C := hwork br hbr i
  have hlen (t : ℕ) :
      (arithmeticMapWithWork (fun r => ((i, t, r), 1)) states.1).1.length ≤ G := by
    simpa only [arithmeticMapWithWork_value, List.length_map] using hs
  have hcost (t : ℕ) :
      (arithmeticMapWithWork (fun r => ((i, t, r), 1)) states.1).2 ≤ 4 * G := by
    have h := arithmeticMapWithWork_cost (fun r => ((i, t, r), 1)) states.1 1 (fun _ _ => le_rfl)
    simpa only [Nat.reduceAdd, Nat.mul_comm] using h.trans (Nat.mul_le_mul_right 4 hs)
  have hl := arithmeticFlatMapWithWork_length
    (fun t => arithmeticMapWithWork (fun r => ((i, t, r), 1)) states.1)
    (List.range history) G (fun t _ => hlen t)
  have hw := arithmeticFlatMapWithWork_cost
    (fun t => arithmeticMapWithWork (fun r => ((i, t, r), 1)) states.1)
    (List.range history) (4 * G) G (fun t _ => hcost t) (fun t _ => hlen t)
  simp only [List.length_range] at hl hw
  refine ⟨hl, ?_⟩
  change states.2 + (arithmeticFlatMapWithWork
    (fun t => arithmeticMapWithWork (fun r => ((i, t, r), 1)) states.1)
    (List.range history)).2 + history + 2 ≤ _
  have heq : 4 * G + G + 3 = 5 * G + 3 := by omega
  rw [heq] at hw
  omega

include hgrid hwork in
theorem queryRawHistoryInputsWithWork_bounds :
    (queryRawHistoryInputsWithWork M parent P history representatives).1.length ≤
      representatives.length * (M * (history * G)) ∧
    (queryRawHistoryInputsWithWork M parent P history representatives).2 ≤
      representatives.length *
        (M * (C + history * (5 * G + 3) + history + 2 + history * G + 3) +
          M * (history * G) + 3) + M + 1 := by
  let run := fun br : ℕ × TargetInterval ny => arithmeticFlatMapWithWork (historyChildRun M parent P history br) (List.finRange M)
  have one (br : ℕ × TargetInterval ny) (hbr : br ∈ representatives) :
      (run br).1.length ≤ M * (history * G) ∧
      (run br).2 ≤ M * (C + history * (5 * G + 3) + history + 2 + history * G + 3) := by
    have hl := arithmeticFlatMapWithWork_length (historyChildRun M parent P history br)
      (List.finRange M) (history * G)
      (fun i _ => (historyChildRun_bounds M parent P history representatives G C hgrid hwork br hbr i).1)
    have hw := arithmeticFlatMapWithWork_cost (historyChildRun M parent P history br)
      (List.finRange M) (C + history * (5 * G + 3) + history + 2) (history * G)
      (fun i _ => (historyChildRun_bounds M parent P history representatives G C hgrid hwork br hbr i).2)
      (fun i _ => (historyChildRun_bounds M parent P history representatives G C hgrid hwork br hbr i).1)
    simpa only [List.length_finRange] using And.intro hl hw
  have hl := arithmeticFlatMapWithWork_length run representatives (M * (history * G))
    (fun br hbr => (one br hbr).1)
  have hw := arithmeticFlatMapWithWork_cost run representatives
    (M * (C + history * (5 * G + 3) + history + 2 + history * G + 3)) (M * (history * G))
    (fun br hbr => (one br hbr).2) (fun br hbr => (one br hbr).1)
  exact ⟨hl, Nat.add_le_add_right (Nat.add_le_add_right hw M) 1⟩

end History
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryScopedOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sorting costs only require bounded comparisons between keys actually
present in the input.  This is needed for the natural-valued history time. -/

namespace EditApproximation

theorem memberByWithWork_cost_on {α : Type*} (P : α → Prop)
    (equal : α → α → Bool × ℕ) (C : ℕ)
    (hC : ∀ a, P a → ∀ b, P b → (equal a b).2 ≤ C)
    (a : α) (ha : P a) (xs : List α) (hx : ∀ b ∈ xs, P b) :
    (memberByWithWork equal a xs).2 ≤ 1 + xs.length * (C + 1) := by
  induction xs with
  | nil => simp only [memberByWithWork, List.length_nil, Nat.zero_mul, Nat.add_zero, le_refl]
  | cons b xs ih =>
    have h := hC a ha b (hx b (by simp))
    have ht := ih (fun c hc => hx c (List.mem_cons_of_mem b hc))
    change _ + _ + 1 ≤ _
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem queryEraseLoopWithWork_cost_on {α : Type*} (P : α → Prop)
    (equal : α → α → Bool × ℕ) (C : ℕ)
    (hC : ∀ a, P a → ∀ b, P b → (equal a b).2 ≤ C)
    (xs seen : List α) (hx : ∀ a ∈ xs, P a) (hs : ∀ a ∈ seen, P a) :
    (queryEraseLoopWithWork equal xs seen).2 ≤
      (xs.length + 1) * (xs.length + seen.length + 1) * (C + 4) := by
  induction xs generalizing seen with
  | nil =>
    simp only [queryEraseLoopWithWork, List.length_nil, zero_add, one_mul]
    nlinarith
  | cons a xs ih =>
    have ha := hx a (by simp)
    have hm := memberByWithWork_cost_on P equal C hC a ha seen hs
    let next := if (memberByWithWork equal a seen).1 then seen else a :: seen
    have hn : ∀ b ∈ next, P b := by
      intro b hb
      dsimp only [next] at hb
      split_ifs at hb
      · exact hs b hb
      · rcases List.mem_cons.mp hb with rfl | hb
        · exact ha
        · exact hs b hb
    have hl : next.length ≤ seen.length + 1 := by
      dsimp only [next]
      split <;> (try simp only [List.length_cons]) <;> omega
    have hi := ih next (fun b hb => hx b (List.mem_cons_of_mem a hb)) hn
    have hh : (queryEraseLoopWithWork equal xs next).2 ≤
        (xs.length + 1) * (xs.length + (seen.length + 1) + 1) * (C + 4) :=
      hi.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))
    change (memberByWithWork equal a seen).2 + (queryEraseLoopWithWork equal xs next).2 + 2 ≤ _
    simp only [List.length_cons]
    nlinarith only [hm, hh, Nat.zero_le xs.length, Nat.zero_le seen.length, Nat.zero_le C]

theorem queryEraseWithWork_cost_on {α : Type*} (P : α → Prop)
    (equal : α → α → Bool × ℕ) (C : ℕ)
    (hC : ∀ a, P a → ∀ b, P b → (equal a b).2 ≤ C)
    (xs : List α) (hx : ∀ a ∈ xs, P a) :
    (queryEraseWithWork equal xs).2 ≤ (xs.length + 1) ^ 2 * (C + 4) := by
  simpa only [queryEraseWithWork, List.length_nil, Nat.add_zero, pow_two] using
    queryEraseLoopWithWork_cost_on P equal C hC xs [] hx (by simp)

theorem queryInsertWithWork_cost_on {α : Type*} (P : α → Prop)
    (le : α → α → Bool × ℕ) (C : ℕ)
    (hC : ∀ a, P a → ∀ b, P b → (le a b).2 ≤ C)
    (a : α) (ha : P a) (xs : List α) (hx : ∀ b ∈ xs, P b) :
    (queryInsertWithWork le a xs).2 ≤ (xs.length + 1) * (C + 2) := by
  induction xs with
  | nil => simp only [queryInsertWithWork, List.length_nil]; omega
  | cons b xs ih =>
    have h := hC a ha b (hx b (by simp))
    have ht := ih (fun c hc => hx c (List.mem_cons_of_mem b hc))
    simp only [queryInsertWithWork, List.length_cons]
    split <;> dsimp only
    · nlinarith only [h, Nat.zero_le xs.length, Nat.zero_le C]
    · nlinarith only [h, ht]

theorem querySortWithWork_cost_on {α : Type*} (P : α → Prop)
    (r : α → α → Prop) [DecidableRel r]
    (le : α → α → Bool × ℕ) (hle : ∀ a b, (le a b).1 = decide (r a b))
    (C : ℕ) (hC : ∀ a, P a → ∀ b, P b → (le a b).2 ≤ C)
    (xs : List α) (hx : ∀ a ∈ xs, P a) :
    (querySortWithWork le xs).2 ≤ (xs.length + 1) ^ 2 * (C + 3) := by
  induction xs with
  | nil => simp only [querySortWithWork, List.length_nil]; omega
  | cons a xs ih =>
    have ht := ih (fun b hb => hx b (List.mem_cons_of_mem a hb))
    have hs : ∀ b ∈ (querySortWithWork le xs).1, P b := by
      intro b hb
      rw [querySortWithWork_value r le hle, List.mem_insertionSort] at hb
      exact hx b (List.mem_cons_of_mem a hb)
    have hi := queryInsertWithWork_cost_on P le C hC a (hx a (by simp))
      (querySortWithWork le xs).1 hs
    have hl : (querySortWithWork le xs).1.length = xs.length := by
      rw [querySortWithWork_value r le hle, List.length_insertionSort]
    rw [hl] at hi
    change (querySortWithWork le xs).2 + _ + 1 ≤ _
    simp only [List.length_cons]
    nlinarith only [ht, hi, Nat.zero_le xs.length, Nat.zero_le C]

theorem queryOrderedInputsWithWork_cost_on {α : Type*} [DecidableEq α]
    (P : α → Prop) (encode : α → ℕ) (equal le : α → α → Bool × ℕ)
    (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (hle : ∀ a b, (le a b).1 = decide (encode a ≤ encode b))
    (C D : ℕ) (hequal : ∀ a, P a → ∀ b, P b → (equal a b).2 ≤ C)
    (horder : ∀ a, P a → ∀ b, P b → (le a b).2 ≤ D)
    (xs : List α) (hx : ∀ a ∈ xs, P a) :
    (queryOrderedInputsWithWork equal le xs).2 ≤ (xs.length + 1) ^ 2 * (C + D + 8) := by
  have he := queryEraseWithWork_cost_on P equal C hequal xs hx
  have hu : ∀ a ∈ (queryEraseWithWork equal xs).1, P a := by
    intro a ha
    rw [queryEraseWithWork_value equal heq, List.mem_eraseDups] at ha
    exact hx a ha
  have hs := querySortWithWork_cost_on P (fun a b => encode a ≤ encode b)
    le hle D horder (queryEraseWithWork equal xs).1 hu
  have hl := queryEraseWithWork_length equal xs
  have hp : ((queryEraseWithWork equal xs).1.length + 1) ^ 2 ≤ (xs.length + 1) ^ 2 := by
    gcongr
  have hb := hs.trans (Nat.mul_le_mul_right (D + 3) hp)
  change (queryEraseWithWork equal xs).2 + _ + 1 ≤ _
  nlinarith only [he, hb, Nat.zero_le C, Nat.zero_le D, Nat.zero_le xs.length]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryHistoryCodeBounds
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word and comparison bounds for the actual finite history-key lists. -/

namespace EditApproximation

theorem queryPairWithWork_bounds (a b B : ℕ) (ha : Nat.size a ≤ B) (hb : Nat.size b ≤ B) :
    Nat.size (queryPairWithWork a b).1 ≤ 5 * (B + 1) ∧
      (queryPairWithWork a b).2 ≤ 10000 * (B + 1) ^ 2 := by
  have haa : Nat.size (a * a) ≤ 3 * B + 1 := by
    have h := queryNaturalMul_size a a
    omega
  have hbb : Nat.size (b * b) ≤ 3 * B + 1 := by
    have h := queryNaturalMul_size b b
    omega
  have hl : Nat.size (a * a + a) ≤ 4 * B + 2 := by
    have h := queryNaturalAdd_size (a * a) a
    omega
  have ho : Nat.size (a * a + a + b) ≤ 5 * B + 3 := by
    have h := queryNaturalAdd_size (a * a + a) b
    omega
  have hp : Nat.size (b * b + a) ≤ 4 * B + 2 := by
    have h := queryNaturalAdd_size (b * b) a
    omega
  let K := 5 * (B + 1)
  have haK : Nat.size a ≤ K := by dsimp [K]; omega
  have hbK : Nat.size b ≤ K := by dsimp [K]; omega
  have haaK : Nat.size (a * a) ≤ K := by dsimp [K]; omega
  have hbbK : Nat.size (b * b) ≤ K := by dsimp [K]; omega
  have hlK : Nat.size (a * a + a) ≤ K := by dsimp [K]; omega
  have ca := queryNaturalMul_cost a a K haK haK
  have cb := queryNaturalMul_cost b b K hbK hbK
  have cl := queryNaturalAdd_cost (a * a) a K haaK haK
  have co := queryNaturalAdd_cost (a * a + a) b K hlK hbK
  have cp := queryNaturalAdd_cost (b * b) a K hbbK haK
  have ct := binaryNaturalCompareWithWork_cost a b
  dsimp only [K] at ca cb cl co cp
  unfold queryPairWithWork
  dsimp only
  split_ifs <;> simp only [binaryNaturalMulWithWork_value, binaryNaturalAddWithWork_value]
  · exact ⟨by omega, by nlinarith only [cb, cp, ct, ha, hb, Nat.zero_le B]⟩
  · exact ⟨by omega, by nlinarith only [ca, cl, co, ct, ha, hb, Nat.zero_le B]⟩

theorem queryHistoryCodeWithWork_bounds {M n : ℕ} (input : Fin M × ℕ × TargetInterval n)
    (B : ℕ) (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) (ht : Nat.size input.2.1 ≤ B) :
    Nat.size (queryHistoryCodeWithWork input).1 ≤ 50 * (B + 1) ∧
      (queryHistoryCodeWithWork input).2 ≤ 1000000 * (B + 1) ^ 2 := by
  have hc := queryChildCodeWithWork_bounds (input.1, input.2.2) B hM hn
  have ht' : Nat.size input.2.1 ≤ 8 * (B + 1) := by omega
  have hp := queryPairWithWork_bounds input.2.1
    (queryChildCodeWithWork (input.1, input.2.2)).1 (8 * (B + 1)) ht' hc.1
  constructor
  · exact hp.1.trans (by omega)
  · change (queryChildCodeWithWork (input.1, input.2.2)).2 +
      (queryPairWithWork input.2.1 (queryChildCodeWithWork (input.1, input.2.2)).1).2 + 1 ≤ _
    nlinarith only [hc.2, hp.2, Nat.zero_le B]

theorem queryHistoryEqualWithWork_cost {M n : ℕ} (a b : Fin M × ℕ × TargetInterval n)
    (B : ℕ) (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B)
    (ha : Nat.size a.2.1 ≤ B) (hb : Nat.size b.2.1 ≤ B) :
    (queryHistoryEqualWithWork a b).2 ≤ 32 * B + 11 := by
  have hc := coordinateEqualWithWork_cost (a.1, a.2.2) (b.1, b.2.2) B hM hn
  have ht := naturalEqualWithWork_cost a.2.1 b.2.1 B ha hb
  change _ + _ + 1 ≤ _
  omega

theorem queryHistoryOrderWithWork_cost {M n : ℕ} (a b : Fin M × ℕ × TargetInterval n)
    (B : ℕ) (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B)
    (ha : Nat.size a.2.1 ≤ B) (hb : Nat.size b.2.1 ≤ B) :
    (queryEncodedLEWithWork queryHistoryCodeWithWork a b).2 ≤ 2001000 * (B + 1) ^ 2 := by
  have ca := queryHistoryCodeWithWork_bounds a B hM hn ha
  have cb := queryHistoryCodeWithWork_bounds b B hM hn hb
  have h := queryEncodedLEWithWork_cost queryHistoryCodeWithWork a b
    (1000000 * (B + 1) ^ 2) (50 * (B + 1)) ca.2 cb.2 ca.1 cb.1
  nlinarith only [h, Nat.zero_le B]

theorem queryOrderedHistoryInputsWithWork_cost {M n : ℕ}
    (inputs : List (Fin M × ℕ × TargetInterval n)) (B : ℕ)
    (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B)
    (ht : ∀ input ∈ inputs, Nat.size input.2.1 ≤ B) :
    (queryOrderedHistoryInputsWithWork inputs).2 ≤
      (inputs.length + 1) ^ 2 * (2002000 * (B + 1) ^ 2) := by
  have h := queryOrderedInputsWithWork_cost_on (fun input : Fin M × ℕ × TargetInterval n =>
      Nat.size input.2.1 ≤ B) historyInputCode queryHistoryEqualWithWork
    (queryEncodedLEWithWork queryHistoryCodeWithWork) queryHistoryEqualWithWork_value
    (fun a b => by simp only [queryEncodedLEWithWork_value, queryHistoryCodeWithWork_value])
    (32 * B + 11) (2001000 * (B + 1) ^ 2)
    (fun a ha b hb => queryHistoryEqualWithWork_cost a b B hM hn ha hb)
    (fun a ha b hb => queryHistoryOrderWithWork_cost a b B hM hn ha hb) inputs ht
  apply h.trans
  gcongr
  nlinarith only [Nat.zero_le B]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryScalarDispatch
attribute [-instance] _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryRepresentativeScales
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

theorem queryEarlierRepresentatives_scale {n : ℕ} (N P F exponent : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) (q : TargetInterval n) (br : ℕ × TargetInterval n)
    (hb : br ∈ queryEarlierRepresentatives N P F exponent a initial q) :
    br.1 ∈ dyadicScales N := by
  simp only [queryEarlierRepresentatives, List.mem_append] at hb
  rcases hb with (hlocal | hcell) | honline
  · exact (representativeList_conditions a initial
      (localRefinementRepresentatives_subset N P F a initial q br hlocal)).1
  · obtain ⟨key, hkey, hbr⟩ := List.mem_flatMap.mp hcell
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hbr
    exact localGroupQueryKeys_scale hkey
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp honline
    exact (List.mem_filter.mp hb).1

theorem BinaryFraction.queryEarlierRepresentativesWithWork_scale {n : ℕ}
    (N P F exponent : ℕ) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction × ℕ) (q : TargetInterval n)
    (R : ℕ) (hR : ∀ r, (initial r).2 ≤ R) (br : ℕ × TargetInterval n)
    (hb : br ∈ (queryEarlierRepresentativesWithWork N P F exponent hP a initial q).1) :
    br.1 ∈ dyadicScales N := by
  rw [queryEarlierRepresentativesWithWork_value N P F exponent hP a initial q R hR] at hb
  exact queryEarlierRepresentatives_scale N P F exponent a.value (fun r => (initial r).1.value) q br hb

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryHistoryInputCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
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

theorem queryRawHistoryInputsWithWork_dyadic_bounds {nx ny : ℕ}
    (M N P history count B : ℕ) (parent : TargetInterval nx) (hP : 0 < P)
    (representatives : List (ℕ × TargetInterval ny)) (hl : representatives.length ≤ count)
    (hs : ∀ br ∈ representatives, br.1 ∈ dyadicScales N)
    (hN : Nat.size N ≤ B) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (hM : Nat.size M ≤ B) (hPb : Nat.size P ≤ B) :
    (queryRawHistoryInputsWithWork M parent P history representatives).1.length ≤
      queryHistoryInputsLength M P history count ∧
    (queryRawHistoryInputsWithWork M parent P history representatives).2 ≤
      queryRawHistoryInputsBitBudget M P history count B := by
  have hb := queryRawHistoryInputsWithWork_bounds M parent P history representatives
    ((40 * P + 2) ^ 2) (wideChildGridBitBudget P (B + 1))
    (fun br _ i => by rw [wideChildGridWithWork_value _ _ _ _ _ hP]; exact wideChildStateList_length_le parent br.2 hP i)
    (fun br hbr i => wideChildGridWithWork_cost parent br.2 br.1 P (B + 1) i hP
      (by omega) (by omega) (by omega)
      ((dyadicScales_size_bound N br.1 (hs br hbr)).trans (by omega)) (by omega))
  constructor
  · exact hb.1.trans (Nat.mul_le_mul_right _ hl)
  · apply hb.2.trans
    unfold queryRawHistoryInputsBitBudget
    dsimp only
    gcongr

theorem queryOrderedHistoryInputsWithWork_length {M n : ℕ}
    (inputs : List (Fin M × ℕ × TargetInterval n)) :
    (queryOrderedHistoryInputsWithWork inputs).1.length ≤ inputs.length := by
  rw [queryOrderedHistoryInputsWithWork_value, orderedInputs_length]
  exact List.toFinset_card_le _

theorem queryEarlierInputsWithWork_bounds_oai {nx ny : ℕ} (M N P F exponent history B R : ℕ)
    (parent : TargetInterval nx) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (q : TargetInterval ny)
    (hB : 8 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hPb : Nat.size P ≤ B) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (hM : Nat.size M ≤ B) (ht : Nat.size history ≤ B) (he : exponent + 1 ≤ B) (ha : a.width ≤ B)
    (hi : ∀ r, (initial r).1.width ≤ B) (hR : ∀ r, (initial r).2 ≤ R)
    (hw : 0 ≤ (initial q).1.value) (hPd : ∃ e : ℕ, P = 2 ^ e) :
    (queryEarlierInputsWithWork M parent N P F exponent history hP a initial q).1.length ≤
      queryHistoryInputsLength M P history (queryEarlierRepresentativesLength P F exponent B) ∧
    (queryEarlierInputsWithWork M parent N P F exponent history hP a initial q).2 ≤
      queryEarlierInputsBitBudget M P F exponent history B R := by
  let representatives := queryEarlierRepresentativesWithWork N P F exponent hP a initial q
  let raw := queryRawHistoryInputsWithWork M parent P history representatives.1
  let count := queryEarlierRepresentativesLength P F exponent B
  have hr := queryEarlierRepresentativesWithWork_bounds N P F exponent B R hP a initial q
    hB hN hF hFpos hPb hny he ha hi hR hw hPd
  have hraw := queryRawHistoryInputsWithWork_dyadic_bounds M N P history count B parent hP
    representatives.1 hr.1
    (fun br hb => queryEarlierRepresentativesWithWork_scale N P F exponent hP a initial q R hR br hb)
    hN hnx hny hM hPb
  have hsort := queryOrderedHistoryInputsWithWork_cost raw.1 B hM hny (fun input hin =>
    (Nat.size_le_size (queryRawHistoryInputsWithWork_time M parent P history hP
      representatives.1 input hin).le).trans ht)
  have hsort' := hsort.trans (Nat.mul_le_mul_right _
    (Nat.pow_le_pow_left (Nat.add_le_add_right hraw.1 1) 2))
  constructor
  · simpa only [queryEarlierInputsWithWork] using
      (queryOrderedHistoryInputsWithWork_length raw.1).trans hraw.1
  · simpa only [queryEarlierInputsWithWork, queryEarlierInputsBitBudget] using
      Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hr.2 hraw.2) hsort') 2

end EditApproximation.BinaryFraction

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.BinaryFraction.queryEarlierInputsWithWork_bounds_oai := @OAI.EditApproximation.BinaryFraction.queryEarlierInputsWithWork_bounds_oai
