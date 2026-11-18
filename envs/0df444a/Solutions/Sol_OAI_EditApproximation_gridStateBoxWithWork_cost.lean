-- Prove2me | solution 1 for OAI.EditApproximation.gridStateBoxWithWork_cost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:23:24.480209+00:00
-- url     : https://prove2.me/submissions/c91f2d71-1ac0-43f2-8f1e-d58c96eac6be

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
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

theorem gridStateBoxWithWork_cost_oai (n g radius lo hi B : ℕ) (hg : 0 < g)
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

theorem solution : type_of% @OAI.EditApproximation.gridStateBoxWithWork_cost_oai := @OAI.EditApproximation.gridStateBoxWithWork_cost_oai
