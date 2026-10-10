-- Prove2me | solution 1 for IntMul.BinarySchoolbook.product_word_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T20:04:04.216983+00:00
-- url     : https://prove2.me/submissions/6ca2e770-2a4d-43ac-86d2-6e2295116a02

import Definitions.Def_IntMul_BinarySchoolbook
import Definitions.Def_IntMul_MultitapeModel
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic


namespace IntMul.BinaryAdder

private theorem full_adder_value (a b c : Bool) :
    (sumBit a b c).toNat + 2 * (carryBit a b c).toNat = a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

private theorem add_little_length (x y : List Bool) (c : Bool) (h : x.length = y.length) :
    (addLittle x y c).length = x.length + 1 := by
  induction x generalizing y c with
  | nil =>
      cases y with
      | nil => rfl
      | cons b ys => simp at h
  | cons a xs ih =>
      cases y with
      | nil => simp at h
      | cons b ys =>
          have ht : xs.length = ys.length := by simpa using h
          simp only [addLittle, List.length_cons, ih ys _ ht]

private theorem add_little_value (x y : List Bool) (c : Bool) (h : x.length = y.length) :
    littleVal (addLittle x y c) = littleVal x + littleVal y + c.toNat := by
  induction x generalizing y c with
  | nil =>
      cases y with
      | nil => simp [addLittle, littleVal]
      | cons b ys => simp at h
  | cons a xs ih =>
      cases y with
      | nil => simp at h
      | cons b ys =>
          have ht : xs.length = ys.length := by simpa using h
          simp only [addLittle, littleVal, ih ys _ ht]
          have hv := full_adder_value a b c
          omega

private theorem little_value_bound (x : List Bool) : littleVal x < 2 ^ x.length := by
  induction x with
  | nil => simp [littleVal]
  | cons b xs ih =>
      cases b <;> simp only [littleVal, List.length_cons, pow_succ,
        Bool.toNat_false, Bool.toNat_true] <;> omega

private theorem foldl_affine (x : List Bool) (a : ℕ) :
    x.foldl (fun acc b => 2 * acc + b.toNat) a = 2 ^ x.length * a + IntMul.val x := by
  induction x generalizing a with
  | nil => simp [IntMul.val]
  | cons b xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      have hv : IntMul.val (b :: xs) = 2 ^ xs.length * b.toNat + IntMul.val xs := by
        simp only [IntMul.val, List.foldl_cons, Nat.mul_zero, Nat.zero_add]
        exact ih b.toNat
      rw [hv, pow_succ]
      ring

private theorem val_append (x y : List Bool) :
    IntMul.val (x ++ y) = 2 ^ y.length * IntMul.val x + IntMul.val y := by
  unfold IntMul.val
  rw [List.foldl_append]
  exact foldl_affine y _

private theorem val_singleton (b : Bool) : IntMul.val [b] = b.toNat := by
  simp [IntMul.val]

private theorem val_reverse_little (x : List Bool) : IntMul.val x.reverse = littleVal x := by
  induction x with
  | nil => simp [IntMul.val, littleVal]
  | cons b xs ih =>
      rw [List.reverse_cons, val_append, val_singleton]
      simp only [List.length_singleton, pow_one, ih, littleVal]
      ring

/-- Ripple-carry addition computes the ordinary campaign-model value, preserving
all leading zeroes and adding exactly one final carry position. -/
private theorem ripple_sum_spec (x y : List Bool) (h : x.length = y.length) :
    ((addLittle x.reverse y.reverse false).reverse).length = x.length + 1 ∧
    IntMul.val ((addLittle x.reverse y.reverse false).reverse) = IntMul.val x + IntMul.val y := by
  have hl : x.reverse.length = y.reverse.length := by simpa using h
  constructor
  · simpa using add_little_length x.reverse y.reverse false hl
  · rw [val_reverse_little, add_little_value _ _ _ hl]
    have hx : littleVal x.reverse = IntMul.val x := by
      rw [← val_reverse_little, List.reverse_reverse]
    have hy : littleVal y.reverse = IntMul.val y := by
      rw [← val_reverse_little, List.reverse_reverse]
    simp [hx, hy]

/-- Every little-endian word has exactly its specified binary digits, including
trailing zeroes; no normalization assumption is needed. -/
private theorem little_value_test_bit (x : List Bool) (i : ℕ) :
    (littleVal x).testBit i = x.getD i false := by
  induction x generalizing i with
  | nil => simp [littleVal]
  | cons b xs ih =>
      have hv : littleVal (b :: xs) = Nat.bit b (littleVal xs) := by
        cases b <;> simp [littleVal, Nat.bit] <;> omega
      rw [hv]
      cases i with
      | zero => cases b <;> simp [Nat.bit, Nat.testBit_zero]
      | succ i => rw [Nat.testBit_bit_succ]; simpa using ih i

/-- The campaign's padded big-endian binary encoding returns every original
word, preserving its declared width and any leading zeroes. -/
private theorem bin_value_roundtrip (x : List Bool) : IntMul.bin x.length (IntMul.val x) = x := by
  have hv : IntMul.val x = littleVal x.reverse := by
    rw [← val_reverse_little, List.reverse_reverse]
  apply List.ext_getElem (by simp [IntMul.bin])
  intro i hi hx
  simp only [IntMul.bin, List.getElem_ofFn]
  rw [hv, little_value_test_bit]
  have hj : x.length - 1 - i < x.reverse.length := by simp only [List.length_reverse]; omega
  rw [List.getD_eq_getElem _ _ hj, List.getElem_reverse hj]
  have he : x.length - 1 - (x.length - 1 - i) = i := by omega
  simp only [he]

/-- The ripple adder produces exactly the canonical output word demanded by the
linear-time addition milestone, rather than merely a word of the same value. -/
private theorem ripple_sum_bin (x y : List Bool) (h : x.length = y.length) :
    (addLittle x.reverse y.reverse false).reverse =
      IntMul.bin (x.length + 1) (IntMul.val x + IntMul.val y) := by
  have hs := ripple_sum_spec x y h
  have hr := bin_value_roundtrip ((addLittle x.reverse y.reverse false).reverse)
  rw [hs.1, hs.2] at hr
  exact hr.symm

end IntMul.BinaryAdder




namespace IntMul.BinarySchoolbook

open BinaryAdder (littleVal)

private theorem shift_length (previous : Bool) (p : List Bool) :
    (shiftCarry previous p).length = p.length := by
  induction p generalizing previous with
  | nil => rfl
  | cons b bs ih => simp [shiftCarry,ih]

private theorem shift_value_carry (previous : Bool) (p : List Bool) :
    littleVal (shiftCarry previous p) + 2 ^ p.length * (highCarry previous p).toNat =
      2 * littleVal p + previous.toNat := by
  induction p generalizing previous with
  | nil => simp [shiftCarry,highCarry,littleVal]
  | cons b bs ih =>
      simp only [shiftCarry,highCarry,littleVal,List.length_cons,pow_succ]
      have hv := ih b
      nlinarith

private theorem shift_value (previous : Bool) (p : List Bool) :
    littleVal (shiftCarry previous p) = (2 * littleVal p + previous.toNat) % 2 ^ p.length := by
  have hv := shift_value_carry previous p
  have hl : littleVal (shiftCarry previous p) < 2 ^ p.length := by
    simpa only [shift_length] using BinaryAdder.little_value_bound (shiftCarry previous p)
  calc
    littleVal (shiftCarry previous p) = littleVal (shiftCarry previous p) % 2 ^ p.length := (Nat.mod_eq_of_lt hl).symm
    _ = (littleVal (shiftCarry previous p) + 2 ^ p.length * (highCarry previous p).toNat) % 2 ^ p.length := by
      rw [Nat.add_mul_mod_self_left]
    _ = (2 * littleVal p + previous.toNat) % 2 ^ p.length := by rw [hv]

private theorem add_fixed_length (x y : List Bool) (c : Bool) (h : x.length = y.length) :
    (addFixed x y c).length = x.length := by
  induction x generalizing y c with
  | nil => simp [addFixed]
  | cons a xs ih =>
      cases y with
      | nil => simp at h
      | cons b ys =>
          have ht : xs.length = ys.length := by simpa using h
          simp [addFixed,ih ys _ ht]

private theorem add_fixed_value_carry (x y : List Bool) (c : Bool) (h : x.length = y.length) :
    littleVal (addFixed x y c) + 2 ^ x.length * (lastCarry x y c).toNat =
      littleVal x + littleVal y + c.toNat := by
  induction x generalizing y c with
  | nil =>
      cases y with
      | nil => simp [addFixed,lastCarry,littleVal]
      | cons b ys => simp at h
  | cons a xs ih =>
      cases y with
      | nil => simp at h
      | cons b ys =>
          have ht : xs.length = ys.length := by simpa using h
          simp only [addFixed,lastCarry,littleVal,List.length_cons,pow_succ]
          have hv := ih ys (BinaryAdder.carryBit a b c) ht
          have hb := BinaryAdder.full_adder_value a b c
          nlinarith

private theorem add_fixed_value (x y : List Bool) (c : Bool) (h : x.length = y.length) :
    littleVal (addFixed x y c) = (littleVal x + littleVal y + c.toNat) % 2 ^ x.length := by
  have hv := add_fixed_value_carry x y c h
  have hl : littleVal (addFixed x y c) < 2 ^ x.length := by
    simpa only [add_fixed_length x y c h] using BinaryAdder.little_value_bound (addFixed x y c)
  calc
    littleVal (addFixed x y c) = littleVal (addFixed x y c) % 2 ^ x.length := (Nat.mod_eq_of_lt hl).symm
    _ = (littleVal (addFixed x y c) + 2 ^ x.length * (lastCarry x y c).toNat) % 2 ^ x.length := by
      rw [Nat.add_mul_mod_self_left]
    _ = (littleVal x + littleVal y + c.toNat) % 2 ^ x.length := by rw [hv]

private theorem advance_length (x p : List Bool) (b : Bool) (h : x.length = p.length) :
    (advanceWord x p b).length = x.length := by
  cases b
  · simp [advanceWord,shift_length,h]
  · simp only [advanceWord,↓reduceIte]
    rw [add_fixed_length _ _ _ (by simpa [shift_length] using h.symm),shift_length,h]

private theorem advance_value (x p : List Bool) (b : Bool) (h : x.length = p.length) :
    littleVal (advanceWord x p b) = (2 * littleVal p + b.toNat * littleVal x) % 2 ^ x.length := by
  cases b
  · simp [advanceWord,shift_value,h]
  · simp only [advanceWord,↓reduceIte]
    rw [add_fixed_value _ _ _ (by simpa [shift_length] using h.symm),shift_length,
      shift_value,Bool.toNat_false,Nat.add_zero,h,Bool.toNat_true,Nat.one_mul]
    simp only [Nat.add_mod,Nat.mod_mod,Nat.zero_mod,Nat.add_zero]

private theorem fold_length (x y p : List Bool) (h : x.length = p.length) :
    (foldWord x y p).length = x.length := by
  induction y generalizing p with
  | nil => simpa [foldWord] using h.symm
  | cons b bs ih =>
      change (foldWord x bs (advanceWord x p b)).length = _
      exact ih _ (advance_length x p b h).symm

private theorem schoolbook_val_cons (b : Bool) (bs : List Bool) :
    IntMul.val (b :: bs) = 2 ^ bs.length * b.toNat + IntMul.val bs := by
  simpa [BinaryAdder.val_singleton] using BinaryAdder.val_append [b] bs

/-- The accumulator implements Horner's formula modulo its fixed capacity. -/
private theorem fold_value (x y p : List Bool) (h : x.length = p.length) :
    littleVal (foldWord x y p) =
      (2 ^ y.length * littleVal p + littleVal x * IntMul.val y) % 2 ^ x.length := by
  induction y generalizing p with
  | nil =>
      simp only [foldWord,List.foldl_nil,List.length_nil,pow_zero,Nat.one_mul,IntMul.val,List.foldl_nil,
        Nat.mul_zero,Nat.add_zero]
      exact (Nat.mod_eq_of_lt (by simpa [h] using BinaryAdder.little_value_bound p)).symm
  | cons b bs ih =>
      change littleVal (foldWord x bs (advanceWord x p b)) = _
      rw [ih _ (advance_length x p b h).symm,advance_value x p b h]
      have hm : (2 ^ bs.length * ((2 * littleVal p + b.toNat * littleVal x) % 2 ^ x.length) +
          littleVal x * IntMul.val bs) % 2 ^ x.length =
          (2 ^ bs.length * (2 * littleVal p + b.toNat * littleVal x) +
            littleVal x * IntMul.val bs) % 2 ^ x.length := by
        simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_mod]
      rw [hm,schoolbook_val_cons]
      simp only [List.length_cons,pow_succ]
      congr 1
      ring

private theorem little_replicate_false (n : ℕ) : littleVal (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,littleVal,ih]

private theorem val_bound (x : List Bool) : IntMul.val x < 2 ^ x.length := by
  have h := BinaryAdder.little_value_bound x.reverse
  rw [← BinaryAdder.val_reverse_little,List.reverse_reverse,List.length_reverse] at h
  exact h

private theorem padded_value (x : List Bool) :
    littleVal ((List.replicate x.length false ++ x).reverse) = IntMul.val x := by
  rw [← BinaryAdder.val_reverse_little,List.reverse_reverse,BinaryAdder.val_append]
  have hz : IntMul.val (List.replicate x.length false) = 0 := by
    rw [← List.reverse_replicate, BinaryAdder.val_reverse_little,little_replicate_false]
  rw [hz,Nat.mul_zero,Nat.zero_add]

private theorem product_word_length (x y : List Bool) : (productWord x y).length = 2 * x.length := by
  unfold productWord
  rw [List.length_reverse,fold_length _ _ _ (by simp;omega)]
  simp
  omega

/-- The pure word algorithm computes exactly the required padded product;
overflow is excluded at the final value for equal-width operands. -/
theorem product_word_correct (x y : List Bool) (h : x.length = y.length) :
    productWord x y = IntMul.bin (2 * x.length) (IntMul.val x * IntMul.val y) := by
  have hlen : ((List.replicate x.length false ++ x).reverse).length = 2 * x.length := by simp;omega
  have hw : ((List.replicate x.length false ++ x).reverse).length =
      (List.replicate (2 * x.length) false).length := by simp;omega
  have hv : IntMul.val (productWord x y) = IntMul.val x * IntMul.val y := by
    unfold productWord
    rw [BinaryAdder.val_reverse_little,fold_value _ _ _ hw,hlen,little_replicate_false,
      Nat.mul_zero,Nat.zero_add,padded_value]
    apply Nat.mod_eq_of_lt
    have hx := val_bound x
    have hy := val_bound y
    rw [← h] at hy
    have hp : 0 < 2 ^ x.length := by positivity
    have hm : IntMul.val x * IntMul.val y < 2 ^ x.length * 2 ^ x.length := by nlinarith
    rw [← pow_add,show x.length + x.length = 2 * x.length by omega] at hm
    exact hm
  have hb := BinaryAdder.bin_value_roundtrip (productWord x y)
  rw [product_word_length,hv] at hb
  exact hb.symm

end IntMul.BinarySchoolbook


open IntMul.BinarySchoolbook

theorem solution (x y : List Bool) (h : x.length = y.length) :
    productWord x y = IntMul.bin (2 * x.length) (IntMul.val x * IntMul.val y) :=
  IntMul.BinarySchoolbook.product_word_correct x y h

#print axioms solution
