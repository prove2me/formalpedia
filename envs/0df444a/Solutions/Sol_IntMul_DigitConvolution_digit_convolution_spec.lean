-- Prove2me | solution 1 for IntMul.DigitConvolution.digit_convolution_spec
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T08:48:50.85426+00:00
-- url     : https://prove2.me/submissions/2d8fd4e3-6b03-42d6-816f-70fe578f31ab

import Definitions.Def_IntMul_DigitConvolution
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic

namespace IntMul.BinaryAdder

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


end IntMul.BinaryAdder


namespace IntMul.DigitConvolution

open BinaryAdder (littleVal)

private theorem little_append (x y : List Bool) :
    littleVal (x++y)=littleVal x+2^x.length*littleVal y := by
  rw [←BinaryAdder.val_reverse_little,List.reverse_append,BinaryAdder.val_append]
  simp only [List.length_reverse,BinaryAdder.val_reverse_little]
  ring

private theorem chunk_step (xs : List Bool) (B j : ℕ) :
    littleVal (xs.take ((j+1)*B))=
      littleVal (xs.take (j*B))+2^(j*B)*littleVal ((xs.drop (j*B)).take B) := by
  rw [Nat.add_mul,Nat.one_mul,List.take_add,little_append]
  by_cases hj : j*B ≤ xs.length
  · simp [List.length_take,Nat.min_eq_left hj]
  · have hn : xs.drop (j*B)=[] := List.drop_eq_nil_iff.mpr (by omega)
    simp [hn,littleVal]

private theorem chunk_value (B : ℕ) (x : List Bool) (j : ℕ) :
    digit B x j=littleVal ((x.reverse.drop (j*B)).take B) := by
  exact BinaryAdder.val_reverse_little _

private theorem prefix_value (B : ℕ) (x : List Bool) (k : ℕ) :
    ∑ j ∈ Finset.range k, digit B x j*2^(j*B)=littleVal (x.reverse.take (k*B)) := by
  induction k with
  | zero => simp [littleVal]
  | succ k ih =>
    rw [Finset.sum_range_succ,ih,chunk_value,chunk_step]
    ring

private theorem count_covers (B : ℕ) (x : List Bool) (hB : 0 < B) :
    x.length ≤ blockCount B x*B := by
  have hm := Nat.mod_lt (x.length+B-1) hB
  have he := Nat.div_add_mod (x.length+B-1) B
  rw [Nat.mul_comm] at he
  unfold blockCount
  omega

private theorem digit_bound (B : ℕ) (x : List Bool) (j : ℕ) : digit B x j < 2^B := by
  rw [chunk_value]
  apply lt_of_lt_of_le (BinaryAdder.little_value_bound _)
  apply Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ))
  simp only [List.length_take]
  exact Nat.min_le_left _ _

private theorem digit_zero (B : ℕ) (x : List Bool) (j : ℕ) (hB : 0 < B)
    (hj : blockCount B x ≤ j) : digit B x j=0 := by
  have hc := count_covers B x hB
  have hm := Nat.mul_le_mul_right B hj
  rw [chunk_value,List.drop_eq_nil_iff.mpr (by simpa using le_trans hc hm)]
  simp [littleVal]

private theorem coefficient (B : ℕ) (x : List Bool) (j : ℕ) (hB : 0 < B) :
    (polynomial B x).coeff j=digit B x j := by
  unfold polynomial
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]
  by_cases hj : j < blockCount B x
  · simp [Finset.mem_range,hj]
  · rw [digit_zero B x j hB (by omega)]
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg (by have := Finset.mem_range.mp hi; omega)]

private theorem evaluate (B : ℕ) (x : List Bool) (hB : 0 < B) :
    (polynomial B x).eval (2^B)=val x := by
  unfold polynomial
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial,←pow_mul]
  simp_rw [Nat.mul_comm B]
  rw [prefix_value,List.take_of_length_le (by simpa using count_covers B x hB)]
  rw [←BinaryAdder.val_reverse_little,List.reverse_reverse]

private theorem product_coefficient (B : ℕ) (x y : List Bool) (k : ℕ) (hB : 0 < B) :
    (polynomial B x*polynomial B y).coeff k=
      ∑ i ∈ Finset.range (blockCount B x),
        if i ≤ k then digit B x i*digit B y (k-i) else 0 := by
  rw [polynomial,Finset.sum_mul,Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  rw [←Polynomial.C_mul_X_pow_eq_monomial,mul_assoc,Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_mul']
  rw [coefficient B y (k-i) hB]
  by_cases h : i ≤ k
  · simp [h]
  · simp [h]

private theorem product_bound_left (B : ℕ) (x y : List Bool) (k : ℕ) (hB : 0 < B) :
    (polynomial B x*polynomial B y).coeff k ≤ blockCount B x*(2^B-1)^2 := by
  rw [product_coefficient B x y k hB]
  calc
    _ ≤ ∑ _i ∈ Finset.range (blockCount B x), (2^B-1)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases h : i ≤ k
      · rw [if_pos h,pow_two]
        have hx := digit_bound B x i
        have hy := digit_bound B y (k-i)
        exact Nat.mul_le_mul (by omega) (by omega)
      · rw [if_neg h]
        exact Nat.zero_le _
    _ = _ := by simp

private theorem product_bound (B : ℕ) (x y : List Bool) (k : ℕ) (hB : 0 < B) :
    (polynomial B x*polynomial B y).coeff k ≤
      min (blockCount B x) (blockCount B y)*(2^B-1)^2 := by
  by_cases h : blockCount B x ≤ blockCount B y
  · rw [Nat.min_eq_left h]
    exact product_bound_left B x y k hB
  · rw [Nat.min_eq_right (by omega),mul_comm (polynomial B x)]
    exact product_bound_left B y x k hB

/-- Exact base-2^B digit encoding and convolution, including short, empty,
leading-zero and over-width blocks. Coefficient growth is explicit. -/
private theorem digit_convolution_spec (B : ℕ) (hB : 0 < B) (x y : List Bool) :
    (polynomial B x).eval (2^B)=val x ∧
    (polynomial B y).eval (2^B)=val y ∧
    (polynomial B x*polynomial B y).eval (2^B)=val x*val y ∧
    (∀ j, (polynomial B x).coeff j=digit B x j ∧ digit B x j < 2^B) ∧
    (∀ j, (polynomial B y).coeff j=digit B y j ∧ digit B y j < 2^B) ∧
    (∀ k,
      (polynomial B x*polynomial B y).coeff k=
        ∑ i ∈ Finset.range (blockCount B x),
          if i ≤ k then digit B x i*digit B y (k-i) else 0) ∧
    (∀ k, (polynomial B x*polynomial B y).coeff k ≤
      min (blockCount B x) (blockCount B y)*(2^B-1)^2) := by
  refine ⟨evaluate B x hB,evaluate B y hB,?_,?_,?_,?_,?_⟩
  · rw [Polynomial.eval_mul,evaluate B x hB,evaluate B y hB]
  · intro j
    exact ⟨coefficient B x j hB,digit_bound B x j⟩
  · intro j
    exact ⟨coefficient B y j hB,digit_bound B y j⟩
  · intro k
    exact product_coefficient B x y k hB
  · intro k
    exact product_bound B x y k hB

end IntMul.DigitConvolution


open IntMul IntMul.DigitConvolution

theorem solution (B : ℕ) (hB : 0 < B) (x y : List Bool) :
    (polynomial B x).eval (2^B)=val x ∧
    (polynomial B y).eval (2^B)=val y ∧
    (polynomial B x*polynomial B y).eval (2^B)=val x*val y ∧
    (∀ j, (polynomial B x).coeff j=digit B x j ∧ digit B x j < 2^B) ∧
    (∀ j, (polynomial B y).coeff j=digit B y j ∧ digit B y j < 2^B) ∧
    (∀ k,
      (polynomial B x*polynomial B y).coeff k=
        ∑ i ∈ Finset.range (blockCount B x),
          if i ≤ k then digit B x i*digit B y (k-i) else 0) ∧
    (∀ k, (polynomial B x*polynomial B y).coeff k ≤
      min (blockCount B x) (blockCount B y)*(2^B-1)^2) :=
  IntMul.DigitConvolution.digit_convolution_spec B hB x y

#print axioms solution
