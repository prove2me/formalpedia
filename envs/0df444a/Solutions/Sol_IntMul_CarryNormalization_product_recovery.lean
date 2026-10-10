-- Prove2me | solution 1 for IntMul.CarryNormalization.product_recovery
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T09:06:05.652326+00:00
-- url     : https://prove2.me/submissions/6cb39a4e-674c-43e4-a577-75a6335b843c

import Definitions.Def_IntMul_CarryNormalization
import Theorems.Thm_IntMul_DigitConvolution_digit_convolution_spec
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


end IntMul.BinaryAdder


namespace IntMul.CarryNormalization

private theorem scan_length (base : ℕ) (as : List ℕ) (c : ℕ) :
    (scan base as c).1.length=as.length := by
  induction as generalizing c with
  | nil => rfl
  | cons a as ih => simp [scan,ih]

private theorem scan_digits (base : ℕ) (as : List ℕ) (c : ℕ) (hb : 0 < base) :
    ∀ d ∈ (scan base as c).1, d < base := by
  induction as generalizing c with
  | nil => simp [scan]
  | cons a as ih =>
    simp only [scan,List.mem_cons]
    intro d hd
    rcases hd with rfl|hd
    · exact Nat.mod_lt _ hb
    · exact ih _ d hd

private theorem scan_value (base : ℕ) (as : List ℕ) (c : ℕ) :
    Nat.ofDigits base (scan base as c).1+base^as.length*(scan base as c).2=
      Nat.ofDigits base as+c := by
  induction as generalizing c with
  | nil => simp [scan]
  | cons a as ih =>
    simp only [scan,Nat.ofDigits_cons,List.length_cons,pow_succ]
    have h := ih ((a+c)/base)
    have hm := Nat.mod_add_div (a+c) base
    nlinarith

private theorem scan_final_zero (base : ℕ) (as : List ℕ) (c : ℕ) (hb : 0 < base)
    (h : Nat.ofDigits base as+c < base^as.length) : (scan base as c).2=0 := by
  have hv := scan_value base as c
  have hp : 0 < base^as.length := by positivity
  by_contra hn
  have hc : 1 ≤ (scan base as c).2 := by omega
  have hm := Nat.mul_le_mul_left (base^as.length) hc
  rw [Nat.mul_one] at hm
  omega

private theorem carry_step_bound (base m a c : ℕ) (hb : 0 < base)
    (ha : a ≤ m*(base-1)^2) (hc : c ≤ m*(base-1)) :
    (a+c)/base ≤ m*(base-1) := by
  have hp : base-1+1=base := by omega
  have he : m*(base-1)^2+m*(base-1)=m*(base-1)*base := by
    calc
      _ = m*(base-1)*((base-1)+1) := by ring
      _ = _ := by rw [hp]
  have hsum : a+c ≤ m*(base-1)*base := by omega
  calc
    _ ≤ (m*(base-1)*base)/base := Nat.div_le_div_right hsum
    _ = _ := Nat.mul_div_cancel _ hb

private theorem scan_carry_bound (base m : ℕ) (as : List ℕ) (c : ℕ) (hb : 0 < base)
    (ha : ∀ a ∈ as, a ≤ m*(base-1)^2) (hc : c ≤ m*(base-1)) :
    (scan base as c).2 ≤ m*(base-1) := by
  induction as generalizing c with
  | nil => exact hc
  | cons a as ih =>
    change (scan base as ((a+c)/base)).2 ≤ _
    exact ih _ (fun b h => ha b (List.mem_cons_of_mem _ h))
      (carry_step_bound base m a c hb (ha a (List.mem_cons_self)) hc)

private theorem carry_prefix_bound (base m : ℕ) (as : List ℕ) (c j : ℕ) (hb : 0 < base)
    (ha : ∀ a ∈ as, a ≤ m*(base-1)^2) (hc : c ≤ m*(base-1)) :
    carryAt base as c j ≤ m*(base-1) := by
  exact scan_carry_bound base m (as.take j) c hb
    (fun a h => ha a (List.mem_of_mem_take h)) hc

private theorem count_covers (B : ℕ) (x : List Bool) (hB : 0 < B) :
    x.length ≤ DigitConvolution.blockCount B x*B := by
  have hm := Nat.mod_lt (x.length+B-1) hB
  have he := Nat.div_add_mod (x.length+B-1) B
  rw [Nat.mul_comm] at he
  unfold DigitConvolution.blockCount
  omega

private theorem digit_zero (B : ℕ) (x : List Bool) (j : ℕ) (hB : 0 < B)
    (hj : DigitConvolution.blockCount B x ≤ j) : DigitConvolution.digit B x j=0 := by
  have hc := count_covers B x hB
  have hm := Nat.mul_le_mul_right B hj
  unfold DigitConvolution.digit DigitConvolution.chunk
  rw [List.drop_eq_nil_iff.mpr (by simpa using le_trans hc hm)]
  simp [val]

private theorem product_coefficient_zero (B : ℕ) (x y : List Bool) (k : ℕ) (hB : 0 < B)
    (hk : DigitConvolution.blockCount B x+DigitConvolution.blockCount B y ≤ k) :
    (DigitConvolution.polynomial B x*DigitConvolution.polynomial B y).coeff k=0 := by
  rcases DigitConvolution.digit_convolution_spec B hB x y with ⟨_,_,_,_,_,hconv,_⟩
  rw [hconv k]
  apply Finset.sum_eq_zero
  intro i hi
  have hi' := Finset.mem_range.mp hi
  by_cases h : i ≤ k
  · rw [if_pos h,digit_zero B y (k-i) hB (by omega),Nat.mul_zero]
  · rw [if_neg h]

private theorem ofDigits_range (base k : ℕ) (f : ℕ → ℕ) :
    Nat.ofDigits base ((List.range k).map f)=∑ j ∈ Finset.range k, f j*base^j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ,List.map_append,Nat.ofDigits_append,ih,Finset.sum_range_succ]
    simp [Nat.mul_comm]

private theorem coefficients_value (B : ℕ) (x y : List Bool) (hB : 0 < B) :
    Nat.ofDigits (2^B) (coefficients B x y)=val x*val y := by
  rcases DigitConvolution.digit_convolution_spec B hB x y with ⟨_,_,hprod,_,_,_,_⟩
  unfold coefficients
  rw [ofDigits_range]
  by_cases hp : DigitConvolution.polynomial B x*DigitConvolution.polynomial B y=0
  · rw [hp] at hprod ⊢
    simpa using hprod
  · have hd := (Polynomial.degree_lt_iff_coeff_zero
      (DigitConvolution.polynomial B x*DigitConvolution.polynomial B y)
      (DigitConvolution.blockCount B x+DigitConvolution.blockCount B y)).mpr
      (fun k hk => product_coefficient_zero B x y k hB hk)
    have hn := (Polynomial.natDegree_lt_iff_degree_lt hp).mpr hd
    rw [←Polynomial.eval_eq_sum_range' hn (2^B)]
    exact hprod

private theorem coefficients_length (B : ℕ) (x y : List Bool) :
    (coefficients B x y).length=DigitConvolution.blockCount B x+DigitConvolution.blockCount B y := by
  simp [coefficients]

private theorem coefficients_bound (B : ℕ) (x y : List Bool) (hB : 0 < B) :
    ∀ a ∈ coefficients B x y,
      a ≤ min (DigitConvolution.blockCount B x) (DigitConvolution.blockCount B y)*(2^B-1)^2 := by
  rcases DigitConvolution.digit_convolution_spec B hB x y with ⟨_,_,_,_,_,_,hb⟩
  intro a ha
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
  exact hb i

private theorem word_value_bound (x : List Bool) : val x < 2^x.length := by
  have h := BinaryAdder.little_value_bound x.reverse
  rw [←BinaryAdder.val_reverse_little,List.reverse_reverse,List.length_reverse] at h
  exact h

private theorem product_value_bound (B : ℕ) (x y : List Bool) (hB : 0 < B) :
    val x*val y < (2^B)^(coefficients B x y).length := by
  have hx := word_value_bound x
  have hy := word_value_bound y
  have hc := count_covers B x hB
  have hd := count_covers B y hB
  calc
    _ ≤ val x*2^y.length := Nat.mul_le_mul_left _ hy.le
    _ < 2^x.length*2^y.length := Nat.mul_lt_mul_of_pos_right hx (by positivity)
    _ = 2^(x.length+y.length) := (pow_add _ _ _).symm
    _ ≤ 2^(B*(DigitConvolution.blockCount B x+DigitConvolution.blockCount B y)) := by
      apply Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ))
      rw [Nat.mul_add,Nat.mul_comm B (DigitConvolution.blockCount B x),
        Nat.mul_comm B (DigitConvolution.blockCount B y)]
      omega
    _ = _ := by rw [pow_mul,coefficients_length]

private theorem product_final_zero (B : ℕ) (x y : List Bool) (hB : 0 < B) :
    (scan (2^B) (coefficients B x y) 0).2=0 := by
  apply scan_final_zero (2^B) (coefficients B x y) 0 (by positivity)
  rw [coefficients_value B x y hB,Nat.add_zero]
  exact product_value_bound B x y hB

private theorem product_digits_value (B : ℕ) (x y : List Bool) (hB : 0 < B) :
    Nat.ofDigits (2^B) (scan (2^B) (coefficients B x y) 0).1=val x*val y := by
  have hv := scan_value (2^B) (coefficients B x y) 0
  rw [product_final_zero B x y hB,Nat.mul_zero,Nat.add_zero,coefficients_value B x y hB,
    Nat.add_zero] at hv
  exact hv

private theorem bin_reverse (B d : ℕ) :
    (bin B d).reverse=List.ofFn (fun i : Fin B => d.testBit i) := by
  apply List.ext_getElem (by simp [bin])
  intro i hi hi'
  simp only [bin,List.getElem_reverse,List.getElem_ofFn]
  congr 1
  simp only [List.length_ofFn] at *
  omega

private theorem bin_value (B d : ℕ) : val (bin B d)=d%2^B := by
  have hv : val (bin B d)=BinaryAdder.littleVal (bin B d).reverse := by
    rw [←BinaryAdder.val_reverse_little,List.reverse_reverse]
  rw [hv,bin_reverse]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [BinaryAdder.little_value_test_bit,Nat.testBit_mod_two_pow]
  by_cases hj : j < B
  · rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_ofFn]
    simp [hj]
  · rw [List.getD_eq_default _ _ (by simp;omega)]
    simp [hj]

private theorem bits_length (B : ℕ) (ds : List ℕ) : (bits B ds).length=B*ds.length := by
  unfold bits
  rw [List.length_reverse]
  induction ds with
  | nil => simp
  | cons d ds ih => simp [List.flatMap_cons,bin,ih]; ring

private theorem little_append (x y : List Bool) :
    BinaryAdder.littleVal (x++y)=BinaryAdder.littleVal x+2^x.length*BinaryAdder.littleVal y := by
  rw [←BinaryAdder.val_reverse_little,List.reverse_append,BinaryAdder.val_append]
  simp only [List.length_reverse,BinaryAdder.val_reverse_little]
  ring

private theorem bits_value (B : ℕ) (ds : List ℕ) (hd : ∀ d ∈ ds, d < 2^B) :
    val (bits B ds)=Nat.ofDigits (2^B) ds := by
  unfold bits
  rw [BinaryAdder.val_reverse_little]
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    have hv : BinaryAdder.littleVal (bin B d).reverse=val (bin B d) := by
      rw [←BinaryAdder.val_reverse_little,List.reverse_reverse]
    rw [List.flatMap_cons,little_append,hv,
      bin_value,Nat.mod_eq_of_lt (hd d List.mem_cons_self),ih (fun a ha => hd a (List.mem_cons_of_mem _ ha))]
    simp [bin,Nat.ofDigits]

private theorem product_word_correct (B : ℕ) (x y : List Bool) (hB : 0 < B) :
    productWord B x y=bin
      (B*(DigitConvolution.blockCount B x+DigitConvolution.blockCount B y)) (val x*val y) := by
  have hl : (productWord B x y).length=
      B*(DigitConvolution.blockCount B x+DigitConvolution.blockCount B y) := by
    rw [productWord,bits_length,scan_length,coefficients_length]
  have hv : val (productWord B x y)=val x*val y := by
    rw [productWord,bits_value B _ (scan_digits _ _ _ (by positivity)),product_digits_value B x y hB]
  have hc := BinaryAdder.bin_value_roundtrip (productWord B x y)
  rw [hl,hv] at hc
  exact hc.symm

private theorem carry_width (B m c : ℕ) (hc : c ≤ m*(2^B-1)) :
    c < 2^(B+Nat.clog 2 m) := by
  by_cases hm : m=0
  · have hz : c=0 := by simp [hm] at hc; exact hc
    rw [hz]
    positivity
  · have hb : 0 < 2^B := by positivity
    have hsub : 2^B-1 < 2^B := by omega
    calc
      c ≤ m*(2^B-1) := hc
      _ < m*2^B := Nat.mul_lt_mul_of_pos_left hsub (by omega)
      _ ≤ 2^(Nat.clog 2 m)*2^B := Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide) m)
      _ = _ := by rw [←pow_add,Nat.add_comm]

private theorem sum_width (B m a c : ℕ) (ha : a ≤ m*(2^B-1)^2) (hc : c ≤ m*(2^B-1)) :
    a+c < 2^(2*B+Nat.clog 2 m) := by
  by_cases hm : m=0
  · have hz : a+c=0 := by simp [hm] at ha hc; omega
    rw [hz]
    positivity
  · have hb : 0 < 2^B := by positivity
    have hp : 2^B-1+1=2^B := by omega
    have he : m*(2^B-1)^2+m*(2^B-1)=m*(2^B-1)*2^B := by
      calc
        _ = m*(2^B-1)*((2^B-1)+1) := by ring
        _ = _ := by rw [hp]
    have hsum : a+c ≤ m*(2^B-1)*2^B := by omega
    calc
      a+c ≤ m*(2^B-1)*2^B := hsum
      _ < m*2^B*2^B := Nat.mul_lt_mul_of_pos_right
        (Nat.mul_lt_mul_of_pos_left (by omega) (by omega)) hb
      _ ≤ 2^(Nat.clog 2 m)*2^B*2^B :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide) m))
      _ = _ := by rw [←pow_add,←pow_add]; congr 1; omega

/-- Exact product recovery by a single low-to-high carry pass. Every partial
carry and every coefficient-plus-carry sum has an explicit finite bit width. -/
private theorem product_recovery (B : ℕ) (hB : 0 < B) (x y : List Bool) :
    productWord B x y=bin
      (B*(DigitConvolution.blockCount B x+DigitConvolution.blockCount B y)) (val x*val y) ∧
    (scan (2^B) (coefficients B x y) 0).2=0 ∧
    (∀ d ∈ (scan (2^B) (coefficients B x y) 0).1, d < 2^B) ∧
    (∀ j, carryAt (2^B) (coefficients B x y) 0 j ≤
      min (DigitConvolution.blockCount B x) (DigitConvolution.blockCount B y)*(2^B-1) ∧
      carryAt (2^B) (coefficients B x y) 0 j <
        2^(B+Nat.clog 2 (min (DigitConvolution.blockCount B x) (DigitConvolution.blockCount B y)))) ∧
    (∀ a ∈ coefficients B x y, ∀ j,
      a+carryAt (2^B) (coefficients B x y) 0 j <
        2^(2*B+Nat.clog 2 (min (DigitConvolution.blockCount B x) (DigitConvolution.blockCount B y)))) := by
  have hb := coefficients_bound B x y hB
  have hc := fun j => carry_prefix_bound (2^B)
    (min (DigitConvolution.blockCount B x) (DigitConvolution.blockCount B y))
    (coefficients B x y) 0 j (by positivity) hb (Nat.zero_le _)
  refine ⟨product_word_correct B x y hB,product_final_zero B x y hB,
    scan_digits _ _ _ (by positivity),?_,?_⟩
  · intro j
    exact ⟨hc j,carry_width B _ _ (hc j)⟩
  · intro a ha j
    exact sum_width B _ _ _ (hb a ha) (hc j)

end IntMul.CarryNormalization


open IntMul IntMul.CarryNormalization

theorem solution (B : ℕ) (hB : 0 < B) (x y : List Bool) :
    productWord B x y=bin
      (B*(DigitConvolution.blockCount B x+DigitConvolution.blockCount B y)) (val x*val y) ∧
    (scan (2^B) (coefficients B x y) 0).2=0 ∧
    (∀ d ∈ (scan (2^B) (coefficients B x y) 0).1, d < 2^B) ∧
    (∀ j, carryAt (2^B) (coefficients B x y) 0 j ≤
      min (DigitConvolution.blockCount B x) (DigitConvolution.blockCount B y)*(2^B-1) ∧
      carryAt (2^B) (coefficients B x y) 0 j <
        2^(B+Nat.clog 2 (min (DigitConvolution.blockCount B x) (DigitConvolution.blockCount B y)))) ∧
    (∀ a ∈ coefficients B x y, ∀ j,
      a+carryAt (2^B) (coefficients B x y) 0 j <
        2^(2*B+Nat.clog 2 (min (DigitConvolution.blockCount B x) (DigitConvolution.blockCount B y)))) :=
  IntMul.CarryNormalization.product_recovery B hB x y

#print axioms solution
