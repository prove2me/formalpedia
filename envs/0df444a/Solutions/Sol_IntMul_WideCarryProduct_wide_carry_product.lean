-- Prove2me | solution 1 for IntMul.WideCarryProduct.wide_carry_product
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T16:09:01.29698+00:00
-- url     : https://prove2.me/submissions/db786ca3-f42d-4064-8255-bad29f6947e8

import Definitions.Def_IntMul_BinaryAdder
import Definitions.Def_IntMul_MultitapeModel
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic
import Definitions.Def_IntMul_WideCarryProduct
import Theorems.Thm_IntMul_CarryNormalization_product_recovery
import Theorems.Thm_IntMul_CarryOutput_carry_output

set_option maxHeartbeats 1000000
set_option Elab.async false


namespace IntMul.CarryProductEncoding
open IntMul.BinaryAdder (littleVal)

private theorem owned_intmulcarryproductencoding_little_value_bound (x : List Bool) : littleVal x < 2 ^ x.length := by
  induction x with
  | nil => simp [littleVal]
  | cons b xs ih =>
      cases b <;> simp only [littleVal, List.length_cons, pow_succ,
        Bool.toNat_false, Bool.toNat_true] <;> omega

private theorem owned_intmulcarryproductencoding_foldl_affine (x : List Bool) (a : ℕ) :
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

private theorem owned_intmulcarryproductencoding_val_append (x y : List Bool) :
    IntMul.val (x ++ y) = 2 ^ y.length * IntMul.val x + IntMul.val y := by
  unfold IntMul.val
  rw [List.foldl_append]
  exact owned_intmulcarryproductencoding_foldl_affine y _

private theorem owned_intmulcarryproductencoding_val_singleton (b : Bool) : IntMul.val [b] = b.toNat := by
  simp [IntMul.val]

private theorem owned_intmulcarryproductencoding_val_reverse_little (x : List Bool) : IntMul.val x.reverse = littleVal x := by
  induction x with
  | nil => simp [IntMul.val, littleVal]
  | cons b xs ih =>
      rw [List.reverse_cons, owned_intmulcarryproductencoding_val_append, owned_intmulcarryproductencoding_val_singleton]
      simp only [List.length_singleton, pow_one, ih, littleVal]
      ring


private theorem owned_intmulcarryproductencoding_little_value_test_bit (x : List Bool) (i : ℕ) :
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
    rw [← owned_intmulcarryproductencoding_val_reverse_little, List.reverse_reverse]
  apply List.ext_getElem (by simp [IntMul.bin])
  intro i hi hx
  simp only [IntMul.bin, List.getElem_ofFn]
  rw [hv, owned_intmulcarryproductencoding_little_value_test_bit]
  have hj : x.length - 1 - i < x.reverse.length := by simp only [List.length_reverse]; omega
  rw [List.getD_eq_getElem _ _ hj, List.getElem_reverse hj]
  have he : x.length - 1 - (x.length - 1 - i) = i := by omega
  simp only [he]


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
    rw [←owned_intmulcarryproductencoding_val_reverse_little,List.reverse_reverse]
  rw [hv,bin_reverse]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [owned_intmulcarryproductencoding_little_value_test_bit,Nat.testBit_mod_two_pow]
  by_cases hj : j < B
  · rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_ofFn]
    simp [hj]
  · rw [List.getD_eq_default _ _ (by simp;omega)]
    simp [hj]


end IntMul.CarryProductEncoding


namespace IntMul.WideCarryProduct

private theorem coefficient_values (N B : ℕ) (x y : List Bool) (hB : 0< B)
    (hN : CarryProduct.coefficientWidth B x y≤ N) :
    (coefficientWords N B x y).map val=CarryNormalization.coefficients B x y := by
  have hb := (CarryNormalization.product_recovery B hB x y).2.2.2.2
  have hm : (CarryNormalization.coefficients B x y).map (fun a => val (bin N a))=
      (CarryNormalization.coefficients B x y).map id := by
    apply List.map_congr_left
    intro a ha
    have h := hb a ha 0
    simp only [CarryNormalization.carryAt,List.take_zero,CarryNormalization.scan,Nat.add_zero] at h
    change a< 2^CarryProduct.coefficientWidth B x y at h
    have hn : a< 2^N := lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide : 1≤ (2:ℕ)) hN)
    rw [CarryProductEncoding.bin_value,Nat.mod_eq_of_lt hn];rfl
  simpa only [coefficientWords,List.map_map,List.map_id,Function.comp_def] using hm

private theorem coefficient_word_width (N B : ℕ) (x y : List Bool) :
    ∀ w ∈ coefficientWords N B x y, w.length=N := by
  intro w hw;obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw;simp [bin]
private theorem coefficient_word_count (N B : ℕ) (x y : List Bool) :
    (coefficientWords N B x y).length=DigitConvolution.blockCount B x+DigitConvolution.blockCount B y := by
  simp [coefficientWords,CarryNormalization.coefficients]
private theorem zero_carry_value (N : ℕ) : val (bin N 0)=0 := by
  rw [CarryProductEncoding.bin_value];simp

private theorem final_carry_width (z : List Bool) (xs : List (List Bool)) (y : List Bool) (n : ℕ)
    (hy : y.length=n) (hx : ∀ w ∈ xs, w.length=n) :
    (CarryBatch.scanWords z xs y).2.length=n := by
  induction xs generalizing y with
  | nil => exact hy
  | cons x xs ih =>
      have hx0 : x.length=n := hx x (by simp)
      have hxt : ∀ w ∈ xs, w.length=n := by intro w hw;exact hx w (by simp [hw])
      have hc : (PaddedCarryStep.nextCarryWord x y z).length=n := by simp [PaddedCarryStep.nextCarryWord,bin,hx0]
      exact ih _ hc hxt
end IntMul.WideCarryProduct


namespace IntMul.WideCarryProduct

/-- Actual product recovery from an explicit prepared convolution coefficient
frame, with no coefficient-generation or global initialization cost hidden. -/
private theorem wide_carry_product (pre x y z l : List Bool)
    (hN : CarryProduct.coefficientWidth (CarryStep.blockSize z) x y≤ val l+1) :
    ∃ t : ℕ,
      t ≤ (DigitConvolution.blockCount (CarryStep.blockSize z) x+
        DigitConvolution.blockCount (CarryStep.blockSize z) y)*
        (41*(val l+1)+21*CarryStep.blockSize z+
          21*z.length+4*l.length+126)+21 ∧
      machine.step^[t] (initialFrame pre x y z l)=finalFrame pre x y z l ∧
      (machine.step^[t] (initialFrame pre x y z l)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame pre x y z l)).cells 1=
        machine.tapeOf ((bin (CarryStep.blockSize z*
          (DigitConvolution.blockCount (CarryStep.blockSize z) x+
            DigitConvolution.blockCount (CarryStep.blockSize z) y)) (val x*val y)).map machine.bitSym) ∧
      (machine.step^[t] (initialFrame pre x y z l)).cells 12=
        machine.tapeOf ((bin ((val l+1)) 0).map machine.bitSym) := by
  have hB : 0 < CarryStep.blockSize z := by simp [CarryStep.blockSize]
  have hy : (bin ((val l+1)) 0).length=val l+1 := by
    simp [bin]
  have hx : ∀ w ∈ coefficientWords (val l+1) (CarryStep.blockSize z) x y, w.length=val l+1 := by
    intro w hw;rw [coefficient_word_width _ _ _ _ w hw]
  have hb : CarryStep.blockSize z ≤ val l+2 := by
    unfold CarryProduct.coefficientWidth at hN
    omega
  obtain ⟨t,ht,he,hh,hout,hcarry⟩ := CarryOutput.carry_output pre
    (coefficientWords (val l+1) (CarryStep.blockSize z) x y) []
    (bin ((val l+1)) 0) z l hy hx hb
  have hcoeff := coefficient_values (val l+1) (CarryStep.blockSize z) x y hB hN
  have hz := zero_carry_value (val l+1)
  have hp := CarryNormalization.product_recovery (CarryStep.blockSize z) hB x y
  rw [hcoeff,hz] at hout hcarry
  have hword := hp.1
  change ((CarryNormalization.scan (2^CarryStep.blockSize z)
    (CarryNormalization.coefficients (CarryStep.blockSize z) x y) 0).1.flatMap
      (fun d => (bin (CarryStep.blockSize z) d).reverse)).reverse=_ at hword
  simp only [List.nil_append] at hout
  rw [hword] at hout
  rw [hp.2.1] at hcarry
  have hcwidth := final_carry_width z (coefficientWords (val l+1) (CarryStep.blockSize z) x y)
    (bin ((val l+1)) 0)
    ((val l+1))
    (by simp [bin]) (coefficient_word_width _ _ _ _)
  have hcword := CarryProductEncoding.bin_value_roundtrip
    (CarryBatch.scanWords z (coefficientWords (val l+1) (CarryStep.blockSize z) x y)
      (bin ((val l+1)) 0)).2
  rw [hcwidth,hcarry] at hcword
  change machine.step^[t] (initialFrame pre x y z l)=finalFrame pre x y z l at he
  refine ⟨t,?_,he,hh,hout,?_⟩
  · simpa only [coefficient_word_count,List.length_nil,Nat.mul_zero,Nat.add_zero] using ht
  · rw [he]
    change (CanonicalOutput.finalFrame
      (CarryOutput.outputBase pre (coefficientWords (val l+1) (CarryStep.blockSize z) x y) []
        (bin ((val l+1)) 0) z l)
      ([]++(CarryBatch.scanWords z (coefficientWords (val l+1) (CarryStep.blockSize z) x y)
        (bin ((val l+1)) 0)).1)).cells 12=_
    simp only [CanonicalOutput.finalFrame,Function.update_of_ne (by decide : (12 : Fin 15)≠2),
      Function.update_of_ne (by decide : (12 : Fin 15)≠1)]
    change machine.tapeOf
      ((CarryBatch.scanWords z (coefficientWords (val l+1) (CarryStep.blockSize z) x y)
        (bin ((val l+1)) 0)).2.map machine.bitSym)=_
    rw [← hcword]

end IntMul.WideCarryProduct



open IntMul IntMul.WideCarryProduct

theorem solution (pre x y z l : List Bool)
    (hN : CarryProduct.coefficientWidth (CarryStep.blockSize z) x y≤ val l+1) :
    ∃ t : ℕ,
      t ≤ (DigitConvolution.blockCount (CarryStep.blockSize z) x+
        DigitConvolution.blockCount (CarryStep.blockSize z) y)*
        (41*(val l+1)+21*CarryStep.blockSize z+
          21*z.length+4*l.length+126)+21 ∧
      machine.step^[t] (initialFrame pre x y z l)=finalFrame pre x y z l ∧
      (machine.step^[t] (initialFrame pre x y z l)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame pre x y z l)).cells 1=
        machine.tapeOf ((bin (CarryStep.blockSize z*
          (DigitConvolution.blockCount (CarryStep.blockSize z) x+
            DigitConvolution.blockCount (CarryStep.blockSize z) y)) (val x*val y)).map machine.bitSym) ∧
      (machine.step^[t] (initialFrame pre x y z l)).cells 12=
        machine.tapeOf ((bin ((val l+1)) 0).map machine.bitSym) :=
  IntMul.WideCarryProduct.wide_carry_product pre x y z l hN

#print axioms solution
