-- Prove2me | solution 1 for IntMul.CarryProduct.carry_product
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T13:17:28.023271+00:00
-- url     : https://prove2.me/submissions/9cb462b5-e697-44dc-b2e4-930e2c1d514e

import Definitions.Def_IntMul_BinaryAdder
import Definitions.Def_IntMul_MultitapeModel
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic
import Definitions.Def_IntMul_CarryProduct
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



namespace IntMul.CarryProduct

private theorem coefficient_values (B : ℕ) (x y : List Bool) (hB : 0 < B) :
    (coefficientWords B x y).map val=CarryNormalization.coefficients B x y := by
  have hb := (CarryNormalization.product_recovery B hB x y).2.2.2.2
  have hm : (CarryNormalization.coefficients B x y).map
      (fun a => val (bin (coefficientWidth B x y) a))=
      (CarryNormalization.coefficients B x y).map id := by
    apply List.map_congr_left
    intro a ha
    have h := hb a ha 0
    simp only [CarryNormalization.carryAt,List.take_zero,CarryNormalization.scan,Nat.add_zero] at h
    change a < 2^coefficientWidth B x y at h
    rw [CarryProductEncoding.bin_value,Nat.mod_eq_of_lt h]
    rfl
  simpa only [coefficientWords,List.map_map,List.map_id,Function.comp_def] using hm

private theorem coefficient_word_width (B : ℕ) (x y : List Bool) :
    ∀ w ∈ coefficientWords B x y, w.length=coefficientWidth B x y := by
  intro w hw
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
  simp [bin]

private theorem coefficient_word_count (B : ℕ) (x y : List Bool) :
    (coefficientWords B x y).length=DigitConvolution.blockCount B x+DigitConvolution.blockCount B y := by
  simp [coefficientWords,CarryNormalization.coefficients]

private theorem zero_carry_value (B : ℕ) (x y : List Bool) :
    val (bin (coefficientWidth B x y) 0)=0 := by
  rw [CarryProductEncoding.bin_value]
  simp

end IntMul.CarryProduct


namespace IntMul.CarryProduct

private theorem final_carry_width (z : List Bool) (xs : List (List Bool)) (y : List Bool) (n : ℕ)
    (hy : y.length=n) (hx : ∀ w ∈ xs, w.length=n) :
    (CarryBatch.scanWords z xs y).2.length=n := by
  induction xs generalizing y with
  | nil => exact hy
  | cons x xs ih =>
      have hx0 : x.length=n := hx x (by simp)
      have hxt : ∀ w ∈ xs, w.length=n := by intro w hw;exact hx w (by simp [hw])
      have hc : (PaddedCarryStep.nextCarryWord x y z).length=n := by
        simp [PaddedCarryStep.nextCarryWord,bin,hx0]
      exact ih _ hc hxt

end IntMul.CarryProduct



namespace IntMul.CarryProduct

/-- Actual product recovery from an explicit prepared convolution coefficient
frame, with no coefficient-generation or global initialization cost hidden. -/
private theorem carry_product (pre x y z l : List Bool)
    (hl : val l+1=coefficientWidth (CarryStep.blockSize z) x y) :
    ∃ t : ℕ,
      t ≤ (DigitConvolution.blockCount (CarryStep.blockSize z) x+
        DigitConvolution.blockCount (CarryStep.blockSize z) y)*
        (41*coefficientWidth (CarryStep.blockSize z) x y+21*CarryStep.blockSize z+
          21*z.length+4*l.length+126)+21 ∧
      machine.step^[t] (initialFrame pre x y z l)=finalFrame pre x y z l ∧
      (machine.step^[t] (initialFrame pre x y z l)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame pre x y z l)).cells 1=
        machine.tapeOf ((bin (CarryStep.blockSize z*
          (DigitConvolution.blockCount (CarryStep.blockSize z) x+
            DigitConvolution.blockCount (CarryStep.blockSize z) y)) (val x*val y)).map machine.bitSym) ∧
      (machine.step^[t] (initialFrame pre x y z l)).cells 12=
        machine.tapeOf ((bin (coefficientWidth (CarryStep.blockSize z) x y) 0).map machine.bitSym) := by
  have hB : 0 < CarryStep.blockSize z := by simp [CarryStep.blockSize]
  have hy : (bin (coefficientWidth (CarryStep.blockSize z) x y) 0).length=val l+1 := by
    simp only [bin,List.length_ofFn];exact hl.symm
  have hx : ∀ w ∈ coefficientWords (CarryStep.blockSize z) x y, w.length=val l+1 := by
    intro w hw;rw [coefficient_word_width _ _ _ w hw];exact hl.symm
  have hb : CarryStep.blockSize z ≤ val l+2 := by
    unfold coefficientWidth at hl
    omega
  obtain ⟨t,ht,he,hh,hout,hcarry⟩ := CarryOutput.carry_output pre
    (coefficientWords (CarryStep.blockSize z) x y) []
    (bin (coefficientWidth (CarryStep.blockSize z) x y) 0) z l hy hx hb
  have hcoeff := coefficient_values (CarryStep.blockSize z) x y hB
  have hz := zero_carry_value (CarryStep.blockSize z) x y
  have hp := CarryNormalization.product_recovery (CarryStep.blockSize z) hB x y
  rw [hcoeff,hz] at hout hcarry
  have hword := hp.1
  change ((CarryNormalization.scan (2^CarryStep.blockSize z)
    (CarryNormalization.coefficients (CarryStep.blockSize z) x y) 0).1.flatMap
      (fun d => (bin (CarryStep.blockSize z) d).reverse)).reverse=_ at hword
  simp only [List.nil_append] at hout
  rw [hword] at hout
  rw [hp.2.1] at hcarry
  have hcwidth := final_carry_width z (coefficientWords (CarryStep.blockSize z) x y)
    (bin (coefficientWidth (CarryStep.blockSize z) x y) 0)
    (coefficientWidth (CarryStep.blockSize z) x y)
    (by simp [bin]) (coefficient_word_width _ _ _)
  have hcword := CarryProductEncoding.bin_value_roundtrip
    (CarryBatch.scanWords z (coefficientWords (CarryStep.blockSize z) x y)
      (bin (coefficientWidth (CarryStep.blockSize z) x y) 0)).2
  rw [hcwidth,hcarry] at hcword
  change machine.step^[t] (initialFrame pre x y z l)=finalFrame pre x y z l at he
  refine ⟨t,?_,he,hh,hout,?_⟩
  · simpa only [coefficient_word_count,hl,List.length_nil,Nat.mul_zero,Nat.add_zero] using ht
  · rw [he]
    change (CanonicalOutput.finalFrame
      (CarryOutput.outputBase pre (coefficientWords (CarryStep.blockSize z) x y) []
        (bin (coefficientWidth (CarryStep.blockSize z) x y) 0) z l)
      ([]++(CarryBatch.scanWords z (coefficientWords (CarryStep.blockSize z) x y)
        (bin (coefficientWidth (CarryStep.blockSize z) x y) 0)).1)).cells 12=_
    simp only [CanonicalOutput.finalFrame,Function.update_of_ne (by decide : (12 : Fin 15)≠2),
      Function.update_of_ne (by decide : (12 : Fin 15)≠1)]
    change machine.tapeOf
      ((CarryBatch.scanWords z (coefficientWords (CarryStep.blockSize z) x y)
        (bin (coefficientWidth (CarryStep.blockSize z) x y) 0)).2.map machine.bitSym)=_
    rw [← hcword]

end IntMul.CarryProduct



open IntMul IntMul.CarryProduct

theorem solution (pre x y z l : List Bool)
    (hl : val l+1=coefficientWidth (CarryStep.blockSize z) x y) :
    ∃ t : ℕ,
      t ≤ (DigitConvolution.blockCount (CarryStep.blockSize z) x+
        DigitConvolution.blockCount (CarryStep.blockSize z) y)*
        (41*coefficientWidth (CarryStep.blockSize z) x y+21*CarryStep.blockSize z+
          21*z.length+4*l.length+126)+21 ∧
      machine.step^[t] (initialFrame pre x y z l)=finalFrame pre x y z l ∧
      (machine.step^[t] (initialFrame pre x y z l)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame pre x y z l)).cells 1=
        machine.tapeOf ((bin (CarryStep.blockSize z*
          (DigitConvolution.blockCount (CarryStep.blockSize z) x+
            DigitConvolution.blockCount (CarryStep.blockSize z) y)) (val x*val y)).map machine.bitSym) ∧
      (machine.step^[t] (initialFrame pre x y z l)).cells 12=
        machine.tapeOf ((bin (coefficientWidth (CarryStep.blockSize z) x y) 0).map machine.bitSym) :=
  IntMul.CarryProduct.carry_product pre x y z l hl

#print axioms solution
