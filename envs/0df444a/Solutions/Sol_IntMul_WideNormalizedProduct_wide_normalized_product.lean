-- Prove2me | solution 1 for IntMul.WideNormalizedProduct.wide_normalized_product
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T16:22:00.49059+00:00
-- url     : https://prove2.me/submissions/2b638076-7329-4b50-bade-9802a39d33d9

import Definitions.Def_IntMul_WideNormalizedProduct
import Mathlib.Tactic
import Definitions.Def_IntMul_BinaryAdder
import Definitions.Def_IntMul_MultitapeModel
import Mathlib.Data.Nat.Bits
import Theorems.Thm_IntMul_WideCarryProduct_wide_carry_product
import Theorems.Thm_IntMul_WidthPreparation_prepare_width
import Theorems.Thm_IntMul_FixedOutputWidth_fixed_output_width
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Theorems.Thm_IntMul_FiniteCaller_simulate_run

set_option maxHeartbeats 1000000
set_option Elab.async false


namespace IntMul.WideNormalizedProduct

private theorem cfg_ext (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c;cases d;cases hs;cases hc;cases hh;rfl

private theorem product_step (c : productNative.Cfg) :
    subroutine.step (productView c)=productView (productNative.step c) := by
  let a : Fin 16 → TapeCopy.Sym := fun i => c.cells i (c.head i)
  have ht : transition (productState c.state) a=
      (productState (productNative.δ c.state a).1,(productNative.δ c.state a).2) := by
    by_cases h : c.state=productNative.qHalt
    · rw [h,productNative.halt_fixed a]
      rfl
    · conv_lhs => rw [productState,if_neg h]
      rfl
  change transition (productView c).state
    (fun i => (productView c).cells i ((productView c).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl

private theorem product_run (c : productNative.Cfg) (t : ℕ) :
    subroutine.step^[t] (productView c)=productView (productNative.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,product_step,Function.iterate_succ_apply']

private theorem preparation_step (c : WidthPreparation.machine.Cfg) :
    subroutine.step (preparationView c)=preparationView (WidthPreparation.machine.step c) := by
  let a : Fin 16 → TapeCopy.Sym := fun i => c.cells i (c.head i)
  have ht : transition (preparationState c.state) a=
      (preparationState (WidthPreparation.machine.δ c.state a).1,(WidthPreparation.machine.δ c.state a).2) := by
    by_cases h : c.state=WidthPreparation.machine.qHalt
    · rw [h,WidthPreparation.machine.halt_fixed a]
      rfl
    · conv_lhs => rw [preparationState,if_neg h]
      rfl
  change transition (preparationView c).state
    (fun i => (preparationView c).cells i ((preparationView c).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl

private theorem preparation_run (c : WidthPreparation.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (preparationView c)=preparationView (WidthPreparation.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,preparation_step,Function.iterate_succ_apply']

private theorem width_step (c : widthNative.Cfg) :
    subroutine.step (widthView c)=widthView (widthNative.step c) := by
  let a : Fin 16 → TapeCopy.Sym := fun i => c.cells i (c.head i)
  have ht : transition (widthState c.state) a=
      (widthState (widthNative.δ c.state a).1,(widthNative.δ c.state a).2) := by
    by_cases h : c.state=widthNative.qHalt
    · rw [h,widthNative.halt_fixed a]
      rfl
    · conv_lhs => rw [widthState,if_neg h]
      rfl
  change transition (widthView c).state
    (fun i => (widthView c).cells i ((widthView c).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl

private theorem width_run (c : widthNative.Cfg) (t : ℕ) :
    subroutine.step^[t] (widthView c)=widthView (widthNative.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,width_step,Function.iterate_succ_apply']

end IntMul.WideNormalizedProduct



namespace IntMul.WideNormalizedProduct

private theorem scan_length (z : List Bool) (xs : List (List Bool)) (y : List Bool) (n : ℕ)
    (hx : ∀ w ∈ xs, w.length=n) (hB : CarryStep.blockSize z ≤ n+1) :
    (CarryBatch.scanWords z xs y).1.length=xs.length*CarryStep.blockSize z := by
  induction xs generalizing y with
  | nil => simp [CarryBatch.scanWords]
  | cons x xs ih =>
      have hx0 : x.length=n := hx x (by simp)
      have hxt : ∀ w ∈ xs, w.length=n := by intro w hw;exact hx w (by simp [hw])
      have hd : (CarryStep.digitWord x y z).length=CarryStep.blockSize z := by
        simp [CarryStep.digitWord,CarryStep.sumWord,bin,Nat.min_eq_left (by omega : CarryStep.blockSize z ≤ x.length+1)]
      change (CarryStep.digitWord x y z++
        (CarryBatch.scanWords z xs (PaddedCarryStep.nextCarryWord x y z)).1).length=_
      rw [List.length_append,hd,ih (PaddedCarryStep.nextCarryWord x y z) hxt]
      simp [List.length_cons,Nat.add_mul,Nat.add_comm]

private theorem coefficient_word_width (N B : ℕ) (x y : List Bool) :
    ∀ w ∈ WideCarryProduct.coefficientWords N B x y, w.length=N := by
  intro w hw
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
  simp [bin]

private theorem coefficient_word_count (N B : ℕ) (x y : List Bool) :
    (WideCarryProduct.coefficientWords N B x y).length=DigitConvolution.blockCount B x+DigitConvolution.blockCount B y := by
  simp [WideCarryProduct.coefficientWords,CarryNormalization.coefficients]

private theorem product_head (pre x y z l : List Bool) (hb : CarryStep.blockSize z≤ val l+2) :
    (WideCarryProduct.finalFrame pre x y z l).head 1=
      CarryStep.blockSize z*(DigitConvolution.blockCount (CarryStep.blockSize z) x+
        DigitConvolution.blockCount (CarryStep.blockSize z) y)+1 := by
  have h := scan_length z (WideCarryProduct.coefficientWords (val l+1) (CarryStep.blockSize z) x y)
    (bin (val l+1) 0) (val l+1) (coefficient_word_width _ _ _ _) hb
  simp only [WideCarryProduct.finalFrame,CarryOutput.finalFrame,CanonicalOutput.finalFrame,
    Function.update_of_ne (by decide : (1 : Fin 15)≠2),Function.update_self]
  change ([]++(CarryBatch.scanWords z (WideCarryProduct.coefficientWords (val l+1) (CarryStep.blockSize z) x y)
    (bin (val l+1) 0)).1).length+1=_
  rw [List.nil_append,h,coefficient_word_count,Nat.mul_comm]
end IntMul.WideNormalizedProduct


namespace IntMul.WideNormalizedProduct

private noncomputable def preparationBase (base : machine.Cfg) (pre x y z l d : List Bool) : WidthPreparation.machine.Cfg where
  state := .halt
  cells := (productFinal base pre x y z l d).cells
  head := (productFinal base pre x y z l d).head

private noncomputable def preparationIncoming (base : machine.Cfg) (pre x y z l d : List Bool) : WidthPreparation.machine.Cfg :=
  WidthPreparation.initialFrame (preparationBase base pre x y z l d) d
private noncomputable def preparationFinal (base : machine.Cfg) (pre x y z l d : List Bool) : WidthPreparation.machine.Cfg :=
  WidthPreparation.finalFrame (preparationBase base pre x y z l d) d

private noncomputable def widthBase (base : machine.Cfg) (pre x y z l d : List Bool) : FixedOutputWidth.machine.Cfg where
  state := none
  cells := fun j => (preparationFinal base pre x y z l d).cells (FixedTapeExtension.oldTape FixedOutputWidth.machine j)
  head := fun j => (preparationFinal base pre x y z l d).head (FixedTapeExtension.oldTape FixedOutputWidth.machine j)
private noncomputable def widthExtendedBase (base : machine.Cfg) (pre x y z l d : List Bool) : widthNative.Cfg where
  state := none
  cells := (preparationFinal base pre x y z l d).cells
  head := (preparationFinal base pre x y z l d).head
private noncomputable def paddedWord (x y z : List Bool) : List Bool :=
  bin (CarryStep.blockSize z*(DigitConvolution.blockCount (CarryStep.blockSize z) x+
    DigitConvolution.blockCount (CarryStep.blockSize z) y)) (val x*val y)
private noncomputable def widthIncoming (base : machine.Cfg) (pre x y z l d : List Bool) : widthNative.Cfg :=
  FixedTapeExtension.embed FixedOutputWidth.machine (widthExtendedBase base pre x y z l d)
    (FixedOutputWidth.initialFrame (widthBase base pre x y z l d) (paddedWord x y z) d)
private noncomputable def widthFinal (base : machine.Cfg) (pre x y z l d : List Bool) : widthNative.Cfg :=
  FixedTapeExtension.embed FixedOutputWidth.machine (widthExtendedBase base pre x y z l d)
    (FixedOutputWidth.finalFrame (widthBase base pre x y z l d) (paddedWord x y z) d)

private theorem preparation_ready (base : machine.Cfg) (pre x y z l d : List Bool) :
    (preparationIncoming base pre x y z l d).cells=(productFinal base pre x y z l d).cells ∧
    (preparationIncoming base pre x y z l d).head=(productFinal base pre x y z l d).head := by
  have c3 : (productFinal base pre x y z l d).cells 3=WidthPreparation.machine.tapeOf [] := by
    simp [productFinal,FixedTapeExtension.embed,FixedTapeExtension.innerTape,WideCarryProduct.finalFrame,
      CarryOutput.finalFrame,CanonicalOutput.finalFrame,CarryOutput.outputBase,CarryBatch.finalFrame] <;> rfl
  have c4 : (productFinal base pre x y z l d).cells 4=WidthPreparation.machine.tapeOf [] := by
    simp [productFinal,FixedTapeExtension.embed,FixedTapeExtension.innerTape,WideCarryProduct.finalFrame,
      CarryOutput.finalFrame,CanonicalOutput.finalFrame,CarryOutput.outputBase,CarryBatch.finalFrame] <;> rfl
  have c15 : (productFinal base pre x y z l d).cells 15=WidthPreparation.machine.tapeOf (d.map WidthPreparation.machine.bitSym) := by
    simp [productFinal,FixedTapeExtension.embed,productBase] <;> rfl
  have h3 : (productFinal base pre x y z l d).head 3=0 := by
    simp [productFinal,FixedTapeExtension.embed,FixedTapeExtension.innerTape,WideCarryProduct.finalFrame,
      CarryOutput.finalFrame,CanonicalOutput.finalFrame,CarryOutput.outputBase,CarryBatch.finalFrame] <;> rfl
  have h4 : (productFinal base pre x y z l d).head 4=0 := by
    simp [productFinal,FixedTapeExtension.embed,FixedTapeExtension.innerTape,WideCarryProduct.finalFrame,
      CarryOutput.finalFrame,CanonicalOutput.finalFrame,CarryOutput.outputBase,CarryBatch.finalFrame] <;> rfl
  have h15 : (productFinal base pre x y z l d).head 15=0 := by
    simp [productFinal,FixedTapeExtension.embed,productBase] <;> rfl
  constructor
  · change Function.update (Function.update (Function.update (productFinal base pre x y z l d).cells 15 _) 3 _) 4 _=_
    have u15 : Function.update (productFinal base pre x y z l d).cells 15
        (WidthPreparation.machine.tapeOf (d.map WidthPreparation.machine.bitSym))=(productFinal base pre x y z l d).cells := by
      simpa only [c15] using (Function.update_eq_self (15 : Fin 16) (productFinal base pre x y z l d).cells)
    have u3 : Function.update (productFinal base pre x y z l d).cells 3 (WidthPreparation.machine.tapeOf [])=(productFinal base pre x y z l d).cells := by
      simpa only [c3] using (Function.update_eq_self (3 : Fin 16) (productFinal base pre x y z l d).cells)
    have u4 : Function.update (productFinal base pre x y z l d).cells 4 (WidthPreparation.machine.tapeOf [])=(productFinal base pre x y z l d).cells := by
      simpa only [c4] using (Function.update_eq_self (4 : Fin 16) (productFinal base pre x y z l d).cells)
    rw [u15,u3,u4]
  · change Function.update (Function.update (Function.update (productFinal base pre x y z l d).head 15 _) 3 _) 4 _=_
    have u15 : Function.update (productFinal base pre x y z l d).head 15 0=(productFinal base pre x y z l d).head := by
      simpa only [h15] using (Function.update_eq_self (15 : Fin 16) (productFinal base pre x y z l d).head)
    have u3 : Function.update (productFinal base pre x y z l d).head 3 0=(productFinal base pre x y z l d).head := by
      simpa only [h3] using (Function.update_eq_self (3 : Fin 16) (productFinal base pre x y z l d).head)
    have u4 : Function.update (productFinal base pre x y z l d).head 4 0=(productFinal base pre x y z l d).head := by
      simpa only [h4] using (Function.update_eq_self (4 : Fin 16) (productFinal base pre x y z l d).head)
    rw [u15,u3,u4]

private theorem after_product (base : machine.Cfg) (pre x y z l d : List Bool) :
    FiniteCaller.returned subroutine Phase .product .product dispatch
      (productView (productFinal base pre x y z l d))=
    FiniteCaller.embed subroutine Phase .product .prepare dispatch
      (preparationView (preparationIncoming base pre x y z l d)) := by
  have h := preparation_ready base pre x y z l d
  apply cfg_ext
  · rfl
  · exact h.1.symm
  · exact h.2.symm

end IntMul.WideNormalizedProduct



namespace IntMul.WideNormalizedProduct

private theorem width_ready (base : machine.Cfg) (pre x y z l d : List Bool)
    (hN : CarryStep.blockSize z≤ val l+2)
    (hc : (productFinal base pre x y z l d).cells 1=
      widthNative.tapeOf ((paddedWord x y z).map widthNative.bitSym)) :
    (widthIncoming base pre x y z l d).cells=(preparationFinal base pre x y z l d).cells ∧
    (widthIncoming base pre x y z l d).head=(preparationFinal base pre x y z l d).head := by
  have c2 : (productFinal base pre x y z l d).cells 2=FixedOutputWidth.machine.tapeOf [] := by
    simp [productFinal,FixedTapeExtension.embed,FixedTapeExtension.innerTape,WideCarryProduct.finalFrame,
      CarryOutput.finalFrame,CanonicalOutput.finalFrame] <;> rfl
  have h1 : (productFinal base pre x y z l d).head 1=(paddedWord x y z).length+1 := by
    simp only [productFinal,FixedTapeExtension.embed]
    change (WideCarryProduct.finalFrame pre x y z l).head 1=_
    rw [product_head pre x y z l hN]
    simp [paddedWord,bin]
  have h2 : (productFinal base pre x y z l d).head 2=0 := by
    simp [productFinal,FixedTapeExtension.embed,FixedTapeExtension.innerTape,WideCarryProduct.finalFrame,
      CarryOutput.finalFrame,CanonicalOutput.finalFrame]
  constructor
  · funext i
    fin_cases i <;> simp [widthIncoming,FixedTapeExtension.embed,FixedTapeExtension.innerTape,
      FixedTapeExtension.oldTape,widthBase,widthExtendedBase,FixedOutputWidth.initialFrame,
      preparationFinal,WidthPreparation.finalFrame,preparationBase,hc,c2]
    all_goals rfl
  · funext i
    fin_cases i <;> simp [widthIncoming,FixedTapeExtension.embed,FixedTapeExtension.innerTape,
      FixedTapeExtension.oldTape,widthBase,widthExtendedBase,FixedOutputWidth.initialFrame,
      preparationFinal,WidthPreparation.finalFrame,preparationBase,h1,h2]

private theorem after_preparation (base : machine.Cfg) (pre x y z l d : List Bool)
    (hN : CarryStep.blockSize z≤ val l+2)
    (hc : (productFinal base pre x y z l d).cells 1=
      widthNative.tapeOf ((paddedWord x y z).map widthNative.bitSym)) :
    FiniteCaller.returned subroutine Phase .product .prepare dispatch
      (preparationView (preparationFinal base pre x y z l d))=
    FiniteCaller.embed subroutine Phase .product .width dispatch
      (widthView (widthIncoming base pre x y z l d)) := by
  have h := width_ready base pre x y z l d hN hc
  apply cfg_ext
  · rfl
  · exact h.1.symm
  · exact h.2.symm

end IntMul.WideNormalizedProduct



namespace IntMul.WideNormalizedProduct

private theorem after_width (base : machine.Cfg) (pre x y z l d : List Bool)
    (hc : (widthFinal base pre x y z l d).cells 1=
      machine.tapeOf ((bin (FixedOutputWidth.width d) (val x*val y)).map machine.bitSym)) :
    FiniteCaller.returned subroutine Phase .product .width dispatch
      (widthView (widthFinal base pre x y z l d))=finalFrame base pre x y z l d := by
  have c2 : (productFinal base pre x y z l d).cells 2=FixedOutputWidth.machine.tapeOf [] := by
    simp [productFinal,FixedTapeExtension.embed,FixedTapeExtension.innerTape,WideCarryProduct.finalFrame,
      CarryOutput.finalFrame,CanonicalOutput.finalFrame] <;> rfl
  have h2 : (productFinal base pre x y z l d).head 2=0 := by
    simp [productFinal,FixedTapeExtension.embed,FixedTapeExtension.innerTape,WideCarryProduct.finalFrame,
      CarryOutput.finalFrame,CanonicalOutput.finalFrame]
  have h15 : (productFinal base pre x y z l d).head 15=0 := by
    simp [productFinal,FixedTapeExtension.embed,productBase]
  apply cfg_ext
  · rfl
  · change (widthFinal base pre x y z l d).cells=_
    funext i
    by_cases hi : i=1
    · subst i
      simpa only [finalFrame,Function.update_of_ne (by decide : (1 : Fin 16)≠4),
        Function.update_of_ne (by decide : (1 : Fin 16)≠3),Function.update_self] using hc
    · fin_cases i <;> simp_all [widthFinal,FixedTapeExtension.embed,FixedTapeExtension.innerTape,
        FixedTapeExtension.oldTape,widthBase,widthExtendedBase,FixedOutputWidth.finalFrame,
        preparationFinal,WidthPreparation.finalFrame,preparationBase,finalFrame]
      all_goals rfl
  · change (widthFinal base pre x y z l d).head=_
    funext i
    fin_cases i <;> simp [widthFinal,FixedTapeExtension.embed,FixedTapeExtension.innerTape,
      FixedTapeExtension.oldTape,widthBase,widthExtendedBase,FixedOutputWidth.finalFrame,
      preparationFinal,WidthPreparation.finalFrame,preparationBase,finalFrame,h2,h15]

end IntMul.WideNormalizedProduct



namespace IntMul.WideNormalizedProductEncoding
open IntMul.BinaryAdder (littleVal)

private theorem owned_intmulwidenormalizedproductencoding_little_value_bound (x : List Bool) : littleVal x < 2 ^ x.length := by
  induction x with
  | nil => simp [littleVal]
  | cons b xs ih =>
      cases b <;> simp only [littleVal, List.length_cons, pow_succ,
        Bool.toNat_false, Bool.toNat_true] <;> omega

private theorem owned_intmulwidenormalizedproductencoding_foldl_affine (x : List Bool) (a : ℕ) :
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

private theorem owned_intmulwidenormalizedproductencoding_val_append (x y : List Bool) :
    IntMul.val (x ++ y) = 2 ^ y.length * IntMul.val x + IntMul.val y := by
  unfold IntMul.val
  rw [List.foldl_append]
  exact owned_intmulwidenormalizedproductencoding_foldl_affine y _

private theorem owned_intmulwidenormalizedproductencoding_val_singleton (b : Bool) : IntMul.val [b] = b.toNat := by
  simp [IntMul.val]

private theorem owned_intmulwidenormalizedproductencoding_val_reverse_little (x : List Bool) : IntMul.val x.reverse = littleVal x := by
  induction x with
  | nil => simp [IntMul.val, littleVal]
  | cons b xs ih =>
      rw [List.reverse_cons, owned_intmulwidenormalizedproductencoding_val_append, owned_intmulwidenormalizedproductencoding_val_singleton]
      simp only [List.length_singleton, pow_one, ih, littleVal]
      ring


private theorem owned_intmulwidenormalizedproductencoding_little_value_test_bit (x : List Bool) (i : ℕ) :
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
    rw [← owned_intmulwidenormalizedproductencoding_val_reverse_little, List.reverse_reverse]
  apply List.ext_getElem (by simp [IntMul.bin])
  intro i hi hx
  simp only [IntMul.bin, List.getElem_ofFn]
  rw [hv, owned_intmulwidenormalizedproductencoding_little_value_test_bit]
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
    rw [←owned_intmulwidenormalizedproductencoding_val_reverse_little,List.reverse_reverse]
  rw [hv,bin_reverse]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [owned_intmulwidenormalizedproductencoding_little_value_test_bit,Nat.testBit_mod_two_pow]
  by_cases hj : j < B
  · rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_ofFn]
    simp [hj]
  · rw [List.getD_eq_default _ _ (by simp;omega)]
    simp [hj]


private theorem value_bound (x : List Bool) : val x < 2^x.length := by
  have h := owned_intmulwidenormalizedproductencoding_little_value_bound x.reverse
  have e : val x=littleVal x.reverse := by rw [← owned_intmulwidenormalizedproductencoding_val_reverse_little,List.reverse_reverse]
  simpa only [← e,List.length_reverse] using h

end IntMul.WideNormalizedProductEncoding



namespace IntMul.WideNormalizedProduct

private theorem block_padding_bound (B : ℕ) (x : List Bool) (hB : 0 < B) :
    x.length ≤ B*DigitConvolution.blockCount B x := by
  have hm := Nat.mod_lt (x.length+B-1) hB
  have he := Nat.mod_add_div (x.length+B-1) B
  unfold DigitConvolution.blockCount
  omega

private theorem product_padding_bound (x y z : List Bool) :
    x.length+y.length ≤ CarryStep.blockSize z*
      (DigitConvolution.blockCount (CarryStep.blockSize z) x+
        DigitConvolution.blockCount (CarryStep.blockSize z) y) := by
  have hB : 0 < CarryStep.blockSize z := by simp [CarryStep.blockSize]
  have hx := block_padding_bound (CarryStep.blockSize z) x hB
  have hy := block_padding_bound (CarryStep.blockSize z) y hB
  rw [Nat.mul_add]
  omega

private theorem product_value_bound (x y : List Bool) : val x*val y < 2^(x.length+y.length) := by
  have hx := WideNormalizedProductEncoding.value_bound x
  have hy := WideNormalizedProductEncoding.value_bound y
  rw [pow_add]
  exact lt_of_le_of_lt (Nat.mul_le_mul_left (val x) (le_of_lt hy))
    (Nat.mul_lt_mul_of_pos_right hx (by positivity))

private theorem padded_value (x y z : List Bool) :
    val (bin (CarryStep.blockSize z*(DigitConvolution.blockCount (CarryStep.blockSize z) x+
      DigitConvolution.blockCount (CarryStep.blockSize z) y)) (val x*val y))=val x*val y := by
  rw [WideNormalizedProductEncoding.bin_value,Nat.mod_eq_of_lt]
  exact lt_of_lt_of_le (product_value_bound x y)
    (Nat.pow_le_pow_right (by decide) (product_padding_bound x y z))

end IntMul.WideNormalizedProduct



namespace IntMul.WideNormalizedProduct

/-- Physically complete product recovery and exact-width normalization from
an explicitly prepared coefficient frame. No descriptor preparation, caller
return, tape movement or temporary erasure between these stages is free. -/
private theorem wide_normalized_product (base : machine.Cfg) (pre x y z l d : List Bool)
    (hl : CarryProduct.coefficientWidth (CarryStep.blockSize z) x y≤ val l+1)
    (hd : FixedOutputWidth.width d=x.length+y.length) :
    ∃ t : ℕ,
      t ≤ (DigitConvolution.blockCount (CarryStep.blockSize z) x+
        DigitConvolution.blockCount (CarryStep.blockSize z) y)*
        (41*(val l+1)+32*CarryStep.blockSize z+
          21*z.length+4*l.length+126)+10*FixedOutputWidth.width d+6*d.length+63 ∧
      machine.step^[t] (initialFrame base pre x y z l d)=finalFrame base pre x y z l d ∧
      (machine.step^[t] (initialFrame base pre x y z l d)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame base pre x y z l d)).cells 1=
        machine.tapeOf ((bin (x.length+y.length) (val x*val y)).map machine.bitSym) := by
  have hN : CarryStep.blockSize z≤ val l+2 := by
    unfold CarryProduct.coefficientWidth at hl;omega
  obtain ⟨u,hu,heu,hhu,hpu,hcu⟩ := WideCarryProduct.wide_carry_product pre x y z l hl
  have ec := (FixedTapeExtension.simulate_run WideCarryProduct.machine (productBase base d)
    (WideCarryProduct.initialFrame pre x y z l) u).1
  rw [heu] at ec
  change productNative.step^[u] (productIncoming base pre x y z l d)=productFinal base pre x y z l d at ec
  have cp : (productFinal base pre x y z l d).cells 1=
      widthNative.tapeOf ((paddedWord x y z).map widthNative.bitSym) := by
    simp only [productFinal,FixedTapeExtension.embed]
    change (WideCarryProduct.finalFrame pre x y z l).cells 1=_
    rw [← heu]
    exact hpu
  have ep : subroutine.step^[u] (productView (productIncoming base pre x y z l d))=
      productView (productFinal base pre x y z l d) := by rw [product_run,ec]
  obtain ⟨r,hr,her⟩ := (FiniteCaller.simulate_run subroutine Phase .product .product dispatch
    (productView (productIncoming base pre x y z l d)) u).2 (by rw [ep];rfl)
  rw [ep,after_product] at her
  have eprep := (WidthPreparation.prepare_width (preparationBase base pre x y z l d) d).1
  change WidthPreparation.machine.step^[2*d.length+4] (preparationIncoming base pre x y z l d)=
    preparationFinal base pre x y z l d at eprep
  have esp : subroutine.step^[2*d.length+4] (preparationView (preparationIncoming base pre x y z l d))=
      preparationView (preparationFinal base pre x y z l d) := by rw [preparation_run,eprep]
  obtain ⟨s,hs,hes⟩ := (FiniteCaller.simulate_run subroutine Phase .product .prepare dispatch
    (preparationView (preparationIncoming base pre x y z l d)) (2*d.length+4)).2 (by rw [esp];rfl)
  rw [esp,after_preparation base pre x y z l d hN cp] at hes
  have hW : FixedOutputWidth.width d ≤ (paddedWord x y z).length := by
    rw [hd]
    simpa only [paddedWord,bin,List.length_ofFn] using product_padding_bound x y z
  obtain ⟨v,hv,hev,hhv,houtv⟩ := FixedOutputWidth.fixed_output_width
    (widthBase base pre x y z l d) (paddedWord x y z) d hW
  have ev := (FixedTapeExtension.simulate_run FixedOutputWidth.machine
    (widthExtendedBase base pre x y z l d)
    (FixedOutputWidth.initialFrame (widthBase base pre x y z l d) (paddedWord x y z) d) v).1
  rw [hev] at ev
  change widthNative.step^[v] (widthIncoming base pre x y z l d)=widthFinal base pre x y z l d at ev
  have cv : (widthFinal base pre x y z l d).cells 1=
      machine.tapeOf ((bin (FixedOutputWidth.width d) (val x*val y)).map machine.bitSym) := by
    simp only [widthFinal,FixedTapeExtension.embed]
    change (FixedOutputWidth.finalFrame (widthBase base pre x y z l d) (paddedWord x y z) d).cells 1=_
    rw [← hev]
    have hval : val (paddedWord x y z)=val x*val y := padded_value x y z
    rw [hval] at houtv
    convert houtv using 1 <;> rfl
  have ewp : subroutine.step^[v] (widthView (widthIncoming base pre x y z l d))=
      widthView (widthFinal base pre x y z l d) := by rw [width_run,ev]
  obtain ⟨q,hq,heq⟩ := (FiniteCaller.simulate_run subroutine Phase .product .width dispatch
    (widthView (widthIncoming base pre x y z l d)) v).2 (by rw [ewp];rfl)
  rw [ewp,after_width base pre x y z l d cv] at heq
  have he : machine.step^[q+(s+r)] (initialFrame base pre x y z l d)=finalFrame base pre x y z l d := by
    rw [Function.iterate_add_apply,Function.iterate_add_apply]
    change machine.step^[q] (machine.step^[s]
      (machine.step^[r] (FiniteCaller.embed subroutine Phase .product .product dispatch
        (productView (productIncoming base pre x y z l d)))))=_
    rw [her,hes,heq]
  refine ⟨q+(s+r),?_,he,?_,?_⟩
  · simp only [paddedWord,bin,List.length_ofFn] at hv
    nlinarith
  · rw [he];rfl
  · rw [he]
    simp only [finalFrame,Function.update_of_ne (by decide : (1 : Fin 16)≠4),
      Function.update_of_ne (by decide : (1 : Fin 16)≠3),Function.update_self]
    rw [hd]

end IntMul.WideNormalizedProduct



open IntMul IntMul.WideNormalizedProduct

theorem solution (base : machine.Cfg) (pre x y z l d : List Bool)
    (hl : CarryProduct.coefficientWidth (CarryStep.blockSize z) x y≤ val l+1)
    (hd : FixedOutputWidth.width d=x.length+y.length) :
    ∃ t : ℕ,
      t ≤ (DigitConvolution.blockCount (CarryStep.blockSize z) x+
        DigitConvolution.blockCount (CarryStep.blockSize z) y)*
        (41*(val l+1)+32*CarryStep.blockSize z+
          21*z.length+4*l.length+126)+10*FixedOutputWidth.width d+6*d.length+63 ∧
      machine.step^[t] (initialFrame base pre x y z l d)=finalFrame base pre x y z l d ∧
      (machine.step^[t] (initialFrame base pre x y z l d)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame base pre x y z l d)).cells 1=
        machine.tapeOf ((bin (x.length+y.length) (val x*val y)).map machine.bitSym) :=
  IntMul.WideNormalizedProduct.wide_normalized_product base pre x y z l d hl hd

#print axioms solution
