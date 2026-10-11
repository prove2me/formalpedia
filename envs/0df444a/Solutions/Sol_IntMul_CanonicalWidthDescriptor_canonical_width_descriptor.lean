-- Prove2me | solution 1 for IntMul.CanonicalWidthDescriptor.canonical_width_descriptor
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T14:57:20.091063+00:00
-- url     : https://prove2.me/submissions/47731051-4ac7-414d-940e-a4441c701eaa

import Definitions.Def_IntMul_CanonicalWidthDescriptor
import Mathlib.Tactic
import Theorems.Thm_IntMul_FiniteCaller_simulate_run
import Theorems.Thm_IntMul_InputWidthCounter_input_width_counter
import Theorems.Thm_IntMul_CanonicalOutput_canonical_output

set_option maxHeartbeats 1000000
set_option Elab.async false


set_option maxHeartbeats 1000000
set_option Elab.async false

namespace IntMul.CanonicalWidthDescriptor
open TapeCopy (Sym)

private theorem cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c;cases d;cases hs;cases hc;cases hh;rfl

private noncomputable def countView (base : subroutine.Cfg) (c : InputWidthCounter.machine.Cfg) : subroutine.Cfg where
  state := countState c.state
  cells := fun i => if i=0 then c.cells 0 else if i=1 then c.cells 2 else if i=3 then c.cells 1 else base.cells i
  head := fun i => if i=0 then c.head 0 else if i=1 then c.head 2 else if i=3 then c.head 1 else base.head i

private theorem count_step (base : subroutine.Cfg) (c : InputWidthCounter.machine.Cfg) :
    subroutine.step (countView base c)=countView base (InputWidthCounter.machine.step c) := by
  let a : Fin 15 → Sym := fun i => (countView base c).cells i ((countView base c).head i)
  let b : Fin 3 → Sym := fun j => c.cells j (c.head j)
  have ha : (fun j => a (countTape j))=b := by funext j;fin_cases j <;> rfl
  have ht : transition (countState c.state) a=(countState (InputWidthCounter.machine.δ c.state b).1,
      countAction a (InputWidthCounter.machine.δ c.state b).2) := by
    by_cases h : c.state=none
    · rw [h,InputWidthCounter.machine.halt_fixed b]
      simp only [countState,if_true,transition]
      congr 1
      funext i
      fin_cases i <;> rfl
    · conv_lhs => rw [countState,if_neg h]
      change (countState (InputWidthCounter.machine.δ c.state (fun j => a (countTape j))).1,
        countAction a (InputWidthCounter.machine.δ c.state (fun j => a (countTape j))).2)=_
      rw [ha]
  change transition (countView base c).state
    (fun i => (countView base c).cells i ((countView base c).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> first | rfl | exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> rfl

private theorem count_run (base : subroutine.Cfg) (c : InputWidthCounter.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (countView base c)=countView base (InputWidthCounter.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,count_step,Function.iterate_succ_apply']

private noncomputable def orderView (c : CanonicalOutput.machine.Cfg) : subroutine.Cfg where
  state := orderState c.state
  cells := c.cells
  head := c.head

private theorem order_step (c : CanonicalOutput.machine.Cfg) :
    subroutine.step (orderView c)=orderView (CanonicalOutput.machine.step c) := by
  let a : Fin 15 → Sym := fun i => c.cells i (c.head i)
  have ht : transition (orderState c.state) a=
      (orderState (CanonicalOutput.machine.δ c.state a).1,(CanonicalOutput.machine.δ c.state a).2) := by
    by_cases h : c.state=none
    · rw [h,CanonicalOutput.machine.halt_fixed a]
      simp only [orderState,if_true,transition]
    · conv_lhs => rw [orderState,if_neg h]
      rfl
  change transition (orderView c).state (fun i => (orderView c).cells i ((orderView c).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl

private theorem order_run (c : CanonicalOutput.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (orderView c)=orderView (CanonicalOutput.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,order_step,Function.iterate_succ_apply']

end IntMul.CanonicalWidthDescriptor


namespace IntMul.CanonicalWidthDescriptor
open TapeCopy (Sym)

private noncomputable def emptyBase (x y : List Bool) : subroutine.Cfg where
  state := none
  cells := (initialFrame x y).cells
  head := (initialFrame x y).head

private def counterWord (x y : List Bool) := GrowingCounter.iterateCounter (x.length+y.length-1) []

private noncomputable def countDone (x y : List Bool) : subroutine.Cfg :=
  countView (emptyBase x y) (InputWidthCounter.finalFrame x y)

private noncomputable def seekFrame (x y : List Bool) (j : ℕ) : subroutine.Cfg :=
  {countDone x y with state := seekState,head := Function.update (countDone x y).head 1 (j+1)}
private noncomputable def seekDone (x y : List Bool) : subroutine.Cfg :=
  {seekFrame x y (counterWord x y).length with state := none}

private noncomputable def orderBase (x y : List Bool) : CanonicalOutput.machine.Cfg where
  state := none
  cells := (countDone x y).cells
  head := (countDone x y).head

private noncomputable def orderIn (x y : List Bool) : subroutine.Cfg :=
  orderView (CanonicalOutput.initialFrame (orderBase x y) (counterWord x y))
private noncomputable def orderDone (x y : List Bool) : subroutine.Cfg :=
  orderView (CanonicalOutput.finalFrame (orderBase x y) (counterWord x y))

private theorem initial_handoff (x y : List Bool) :
    initialFrame x y=FiniteCaller.embed subroutine Phase .count .count dispatch
      (countView (emptyBase x y) (InputWidthCounter.initialFrame x y)) := by
  apply cfg_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl

private theorem after_count (x y : List Bool) :
    FiniteCaller.returned subroutine Phase .count .count dispatch (countDone x y)=
      FiniteCaller.embed subroutine Phase .count .seek dispatch (seekFrame x y 0) := by
  apply cfg_ext
  · rfl
  · rfl
  · change (countDone x y).head=Function.update (countDone x y).head 1 (0+1)
    have h : (countDone x y).head 1=1 := rfl
    rw [Nat.zero_add,←h,Function.update_eq_self]

private theorem after_seek (x y : List Bool) :
    FiniteCaller.returned subroutine Phase .count .seek dispatch (seekDone x y)=
      FiniteCaller.embed subroutine Phase .count .order dispatch (orderIn x y) := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,FiniteCaller.embed,seekDone,seekFrame,
      orderIn,orderView,CanonicalOutput.initialFrame,orderBase,countDone,countView,
      InputWidthCounter.finalFrame,counterWord] <;> rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,FiniteCaller.embed,seekDone,seekFrame,
      orderIn,orderView,CanonicalOutput.initialFrame,orderBase,countDone,countView,
      InputWidthCounter.finalFrame,counterWord,emptyBase,initialFrame,MultitapeTM.initCfg]

private theorem final_handoff (x y : List Bool) :
    FiniteCaller.returned subroutine Phase .count .order dispatch (orderDone x y)=finalFrame x y := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,orderDone,orderView,CanonicalOutput.finalFrame,
      orderBase,countDone,countView,InputWidthCounter.finalFrame,finalFrame,counterWord,
      descriptorWord,emptyBase,initialFrame,MultitapeTM.initCfg,MultitapeTM.inTape] <;> rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,orderDone,orderView,CanonicalOutput.finalFrame,
      orderBase,countDone,countView,InputWidthCounter.finalFrame,finalFrame,counterWord,
      descriptorWord,emptyBase,initialFrame,MultitapeTM.initCfg,MultitapeTM.inTape]

end IntMul.CanonicalWidthDescriptor


namespace IntMul.CanonicalWidthDescriptor
open TapeCopy (Sym)

private theorem owned_intmulcanonicalwidthdescriptorseek_bit_not_blank (b : Bool) : subroutine.bitSym b≠Sym.blank := by cases b <;> decide

private theorem owned_intmulcanonicalwidthdescriptorseek_bits_read (w : List Bool) (j : ℕ) (hj : j< w.length) :
    subroutine.tapeOf (w.map subroutine.bitSym) (j+1)=subroutine.bitSym w[j] := by
  change (w.map subroutine.bitSym).getD j Sym.blank=_
  rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]

private theorem owned_intmulcanonicalwidthdescriptorseek_bits_blank (w : List Bool) :
    subroutine.tapeOf (w.map subroutine.bitSym) (w.length+1)=Sym.blank := by
  change (w.map subroutine.bitSym).getD w.length Sym.blank=Sym.blank
  exact List.getD_eq_default _ _ (by simp)

private theorem seek_step (x y : List Bool) (j : ℕ) (hj : j< (counterWord x y).length) :
    subroutine.step (seekFrame x y j)=seekFrame x y (j+1) := by
  let a : Fin 15 → Sym := fun i => (seekFrame x y j).cells i ((seekFrame x y j).head i)
  have hi : a 1≠Sym.blank := by
    change subroutine.tapeOf ((counterWord x y).map subroutine.bitSym) (j+1)≠Sym.blank
    rw [owned_intmulcanonicalwidthdescriptorseek_bits_read _ _ hj]
    exact owned_intmulcanonicalwidthdescriptorseek_bit_not_blank _
  have ht : transition seekState a=(seekState,fun i => (a i,if i=1 then Move.right else Move.stay)) := by
    simp only [transition,seekState,if_neg hi]
  change transition (seekFrame x y j).state
    (fun i => (seekFrame x y j).cells i ((seekFrame x y j).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [seekFrame,Nat.add_assoc]

private theorem seek_run (x y : List Bool) (j : ℕ) (hj : j≤ (counterWord x y).length) :
    subroutine.step^[j] (seekFrame x y 0)=seekFrame x y j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),seek_step x y j (by omega)]

private theorem seek_halt (x y : List Bool) :
    subroutine.step (seekFrame x y (counterWord x y).length)=seekDone x y := by
  let a : Fin 15 → Sym := fun i => (seekFrame x y (counterWord x y).length).cells i
    ((seekFrame x y (counterWord x y).length).head i)
  have hi : a 1=Sym.blank := owned_intmulcanonicalwidthdescriptorseek_bits_blank (counterWord x y)
  have ht : transition seekState a=(none,fun i => (a i,Move.stay)) := by
    simp only [transition,seekState,if_pos hi]
  change transition (seekFrame x y (counterWord x y).length).state
    (fun i => (seekFrame x y (counterWord x y).length).cells i
      ((seekFrame x y (counterWord x y).length).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];rfl

private theorem seek_complete (x y : List Bool) :
    subroutine.step^[(counterWord x y).length+1] (seekFrame x y 0)=seekDone x y := by
  rw [Function.iterate_succ_apply',seek_run x y _ (by omega),seek_halt]

end IntMul.CanonicalWidthDescriptor


namespace IntMul.CanonicalWidthDescriptor

private theorem owned_intmulcanonicalwidthdescriptornumeric_increment_length (bits : List Bool) :
    (GrowingCounter.increment bits).length≤ bits.length+1 := by
  induction bits with
  | nil => simp [GrowingCounter.increment]
  | cons b bs ih => cases b <;> simp only [GrowingCounter.increment,List.length_cons] <;> omega

private theorem iterate_length (n : ℕ) (bits : List Bool) :
    (GrowingCounter.iterateCounter n bits).length≤ bits.length+n := by
  induction n generalizing bits with
  | zero => simp [GrowingCounter.iterateCounter]
  | succ n ih =>
      have h := ih (GrowingCounter.increment bits)
      have hi := owned_intmulcanonicalwidthdescriptornumeric_increment_length bits
      simp only [GrowingCounter.iterateCounter]
      omega

private theorem owned_intmulcanonicalwidthdescriptornumeric_foldl_affine (x : List Bool) (a : ℕ) :
    x.foldl (fun acc b => 2*acc+b.toNat) a=2^x.length*a+val x := by
  induction x generalizing a with
  | nil => simp [val]
  | cons b xs ih =>
      simp only [List.foldl_cons,List.length_cons]
      rw [ih]
      have hv : val (b::xs)=2^xs.length*b.toNat+val xs := by
        simp only [val,List.foldl_cons,Nat.mul_zero,Nat.zero_add]
        exact ih b.toNat
      rw [hv,pow_succ]
      ring

private theorem owned_intmulcanonicalwidthdescriptornumeric_val_append (x y : List Bool) : val (x++y)=2^y.length*val x+val y := by
  unfold val
  rw [List.foldl_append]
  exact owned_intmulcanonicalwidthdescriptornumeric_foldl_affine y _

private theorem owned_intmulcanonicalwidthdescriptornumeric_val_singleton (b : Bool) : val [b]=b.toNat := by simp [val]

private theorem val_reverse_little (x : List Bool) : val x.reverse=BinaryAdder.littleVal x := by
  induction x with
  | nil => simp [val,BinaryAdder.littleVal]
  | cons b xs ih =>
      rw [List.reverse_cons,owned_intmulcanonicalwidthdescriptornumeric_val_append,owned_intmulcanonicalwidthdescriptornumeric_val_singleton]
      simp only [List.length_singleton,pow_one,ih,BinaryAdder.littleVal]
      ring

private theorem descriptor_value (x y : List Bool) (hp : 0< x.length+y.length) :
    val (descriptorWord x y)+1=x.length+y.length := by
  obtain ⟨t,ht,he,hh,hi,ho,hv⟩ := InputWidthCounter.input_width_counter x y hp
  simpa only [descriptorWord,val_reverse_little] using hv

end IntMul.CanonicalWidthDescriptor


namespace IntMul.CanonicalWidthDescriptor

/-- The actual global execution counts original operand bits, seeks the
counter's real blank, reverses it physically and clears all scratch banks. -/
private theorem descriptor_execution (x y : List Bool) (hp : 0< x.length+y.length) :
    ∃ t : ℕ, t≤ 6*(x.length+y.length)+9*(counterWord x y).length+24 ∧
      machine.step^[t] (initialFrame x y)=finalFrame x y := by
  obtain ⟨a,ha,hea,hha,hinput,houtput,hvalue⟩ := InputWidthCounter.input_width_counter x y hp
  have hcount : subroutine.step^[a]
      (countView (emptyBase x y) (InputWidthCounter.initialFrame x y))=countDone x y := by
    rw [count_run,hea];rfl
  obtain ⟨b,hb,heb⟩ := (FiniteCaller.simulate_run subroutine Phase .count .count dispatch
    (countView (emptyBase x y) (InputWidthCounter.initialFrame x y)) a).2
      (by rw [hcount];rfl)
  rw [hcount,after_count] at heb
  obtain ⟨c,hc,hec⟩ := (FiniteCaller.simulate_run subroutine Phase .count .seek dispatch
    (seekFrame x y 0) ((counterWord x y).length+1)).2 (by rw [seek_complete];rfl)
  rw [seek_complete,after_seek] at hec
  obtain ⟨d,hd,hed,hhd⟩ := CanonicalOutput.canonical_output (orderBase x y) (counterWord x y)
  have horder : subroutine.step^[d] (orderIn x y)=orderDone x y := by
    rw [orderIn,order_run,hed];rfl
  obtain ⟨e,he,hee⟩ := (FiniteCaller.simulate_run subroutine Phase .count .order dispatch
    (orderIn x y) d).2 (by rw [horder];rfl)
  rw [horder,final_handoff] at hee
  refine ⟨e+(c+b),by omega,?_⟩
  rw [Function.iterate_add_apply,Function.iterate_add_apply,initial_handoff,heb,hec,hee]

/-- A complete physically computed big-endian width descriptor, from true
initialization, with retained original input and empty scratch banks. -/
private theorem canonical_width_descriptor (x y : List Bool) (hp : 0< x.length+y.length) :
    ∃ t : ℕ, t≤ 15*(x.length+y.length)+15 ∧
      machine.step^[t] (initialFrame x y)=finalFrame x y ∧
      (machine.step^[t] (initialFrame x y)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame x y)).cells machine.inTape=(initialFrame x y).cells machine.inTape ∧
      (machine.step^[t] (initialFrame x y)).cells machine.outTape=
        machine.tapeOf ((descriptorWord x y).map machine.bitSym) ∧
      val (descriptorWord x y)+1=x.length+y.length := by
  obtain ⟨t,ht,het⟩ := descriptor_execution x y hp
  have hl := iterate_length (x.length+y.length-1) []
  simp only [List.length_nil,Nat.zero_add] at hl
  change (counterWord x y).length≤ x.length+y.length-1 at hl
  refine ⟨t,by omega,het,?_,?_,?_,descriptor_value x y hp⟩
  · rw [het];rfl
  · rw [het]
    simp [finalFrame,initialFrame,MultitapeTM.initCfg,MultitapeTM.inTape]
  · rw [het]
    simp [finalFrame,MultitapeTM.outTape]

end IntMul.CanonicalWidthDescriptor


open IntMul IntMul.CanonicalWidthDescriptor

theorem solution (x y : List Bool) (hp : 0< x.length+y.length) :
    ∃ t : ℕ, t≤ 15*(x.length+y.length)+15 ∧
      machine.step^[t] (initialFrame x y)=finalFrame x y ∧
      (machine.step^[t] (initialFrame x y)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame x y)).cells machine.inTape=(initialFrame x y).cells machine.inTape ∧
      (machine.step^[t] (initialFrame x y)).cells machine.outTape=
        machine.tapeOf ((descriptorWord x y).map machine.bitSym) ∧
      val (descriptorWord x y)+1=x.length+y.length :=
  IntMul.CanonicalWidthDescriptor.canonical_width_descriptor x y hp

#print axioms solution
