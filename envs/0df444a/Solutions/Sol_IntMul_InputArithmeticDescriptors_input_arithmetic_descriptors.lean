-- Prove2me | solution 1 for IntMul.InputArithmeticDescriptors.input_arithmetic_descriptors
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T16:30:29.576976+00:00
-- url     : https://prove2.me/submissions/a663d83b-5d7b-4cd1-9866-f5fc254b066e

import Definitions.Def_IntMul_InputArithmeticDescriptors
import Theorems.Thm_IntMul_InputBlockDescriptors_input_block_descriptors
import Theorems.Thm_IntMul_AffineTriple_affine_descriptor
import Theorems.Thm_IntMul_CanonicalOutput_canonical_output
import Theorems.Thm_IntMul_FiniteCaller_simulate_run
import Mathlib.Tactic

set_option maxHeartbeats 1000000
set_option Elab.async false

set_option maxHeartbeats 1000000
set_option Elab.async false
namespace IntMul.InputArithmeticDescriptors
open TapeCopy (Sym)
private theorem cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c;cases d;cases hs;cases hc;cases hh;rfl

private noncomputable def widthView (base : subroutine.Cfg) (c : InputBlockDescriptors.machine.Cfg) : subroutine.Cfg where
  state := widthState c.state
  cells := fun i => if h : i.val< 17 then c.cells (widthIndex i h) else base.cells i
  head := fun i => if h : i.val< 17 then c.head (widthIndex i h) else base.head i
private theorem width_step (base : subroutine.Cfg) (c : InputBlockDescriptors.machine.Cfg) :
    subroutine.step (widthView base c)=widthView base (InputBlockDescriptors.machine.step c) := by
  let a : Fin 18 → Sym := fun i => (widthView base c).cells i ((widthView base c).head i)
  let b : Fin 17 → Sym := fun j => c.cells j (c.head j)
  have ha : (fun j => a (widthTape j))=b := by funext j;fin_cases j <;> rfl
  have ht : transition (widthState c.state) a=(widthState (InputBlockDescriptors.machine.δ c.state b).1,
      widthAction a (InputBlockDescriptors.machine.δ c.state b).2) := by
    by_cases h : c.state=none
    · rw [h,InputBlockDescriptors.machine.halt_fixed b]
      change (none,fun i => (a i,Move.stay))=(none,widthAction a (fun i => (b i,Move.stay)))
      congr 1;funext i;fin_cases i <;> rfl
    · conv_lhs => rw [widthState,if_neg h]
      change (widthState (InputBlockDescriptors.machine.δ c.state (fun j => a (widthTape j))).1,
        widthAction a (InputBlockDescriptors.machine.δ c.state (fun j => a (widthTape j))).2)=_
      rw [ha]
  change transition (widthView base c).state
    (fun i => (widthView base c).cells i ((widthView base c).head i))=_ at ht
  apply cfg_ext subroutine
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];funext i
    fin_cases i <;> first | rfl | exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];funext i;fin_cases i <;> rfl

private theorem width_run (base : subroutine.Cfg) (c : InputBlockDescriptors.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (widthView base c)=widthView base (InputBlockDescriptors.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,width_step,Function.iterate_succ_apply']

private noncomputable def affineView (base : subroutine.Cfg) (c : AffineTriple.machine.Cfg) : subroutine.Cfg where
  state := affineState c.state
  cells := fun i => if i=16 then c.cells 0 else if i=17 then c.cells 1 else if i=13 then c.cells 2 else base.cells i
  head := fun i => if i=16 then c.head 0 else if i=17 then c.head 1 else if i=13 then c.head 2 else base.head i
private theorem affine_step (base : subroutine.Cfg) (c : AffineTriple.machine.Cfg) :
    subroutine.step (affineView base c)=affineView base (AffineTriple.machine.step c) := by
  let a : Fin 18 → Sym := fun i => (affineView base c).cells i ((affineView base c).head i)
  let b : Fin 3 → Sym := fun j => c.cells j (c.head j)
  have ha : (fun j => a (affineTape j))=b := by funext j;fin_cases j <;> rfl
  have ht : transition (affineState c.state) a=(affineState (AffineTriple.machine.δ c.state b).1,
      affineAction a (AffineTriple.machine.δ c.state b).2) := by
    by_cases h : c.state=AffineTriple.State.halt
    · rw [h,AffineTriple.machine.halt_fixed b]
      change (none,fun i => (a i,Move.stay))=(none,affineAction a (fun i => (b i,Move.stay)))
      congr 1;funext i;fin_cases i <;> rfl
    · conv_lhs => rw [affineState,if_neg h]
      change (affineState (AffineTriple.machine.δ c.state (fun j => a (affineTape j))).1,
        affineAction a (AffineTriple.machine.δ c.state (fun j => a (affineTape j))).2)=_
      rw [ha]
  change transition (affineView base c).state
    (fun i => (affineView base c).cells i ((affineView base c).head i))=_ at ht
  apply cfg_ext subroutine
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];funext i
    fin_cases i <;> first | rfl | exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];funext i;fin_cases i <;> rfl

private theorem affine_run (base : subroutine.Cfg) (c : AffineTriple.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (affineView base c)=affineView base (AffineTriple.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,affine_step,Function.iterate_succ_apply']

private noncomputable def orderView (base : subroutine.Cfg) (c : CanonicalOutput.machine.Cfg) : subroutine.Cfg where
  state := orderState c.state
  cells := fun i => if i=17 then c.cells 1 else if i=1 then base.cells i else if h : i.val< 15 then c.cells (orderIndex i h) else base.cells i
  head := fun i => if i=17 then c.head 1 else if i=1 then base.head i else if h : i.val< 15 then c.head (orderIndex i h) else base.head i
private theorem order_step (base : subroutine.Cfg) (c : CanonicalOutput.machine.Cfg) :
    subroutine.step (orderView base c)=orderView base (CanonicalOutput.machine.step c) := by
  let a : Fin 18 → Sym := fun i => (orderView base c).cells i ((orderView base c).head i)
  let b : Fin 15 → Sym := fun j => c.cells j (c.head j)
  have ha : (fun j => a (orderTape j))=b := by funext j;fin_cases j <;> rfl
  have ht : transition (orderState c.state) a=(orderState (CanonicalOutput.machine.δ c.state b).1,
      orderAction a (CanonicalOutput.machine.δ c.state b).2) := by
    by_cases h : c.state=none
    · rw [h,CanonicalOutput.machine.halt_fixed b]
      change (none,fun i => (a i,Move.stay))=(none,orderAction a (fun i => (b i,Move.stay)))
      congr 1;funext i;fin_cases i <;> rfl
    · conv_lhs => rw [orderState,if_neg h]
      change (orderState (CanonicalOutput.machine.δ c.state (fun j => a (orderTape j))).1,
        orderAction a (CanonicalOutput.machine.δ c.state (fun j => a (orderTape j))).2)=_
      rw [ha]
  change transition (orderView base c).state
    (fun i => (orderView base c).cells i ((orderView base c).head i))=_ at ht
  apply cfg_ext subroutine
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];funext i
    fin_cases i <;> first | rfl | exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];funext i;fin_cases i <;> rfl

private theorem order_run (base : subroutine.Cfg) (c : CanonicalOutput.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (orderView base c)=orderView base (CanonicalOutput.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,order_step,Function.iterate_succ_apply']
end IntMul.InputArithmeticDescriptors

namespace IntMul.InputArithmeticDescriptors
open TapeCopy (Sym)
private noncomputable def emptyBase (x y : List Bool) : subroutine.Cfg where
  state := none
  cells := (initialFrame x y).cells
  head := (initialFrame x y).head
private noncomputable def widthDone (x y : List Bool) : subroutine.Cfg :=
  widthView (emptyBase x y) (InputBlockDescriptors.finalFrame x y)
private noncomputable def affineIn (x y : List Bool) : subroutine.Cfg :=
  affineView (widthDone x y) (AffineTriple.initialFrame (blockWord x y))
private noncomputable def affineDone (x y : List Bool) : subroutine.Cfg :=
  affineView (widthDone x y) (AffineTriple.finalFrame (blockWord x y))
private noncomputable def orderBase (x y : List Bool) : CanonicalOutput.machine.Cfg where
  state := none
  cells := fun j => (affineDone x y).cells (orderTape j)
  head := fun j => (affineDone x y).head (orderTape j)
private noncomputable def orderIn (x y : List Bool) : subroutine.Cfg :=
  orderView (affineDone x y) (CanonicalOutput.initialFrame (orderBase x y) (littlePrecision x y))
private noncomputable def orderDone (x y : List Bool) : subroutine.Cfg :=
  orderView (affineDone x y) (CanonicalOutput.finalFrame (orderBase x y) (littlePrecision x y))
private noncomputable def rewindFrame (x y : List Bool) (p : ℕ) : subroutine.Cfg :=
  {orderDone x y with
    state := relayState
    head := Function.update (orderDone x y).head 17 p}
private noncomputable def rewindDone (x y : List Bool) : subroutine.Cfg :=
  {rewindFrame x y 0 with state := none}

private theorem initial_handoff (x y : List Bool) :
    initialFrame x y=FiniteCaller.embed subroutine Phase .width .width dispatch
      (widthView (emptyBase x y) (InputBlockDescriptors.initialFrame x y)) := by
  apply cfg_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl

private theorem after_width (x y : List Bool) :
    FiniteCaller.returned subroutine Phase .width .width dispatch (widthDone x y)=
      FiniteCaller.embed subroutine Phase .width .affine dispatch (affineIn x y) := by
  apply cfg_ext
  · rfl
  · funext i;fin_cases i <;> simp [FiniteCaller.returned,FiniteCaller.embed,affineIn,affineView,
      AffineTriple.initialFrame,widthDone,widthView,widthIndex,InputBlockDescriptors.finalFrame,
      blockWord,emptyBase,initialFrame,MultitapeTM.initCfg,MultitapeTM.inTape] <;> rfl
  · funext i;fin_cases i <;> simp [FiniteCaller.returned,FiniteCaller.embed,affineIn,affineView,
      AffineTriple.initialFrame,widthDone,widthView,widthIndex,InputBlockDescriptors.finalFrame,
      blockWord,emptyBase,initialFrame,MultitapeTM.initCfg]

private theorem after_affine (x y : List Bool) :
    FiniteCaller.returned subroutine Phase .width .affine dispatch (affineDone x y)=
      FiniteCaller.embed subroutine Phase .width .order dispatch (orderIn x y) := by
  apply cfg_ext
  · rfl
  · funext i;fin_cases i <;> simp [FiniteCaller.returned,FiniteCaller.embed,orderIn,orderView,
      orderIndex,CanonicalOutput.initialFrame,orderBase,orderTape,littlePrecision,
      affineDone,affineView,AffineTriple.finalFrame,widthDone,widthView,widthIndex,
      InputBlockDescriptors.finalFrame] <;> rfl
  · funext i;fin_cases i <;> simp [FiniteCaller.returned,FiniteCaller.embed,orderIn,orderView,
      orderIndex,CanonicalOutput.initialFrame,orderBase,orderTape,littlePrecision,
      affineDone,affineView,AffineTriple.finalFrame,widthDone,widthView,widthIndex,
      InputBlockDescriptors.finalFrame]

private theorem after_order (x y : List Bool) :
    FiniteCaller.returned subroutine Phase .width .order dispatch (orderDone x y)=
      FiniteCaller.embed subroutine Phase .width .rewind dispatch
        (rewindFrame x y ((precisionWord x y).length+1)) := by
  have hp : (orderDone x y).head 17=(precisionWord x y).length+1 := by
    simp [orderDone,orderView,CanonicalOutput.finalFrame,precisionWord]
  apply cfg_ext
  · rfl
  · rfl
  · funext i;fin_cases i <;> simp [FiniteCaller.returned,FiniteCaller.embed,rewindFrame,hp]

private theorem final_handoff (x y : List Bool) :
    FiniteCaller.returned subroutine Phase .width .rewind dispatch (rewindDone x y)=finalFrame x y := by
  apply cfg_ext
  · rfl
  · funext i;fin_cases i <;> simp [FiniteCaller.returned,rewindDone,rewindFrame,orderDone,orderView,
      orderIndex,CanonicalOutput.finalFrame,orderBase,orderTape,affineDone,affineView,
      AffineTriple.finalFrame,widthDone,widthView,widthIndex,InputBlockDescriptors.finalFrame,
      finalFrame,widthWord,blockWord,precisionWord,littlePrecision,emptyBase,initialFrame,
      MultitapeTM.initCfg,MultitapeTM.inTape] <;> rfl
  · funext i;fin_cases i <;> simp [FiniteCaller.returned,rewindDone,rewindFrame,orderDone,orderView,
      orderIndex,CanonicalOutput.finalFrame,orderBase,orderTape,affineDone,affineView,
      AffineTriple.finalFrame,widthDone,widthView,widthIndex,InputBlockDescriptors.finalFrame,
      finalFrame,widthWord,blockWord,precisionWord,littlePrecision,emptyBase,initialFrame,
      MultitapeTM.initCfg]
end IntMul.InputArithmeticDescriptors

namespace IntMul.InputArithmeticDescriptors
open TapeCopy (Sym)

private theorem owned_intmulinputarithmeticdescriptorsrewind_bits_not_start (w : List Bool) (j : ℕ) :
    subroutine.tapeOf (w.map subroutine.bitSym) (j+1)≠Sym.start := by
  change (w.map subroutine.bitSym).getD j Sym.blank≠Sym.start
  by_cases h : j< (w.map subroutine.bitSym).length
  · rw [List.getD_eq_getElem _ _ h,List.getElem_map]
    have hj : j< w.length := by simpa only [List.length_map] using h
    cases w[j] <;> decide
  · rw [List.getD_eq_default _ _ (by omega)];decide
private theorem owned_intmulinputarithmeticdescriptorsrewind_bits_start_iff (w : List Bool) (p : ℕ) :
    subroutine.tapeOf (w.map subroutine.bitSym) p=Sym.start ↔ p=0 := by
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p => simp [owned_intmulinputarithmeticdescriptorsrewind_bits_not_start w p]

private theorem rewind_step (x y : List Bool) (p : ℕ) :
    subroutine.step (rewindFrame x y (p+1))=rewindFrame x y p := by
  let a : Fin 18 → Sym := fun i => (rewindFrame x y (p+1)).cells i ((rewindFrame x y (p+1)).head i)
  have hn : a 17≠Sym.start := owned_intmulinputarithmeticdescriptorsrewind_bits_not_start (precisionWord x y) p
  have ht : transition relayState a=(relayState,fun i => (a i,if i=17 then Move.left else Move.stay)) := by
    change (if a 17=Sym.start then (none,fun i => (a i,Move.stay))
      else (relayState,fun i => (a i,if i=17 then Move.left else Move.stay)))=_
    rw [if_neg hn]
  change transition (rewindFrame x y (p+1)).state
    (fun i => (rewindFrame x y (p+1)).cells i ((rewindFrame x y (p+1)).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];funext i;fin_cases i <;> simp [rewindFrame]

private theorem rewind_halt (x y : List Bool) :
    subroutine.step (rewindFrame x y 0)=rewindDone x y := by
  let a : Fin 18 → Sym := fun i => (rewindFrame x y 0).cells i ((rewindFrame x y 0).head i)
  have hi : a 17=Sym.start := rfl
  have ht : transition relayState a=(none,fun i => (a i,Move.stay)) := by
    change (if a 17=Sym.start then (none,fun i => (a i,Move.stay))
      else (relayState,fun i => (a i,if i=17 then Move.left else Move.stay)))=_
    rw [if_pos hi]
  change transition (rewindFrame x y 0).state
    (fun i => (rewindFrame x y 0).cells i ((rewindFrame x y 0).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];rfl

private theorem rewind_complete (x y : List Bool) (p : ℕ) :
    subroutine.step^[p+1] (rewindFrame x y p)=rewindDone x y := by
  induction p with
  | zero => rw [Function.iterate_one,rewind_halt]
  | succ p ih => rw [Function.iterate_succ_apply,rewind_step,ih]
end IntMul.InputArithmeticDescriptors

namespace IntMul.InputArithmeticDescriptors
private theorem owned_intmulinputarithmeticdescriptorsnumeric_foldl_affine (x : List Bool) (a : ℕ) :
    x.foldl (fun acc b => 2*acc+b.toNat) a=2^x.length*a+val x := by
  induction x generalizing a with
  | nil => simp [val]
  | cons b xs ih =>
      simp only [List.foldl_cons,List.length_cons];rw [ih]
      have hv : val (b::xs)=2^xs.length*b.toNat+val xs := by
        simp only [val,List.foldl_cons,Nat.mul_zero,Nat.zero_add];exact ih b.toNat
      rw [hv,pow_succ];ring
private theorem owned_intmulinputarithmeticdescriptorsnumeric_val_append (x y : List Bool) : val (x++y)=2^y.length*val x+val y := by
  unfold val;rw [List.foldl_append];exact owned_intmulinputarithmeticdescriptorsnumeric_foldl_affine y _
private theorem owned_intmulinputarithmeticdescriptorsnumeric_val_singleton (b : Bool) : val [b]=b.toNat := by simp [val]
private theorem val_reverse_little (x : List Bool) : val x.reverse=BinaryAdder.littleVal x := by
  induction x with
  | nil => simp [val,BinaryAdder.littleVal]
  | cons b xs ih =>
      rw [List.reverse_cons,owned_intmulinputarithmeticdescriptorsnumeric_val_append,owned_intmulinputarithmeticdescriptorsnumeric_val_singleton]
      simp only [List.length_singleton,pow_one,ih,BinaryAdder.littleVal];ring


private theorem descriptor_facts (x y : List Bool) (hp : 0< x.length+y.length) :
    val (widthWord x y)+1=x.length+y.length ∧
    val (blockWord x y)+1=lg (x.length+y.length) ∧
    val (precisionWord x y)+1=3*lg (x.length+y.length) ∧
    (widthWord x y).length=Nat.clog 2 (x.length+y.length) ∧
    (blockWord x y).length=Nat.clog 2 (lg (x.length+y.length)) ∧
    (precisionWord x y).length≤ Nat.clog 2 (lg (x.length+y.length))+2 := by
  obtain ⟨a,ha,he,hh,hi,ho,hd,hb,hdl,hbl⟩ := InputBlockDescriptors.input_block_descriptors x y hp
  obtain ⟨b,hbtime,hbe,hvalue,hlen⟩ := AffineTriple.affine_descriptor (blockWord x y)
  change val (widthWord x y)+1=x.length+y.length at hd
  change val (blockWord x y)+1=lg (x.length+y.length) at hb
  change (widthWord x y).length=Nat.clog 2 (x.length+y.length) at hdl
  change (blockWord x y).length=Nat.clog 2 (lg (x.length+y.length)) at hbl
  change (littlePrecision x y).length≤ (blockWord x y).length+2 at hlen
  have hv : val (precisionWord x y)=3*val (blockWord x y)+2 := by
    rw [precisionWord,val_reverse_little];exact hvalue
  refine ⟨hd,hb,?_,hdl,hbl,?_⟩
  · omega
  · simp only [precisionWord,List.length_reverse]
    simpa only [hbl] using hlen
private theorem owned_intmulinputarithmeticdescriptorsnumeric_clog_le_self (W : ℕ) : Nat.clog 2 W≤ W :=
  Nat.clog_le_of_le_pow (Nat.le_of_lt W.lt_two_pow_self)

private theorem parameter_sizes (x y : List Bool) (hp : 0< x.length+y.length) :
    Nat.clog 2 (x.length+y.length)≤ x.length+y.length ∧
    Nat.clog 2 (lg (x.length+y.length))≤ x.length+y.length ∧
    (blockWord x y).length≤ lg (x.length+y.length) ∧
    (precisionWord x y).length≤ 3*lg (x.length+y.length) := by
  obtain ⟨hd,hb,hn,hdl,hbl,hnl⟩ := descriptor_facts x y hp
  have hclog := owned_intmulinputarithmeticdescriptorsnumeric_clog_le_self (x.length+y.length)
  have hB : lg (x.length+y.length)≤ x.length+y.length := max_le hclog (by omega)
  have hclogB := owned_intmulinputarithmeticdescriptorsnumeric_clog_le_self (lg (x.length+y.length))
  have hpositive : 1≤ lg (x.length+y.length) := Nat.le_max_right _ _
  refine ⟨hclog,hclogB.trans hB,?_,?_⟩
  · rw [hbl];exact hclogB
  · omega

end IntMul.InputArithmeticDescriptors

namespace IntMul.InputArithmeticDescriptors

private theorem owned_intmulinputarithmeticdescriptorsprimary_descriptor_execution (x y : List Bool) (hp : 0< x.length+y.length) :
    ∃ t : ℕ, t≤ 18*(x.length+y.length)+7*(widthWord x y).length+
        12*(blockWord x y).length+9*(precisionWord x y).length+76 ∧
      machine.step^[t] (initialFrame x y)=finalFrame x y := by
  obtain ⟨a,ha,hea,hha,hinput,houtput,hvalue,hblock,hwidthlen,hblocklen⟩ :=
    InputBlockDescriptors.input_block_descriptors x y hp
  have hwidth : subroutine.step^[a]
      (widthView (emptyBase x y) (InputBlockDescriptors.initialFrame x y))=widthDone x y := by
    rw [width_run,hea];rfl
  obtain ⟨b,hb,heb⟩ := (FiniteCaller.simulate_run subroutine Phase .width .width dispatch
    (widthView (emptyBase x y) (InputBlockDescriptors.initialFrame x y)) a).2 (by rw [hwidth];rfl)
  rw [hwidth,after_width] at heb
  obtain ⟨c,hc,hec,hcvalue,hclen⟩ := AffineTriple.affine_descriptor (blockWord x y)
  have haffine : subroutine.step^[c] (affineIn x y)=affineDone x y := by
    rw [affineIn,affine_run,hec];rfl
  obtain ⟨d,hd,hed⟩ := (FiniteCaller.simulate_run subroutine Phase .width .affine dispatch
    (affineIn x y) c).2 (by rw [haffine];rfl)
  rw [haffine,after_affine] at hed
  obtain ⟨e,he,hee,hhe⟩ := CanonicalOutput.canonical_output (orderBase x y) (littlePrecision x y)
  have horder : subroutine.step^[e] (orderIn x y)=orderDone x y := by
    rw [orderIn,order_run,hee];rfl
  obtain ⟨f,hf,hef⟩ := (FiniteCaller.simulate_run subroutine Phase .width .order dispatch
    (orderIn x y) e).2 (by rw [horder];rfl)
  rw [horder,after_order] at hef
  have hrewind := rewind_complete x y ((precisionWord x y).length+1)
  obtain ⟨g,hg,heg⟩ := (FiniteCaller.simulate_run subroutine Phase .width .rewind dispatch
    (rewindFrame x y ((precisionWord x y).length+1)) (((precisionWord x y).length+1)+1)).2
      (by rw [hrewind];rfl)
  rw [hrewind,final_handoff] at heg
  have hlen : (littlePrecision x y).length=(precisionWord x y).length := by simp [precisionWord]
  have hw : 18*(x.length+y.length)+7*Nat.clog 2 (x.length+y.length)+
      10*Nat.clog 2 (lg (x.length+y.length))+50=
      18*(x.length+y.length)+7*(widthWord x y).length+10*(blockWord x y).length+50 := by
    rw [widthWord,blockWord,hwidthlen,hblocklen]
  rw [hw] at ha
  rw [hlen] at he
  refine ⟨g+(f+(d+b)),by omega,?_⟩
  rw [Function.iterate_add_apply,Function.iterate_add_apply,Function.iterate_add_apply,
    initial_handoff,heb,hed,hef,heg]

private theorem input_arithmetic_descriptors (x y : List Bool) (hp : 0< x.length+y.length) :
    ∃ t : ℕ, t≤ 18*(x.length+y.length)+7*Nat.clog 2 (x.length+y.length)+
        21*Nat.clog 2 (lg (x.length+y.length))+94 ∧
      t≤ 46*(x.length+y.length)+94 ∧
      machine.step^[t] (initialFrame x y)=finalFrame x y ∧
      (machine.step^[t] (initialFrame x y)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame x y)).cells machine.inTape=(initialFrame x y).cells machine.inTape ∧
      (machine.step^[t] (initialFrame x y)).cells machine.outTape=machine.tapeOf [] ∧
      val (widthWord x y)+1=x.length+y.length ∧
      val (blockWord x y)+1=lg (x.length+y.length) ∧
      val (precisionWord x y)+1=3*lg (x.length+y.length) ∧
      (widthWord x y).length=Nat.clog 2 (x.length+y.length) ∧
      (blockWord x y).length=Nat.clog 2 (lg (x.length+y.length)) ∧
      (precisionWord x y).length≤ Nat.clog 2 (lg (x.length+y.length))+2 ∧
      (blockWord x y).length≤ lg (x.length+y.length) ∧
      (precisionWord x y).length≤ 3*lg (x.length+y.length) := by
  obtain ⟨t,ht,he⟩ := owned_intmulinputarithmeticdescriptorsprimary_descriptor_execution x y hp
  obtain ⟨hwidth,hblock,hprecision,hlwidth,hlblock,hlprecision⟩ := descriptor_facts x y hp
  obtain ⟨hlogW,hlogB,hz,hl⟩ := parameter_sizes x y hp
  refine ⟨t,by omega,by omega,he,?_,?_,?_,hwidth,hblock,hprecision,hlwidth,hlblock,hlprecision,hz,hl⟩
  · rw [he];rfl
  · rw [he];simp [finalFrame,initialFrame,MultitapeTM.initCfg,MultitapeTM.inTape]
  · rw [he];simp [finalFrame,MultitapeTM.outTape]
end IntMul.InputArithmeticDescriptors


open IntMul IntMul.InputArithmeticDescriptors

theorem solution (x y : List Bool) (hp : 0< x.length+y.length) :
    ∃ t : ℕ, t≤ 18*(x.length+y.length)+7*Nat.clog 2 (x.length+y.length)+
        21*Nat.clog 2 (lg (x.length+y.length))+94 ∧
      t≤ 46*(x.length+y.length)+94 ∧
      machine.step^[t] (initialFrame x y)=finalFrame x y ∧
      (machine.step^[t] (initialFrame x y)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame x y)).cells machine.inTape=(initialFrame x y).cells machine.inTape ∧
      (machine.step^[t] (initialFrame x y)).cells machine.outTape=machine.tapeOf [] ∧
      val (widthWord x y)+1=x.length+y.length ∧
      val (blockWord x y)+1=lg (x.length+y.length) ∧
      val (precisionWord x y)+1=3*lg (x.length+y.length) ∧
      (widthWord x y).length=Nat.clog 2 (x.length+y.length) ∧
      (blockWord x y).length=Nat.clog 2 (lg (x.length+y.length)) ∧
      (precisionWord x y).length≤ Nat.clog 2 (lg (x.length+y.length))+2 ∧
      (blockWord x y).length≤ lg (x.length+y.length) ∧
      (precisionWord x y).length≤ 3*lg (x.length+y.length) :=
  IntMul.InputArithmeticDescriptors.input_arithmetic_descriptors x y hp

#print axioms solution
