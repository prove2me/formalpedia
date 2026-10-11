-- Prove2me | solution 1 for IntMul.InputBlockDescriptors.input_block_descriptors
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T16:16:19.166963+00:00
-- url     : https://prove2.me/submissions/7548e5d1-ff35-4e59-88eb-8be9ac826235

import Definitions.Def_IntMul_InputBlockDescriptors
import Mathlib.Tactic
import Theorems.Thm_IntMul_FiniteCaller_simulate_run
import Theorems.Thm_IntMul_InputWidthPreparation_input_width_preparation
import Theorems.Thm_IntMul_WordWidthCounter_count_word_width
import Theorems.Thm_IntMul_CanonicalOutput_canonical_output
import Theorems.Thm_IntMul_GrowingCounter_counter_width_logarithmic
import Theorems.Thm_IntMul_CanonicalWidthDescriptor_canonical_width_descriptor

set_option maxHeartbeats 1000000
set_option Elab.async false

set_option maxHeartbeats 1000000
set_option Elab.async false
namespace IntMul.InputBlockDescriptors
open TapeCopy (Sym)
private theorem cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c;cases d;cases hs;cases hc;cases hh;rfl

private noncomputable def widthView (base : subroutine.Cfg) (c : InputWidthPreparation.machine.Cfg) : subroutine.Cfg where
  state := widthState c.state
  cells := fun i => if h : i.val< 16 then c.cells (widthIndex i h) else base.cells i
  head := fun i => if h : i.val< 16 then c.head (widthIndex i h) else base.head i
private theorem width_step (base : subroutine.Cfg) (c : InputWidthPreparation.machine.Cfg) :
    subroutine.step (widthView base c)=widthView base (InputWidthPreparation.machine.step c) := by
  let a : Fin 17 → Sym := fun i => (widthView base c).cells i ((widthView base c).head i)
  let b : Fin 16 → Sym := fun j => c.cells j (c.head j)
  have ha : (fun j => a (widthTape j))=b := by funext j;fin_cases j <;> rfl
  have ht : transition (widthState c.state) a=(widthState (InputWidthPreparation.machine.δ c.state b).1,
      widthAction a (InputWidthPreparation.machine.δ c.state b).2) := by
    by_cases h : c.state=none
    · rw [h,InputWidthPreparation.machine.halt_fixed b]
      change (none,fun i => (a i,Move.stay))=(none,widthAction a (fun i => (b i,Move.stay)))
      congr 1;funext i;fin_cases i <;> rfl
    · conv_lhs => rw [widthState,if_neg h]
      change (widthState (InputWidthPreparation.machine.δ c.state (fun j => a (widthTape j))).1,
        widthAction a (InputWidthPreparation.machine.δ c.state (fun j => a (widthTape j))).2)=_
      rw [ha]
  change transition (widthView base c).state
    (fun i => (widthView base c).cells i ((widthView base c).head i))=_ at ht
  apply cfg_ext subroutine
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> first | rfl | exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> rfl

private theorem width_run (base : subroutine.Cfg) (c : InputWidthPreparation.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (widthView base c)=widthView base (InputWidthPreparation.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,width_step,Function.iterate_succ_apply']

private noncomputable def wordView (base : subroutine.Cfg) (c : WordWidthCounter.machine.Cfg) : subroutine.Cfg where
  state := wordState c.state
  cells := fun i => if i=15 then c.cells 0 else if i=13 then c.cells 1 else if i=16 then c.cells 2 else base.cells i
  head := fun i => if i=15 then c.head 0 else if i=13 then c.head 1 else if i=16 then c.head 2 else base.head i
private theorem word_step (base : subroutine.Cfg) (c : WordWidthCounter.machine.Cfg) :
    subroutine.step (wordView base c)=wordView base (WordWidthCounter.machine.step c) := by
  let a : Fin 17 → Sym := fun i => (wordView base c).cells i ((wordView base c).head i)
  let b : Fin 3 → Sym := fun j => c.cells j (c.head j)
  have ha : (fun j => a (wordTape j))=b := by funext j;fin_cases j <;> rfl
  have ht : transition (wordState c.state) a=(wordState (WordWidthCounter.machine.δ c.state b).1,
      wordAction a (WordWidthCounter.machine.δ c.state b).2) := by
    by_cases h : c.state=none
    · rw [h,WordWidthCounter.machine.halt_fixed b]
      change (none,fun i => (a i,Move.stay))=(none,wordAction a (fun i => (b i,Move.stay)))
      congr 1;funext i;fin_cases i <;> rfl
    · conv_lhs => rw [wordState,if_neg h]
      change (wordState (WordWidthCounter.machine.δ c.state (fun j => a (wordTape j))).1,
        wordAction a (WordWidthCounter.machine.δ c.state (fun j => a (wordTape j))).2)=_
      rw [ha]
  change transition (wordView base c).state
    (fun i => (wordView base c).cells i ((wordView base c).head i))=_ at ht
  apply cfg_ext subroutine
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> first | rfl | exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> rfl

private theorem word_run (base : subroutine.Cfg) (c : WordWidthCounter.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (wordView base c)=wordView base (WordWidthCounter.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,word_step,Function.iterate_succ_apply']

private noncomputable def orderView (base : subroutine.Cfg) (c : CanonicalOutput.machine.Cfg) : subroutine.Cfg where
  state := orderState c.state
  cells := fun i => if i=16 then c.cells 1 else if i=1 then base.cells i else if h : i.val< 15 then c.cells (orderIndex i h) else base.cells i
  head := fun i => if i=16 then c.head 1 else if i=1 then base.head i else if h : i.val< 15 then c.head (orderIndex i h) else base.head i
private theorem order_step (base : subroutine.Cfg) (c : CanonicalOutput.machine.Cfg) :
    subroutine.step (orderView base c)=orderView base (CanonicalOutput.machine.step c) := by
  let a : Fin 17 → Sym := fun i => (orderView base c).cells i ((orderView base c).head i)
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
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> first | rfl | exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> rfl

private theorem order_run (base : subroutine.Cfg) (c : CanonicalOutput.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (orderView base c)=orderView base (CanonicalOutput.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,order_step,Function.iterate_succ_apply']
end IntMul.InputBlockDescriptors

namespace IntMul.InputBlockDescriptors
open TapeCopy (Sym)

private noncomputable def emptyBase (x y : List Bool) : subroutine.Cfg where
  state := none
  cells := (initialFrame x y).cells
  head := (initialFrame x y).head
private noncomputable def widthDone (x y : List Bool) : subroutine.Cfg :=
  widthView (emptyBase x y) (InputWidthPreparation.finalFrame x y)
private noncomputable def wordIn (x y : List Bool) : subroutine.Cfg :=
  wordView (widthDone x y) (WordWidthCounter.initialFrame (widthWord x y))
private noncomputable def wordDone (x y : List Bool) : subroutine.Cfg :=
  wordView (widthDone x y) (WordWidthCounter.finalFrame (widthWord x y))
private def littleBlock (x y : List Bool) := WordWidthCounter.counterWord (widthWord x y)
private noncomputable def seekFrame (x y : List Bool) (j : ℕ) : subroutine.Cfg :=
  {wordDone x y with state := relayState .seek,head := Function.update (wordDone x y).head 16 (j+1)}
private noncomputable def seekDone (x y : List Bool) : subroutine.Cfg :=
  {seekFrame x y (littleBlock x y).length with state := none}
private noncomputable def orderBase (x y : List Bool) : CanonicalOutput.machine.Cfg where
  state := none
  cells := fun j => (wordDone x y).cells (orderTape j)
  head := fun j => (wordDone x y).head (orderTape j)
private noncomputable def orderIn (x y : List Bool) : subroutine.Cfg :=
  orderView (wordDone x y) (CanonicalOutput.initialFrame (orderBase x y) (littleBlock x y))
private noncomputable def orderDone (x y : List Bool) : subroutine.Cfg :=
  orderView (wordDone x y) (CanonicalOutput.finalFrame (orderBase x y) (littleBlock x y))
private noncomputable def rewindFrame (x y : List Bool) (p q : ℕ) : subroutine.Cfg :=
  {orderDone x y with
    state := relayState .rewind
    head := Function.update (Function.update (orderDone x y).head 15 p) 16 q}
private noncomputable def rewindDone (x y : List Bool) : subroutine.Cfg :=
  {rewindFrame x y 0 0 with state := none}

private theorem initial_handoff (x y : List Bool) :
    initialFrame x y=FiniteCaller.embed subroutine Phase .width .width dispatch
      (widthView (emptyBase x y) (InputWidthPreparation.initialFrame x y)) := by
  apply cfg_ext machine
  · rfl
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl

private theorem after_width (x y : List Bool) :
    FiniteCaller.returned subroutine Phase .width .width dispatch (widthDone x y)=
      FiniteCaller.embed subroutine Phase .width .word dispatch (wordIn x y) := by
  apply cfg_ext machine
  · rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,FiniteCaller.embed,wordIn,wordView,
      WordWidthCounter.initialFrame,widthDone,widthView,widthIndex,InputWidthPreparation.finalFrame,
      widthWord,emptyBase,initialFrame,MultitapeTM.initCfg,MultitapeTM.inTape] <;> rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,FiniteCaller.embed,wordIn,wordView,
      WordWidthCounter.initialFrame,widthDone,widthView,widthIndex,InputWidthPreparation.finalFrame,
      widthWord,emptyBase,initialFrame,MultitapeTM.initCfg]

private theorem after_word (x y : List Bool) :
    FiniteCaller.returned subroutine Phase .width .word dispatch (wordDone x y)=
      FiniteCaller.embed subroutine Phase .width .seek dispatch (seekFrame x y 0) := by
  apply cfg_ext machine
  · rfl
  · rfl
  · have h : (wordDone x y).head 16=1 := rfl
    change (wordDone x y).head=Function.update (wordDone x y).head 16 (0+1)
    rw [Nat.zero_add,←h,Function.update_eq_self]

private theorem after_seek (x y : List Bool) :
    FiniteCaller.returned subroutine Phase .width .seek dispatch (seekDone x y)=
      FiniteCaller.embed subroutine Phase .width .order dispatch (orderIn x y) := by
  apply cfg_ext machine
  · rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,FiniteCaller.embed,seekDone,seekFrame,orderIn,
      orderView,orderIndex,CanonicalOutput.initialFrame,orderBase,orderTape,littleBlock,
      wordDone,wordView,WordWidthCounter.finalFrame,widthDone,widthView,widthIndex,
      InputWidthPreparation.finalFrame] <;> rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,FiniteCaller.embed,seekDone,seekFrame,orderIn,
      orderView,orderIndex,CanonicalOutput.initialFrame,orderBase,orderTape,littleBlock,
      wordDone,wordView,WordWidthCounter.finalFrame,widthDone,widthView,widthIndex,
      InputWidthPreparation.finalFrame]

private theorem after_order (x y : List Bool) :
    FiniteCaller.returned subroutine Phase .width .order dispatch (orderDone x y)=
      FiniteCaller.embed subroutine Phase .width .rewind dispatch
        (rewindFrame x y ((widthWord x y).length+1) ((blockWord x y).length+1)) := by
  have hp : (orderDone x y).head 15=(widthWord x y).length+1 := rfl
  have hq : (orderDone x y).head 16=(blockWord x y).length+1 := by
    simp [orderDone,orderView,CanonicalOutput.finalFrame,blockWord,littleBlock]
  apply cfg_ext machine
  · rfl
  · rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,FiniteCaller.embed,rewindFrame,hp,hq]

private theorem final_handoff (x y : List Bool) :
    FiniteCaller.returned subroutine Phase .width .rewind dispatch (rewindDone x y)=finalFrame x y := by
  apply cfg_ext machine
  · rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,rewindDone,rewindFrame,orderDone,orderView,
      orderIndex,CanonicalOutput.finalFrame,orderBase,orderTape,wordDone,wordView,
      WordWidthCounter.finalFrame,widthDone,widthView,widthIndex,InputWidthPreparation.finalFrame,
      finalFrame,widthWord,blockWord,littleBlock,emptyBase,initialFrame,MultitapeTM.initCfg,
      MultitapeTM.inTape] <;> rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,rewindDone,rewindFrame,orderDone,orderView,
      orderIndex,CanonicalOutput.finalFrame,orderBase,orderTape,wordDone,wordView,
      WordWidthCounter.finalFrame,widthDone,widthView,widthIndex,InputWidthPreparation.finalFrame,
      finalFrame,widthWord,blockWord,littleBlock,emptyBase,initialFrame,MultitapeTM.initCfg]

end IntMul.InputBlockDescriptors

namespace IntMul.InputBlockDescriptors
open TapeCopy (Sym)
private theorem owned_intmulinputblockdescriptorsseek_bit_not_blank (b : Bool) : subroutine.bitSym b≠Sym.blank := by cases b <;> decide
private theorem owned_intmulinputblockdescriptorsseek_bits_read (w : List Bool) (j : ℕ) (hj : j< w.length) :
    subroutine.tapeOf (w.map subroutine.bitSym) (j+1)=subroutine.bitSym w[j] := by
  change (w.map subroutine.bitSym).getD j Sym.blank=_
  rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]
private theorem owned_intmulinputblockdescriptorsseek_bits_blank (w : List Bool) :
    subroutine.tapeOf (w.map subroutine.bitSym) (w.length+1)=Sym.blank := by
  change (w.map subroutine.bitSym).getD w.length Sym.blank=Sym.blank
  exact List.getD_eq_default _ _ (by simp)

private theorem seek_step (x y : List Bool) (j : ℕ) (hj : j< (littleBlock x y).length) :
    subroutine.step (seekFrame x y j)=seekFrame x y (j+1) := by
  let a : Fin 17 → Sym := fun i => (seekFrame x y j).cells i ((seekFrame x y j).head i)
  have hi : a 16≠Sym.blank := by
    change subroutine.tapeOf ((littleBlock x y).map subroutine.bitSym) (j+1)≠Sym.blank
    rw [owned_intmulinputblockdescriptorsseek_bits_read _ _ hj]
    exact owned_intmulinputblockdescriptorsseek_bit_not_blank _
  have ht : transition (relayState .seek) a=(relayState .seek,fun i => (a i,if i=16 then Move.right else Move.stay)) := by
    change (if a 16=Sym.blank then (none,fun i => (a i,Move.stay))
      else (relayState .seek,fun i => (a i,if i=16 then Move.right else Move.stay)))=_
    rw [if_neg hi]
  change transition (seekFrame x y j).state (fun i => (seekFrame x y j).cells i ((seekFrame x y j).head i))=_ at ht
  apply cfg_ext subroutine
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];funext i;fin_cases i <;> simp [seekFrame,Nat.add_assoc]

private theorem seek_run (x y : List Bool) (j : ℕ) (hj : j≤ (littleBlock x y).length) :
    subroutine.step^[j] (seekFrame x y 0)=seekFrame x y j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),seek_step x y j (by omega)]

private theorem seek_halt (x y : List Bool) :
    subroutine.step (seekFrame x y (littleBlock x y).length)=seekDone x y := by
  let a : Fin 17 → Sym := fun i => (seekFrame x y (littleBlock x y).length).cells i
    ((seekFrame x y (littleBlock x y).length).head i)
  have hi : a 16=Sym.blank := owned_intmulinputblockdescriptorsseek_bits_blank (littleBlock x y)
  have ht : transition (relayState .seek) a=(none,fun i => (a i,Move.stay)) := by
    change (if a 16=Sym.blank then (none,fun i => (a i,Move.stay))
      else (relayState .seek,fun i => (a i,if i=16 then Move.right else Move.stay)))=_
    rw [if_pos hi]
  change transition (seekFrame x y (littleBlock x y).length).state
    (fun i => (seekFrame x y (littleBlock x y).length).cells i ((seekFrame x y (littleBlock x y).length).head i))=_ at ht
  apply cfg_ext subroutine
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];rfl

private theorem seek_complete (x y : List Bool) :
    subroutine.step^[(littleBlock x y).length+1] (seekFrame x y 0)=seekDone x y := by
  rw [Function.iterate_succ_apply',seek_run x y _ (by omega),seek_halt]
end IntMul.InputBlockDescriptors

namespace IntMul.InputBlockDescriptors
open TapeCopy (Sym)

private theorem owned_intmulinputblockdescriptorsrewind_bits_not_start (w : List Bool) (j : ℕ) :
    subroutine.tapeOf (w.map subroutine.bitSym) (j+1)≠Sym.start := by
  change (w.map subroutine.bitSym).getD j Sym.blank≠Sym.start
  by_cases h : j< (w.map subroutine.bitSym).length
  · rw [List.getD_eq_getElem _ _ h,List.getElem_map]
    have hj : j< w.length := by simpa only [List.length_map] using h
    cases w[j] <;> decide
  · rw [List.getD_eq_default _ _ (by omega)];decide
private theorem owned_intmulinputblockdescriptorsrewind_bits_start_iff (w : List Bool) (p : ℕ) :
    subroutine.tapeOf (w.map subroutine.bitSym) p=Sym.start ↔ p=0 := by
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p => simp [owned_intmulinputblockdescriptorsrewind_bits_not_start w p]

private theorem rewind_step (x y : List Bool) (p q : ℕ) (hn : 0< p+q) :
    subroutine.step (rewindFrame x y p q)=rewindFrame x y (p-1) (q-1) := by
  let a : Fin 17 → Sym := fun i => (rewindFrame x y p q).cells i ((rewindFrame x y p q).head i)
  have h15 : a 15=Sym.start ↔ p=0 := owned_intmulinputblockdescriptorsrewind_bits_start_iff (widthWord x y) p
  have h16 : a 16=Sym.start ↔ q=0 := owned_intmulinputblockdescriptorsrewind_bits_start_iff (blockWord x y) q
  have hboth : ¬(a 15=Sym.start ∧ a 16=Sym.start) := by rw [h15,h16];omega
  have ht : transition (relayState .rewind) a=(relayState .rewind,fun i => (a i,
      if i=15 then if p=0 then Move.stay else Move.left
      else if i=16 then if q=0 then Move.stay else Move.left else Move.stay)) := by
    change (if a 15=Sym.start ∧ a 16=Sym.start then (none,fun i => (a i,Move.stay))
      else (relayState .rewind,fun i => (a i,
        if (i=15 ∨ i=16) ∧ a i≠Sym.start then Move.left else Move.stay)))=_
    rw [if_neg hboth]
    congr 1
    funext i
    fin_cases i <;> simp [h15,h16]
  change transition (rewindFrame x y p q).state
    (fun i => (rewindFrame x y p q).cells i ((rewindFrame x y p q).head i))=_ at ht
  apply cfg_ext subroutine
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [rewindFrame]
    all_goals split_ifs <;> simp only [] <;> omega

private theorem rewind_halt (x y : List Bool) :
    subroutine.step (rewindFrame x y 0 0)=rewindDone x y := by
  let a : Fin 17 → Sym := fun i => (rewindFrame x y 0 0).cells i ((rewindFrame x y 0 0).head i)
  have h15 : a 15=Sym.start := rfl
  have h16 : a 16=Sym.start := rfl
  have ht : transition (relayState .rewind) a=(none,fun i => (a i,Move.stay)) := by
    change (if a 15=Sym.start ∧ a 16=Sym.start then (none,fun i => (a i,Move.stay))
      else (relayState .rewind,fun i => (a i,
        if (i=15 ∨ i=16) ∧ a i≠Sym.start then Move.left else Move.stay)))=_
    rw [if_pos (And.intro h15 h16)]
  change transition (rewindFrame x y 0 0).state
    (fun i => (rewindFrame x y 0 0).cells i ((rewindFrame x y 0 0).head i))=_ at ht
  apply cfg_ext subroutine
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];rfl

private theorem owned_intmulinputblockdescriptorsrewind_rewind_run_aux (x y : List Bool) (n : ℕ) :
    ∀ p q : ℕ, n=p+q → ∃ t : ℕ, t≤ p+q+1 ∧
      subroutine.step^[t] (rewindFrame x y p q)=rewindDone x y := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro p q hn
      by_cases hzero : p+q=0
      · have hp : p=0 := by omega
        have hq : q=0 := by omega
        subst p;subst q
        refine ⟨1,by omega,?_⟩
        rw [Function.iterate_one,rewind_halt]
      · have hpositive : 0< p+q := by omega
        have hsmall : (p-1)+(q-1)< n := by omega
        obtain ⟨t,ht,he⟩ := ih ((p-1)+(q-1)) hsmall (p-1) (q-1) rfl
        refine ⟨t+1,by omega,?_⟩
        rw [Function.iterate_succ_apply,rewind_step x y p q hpositive,he]

private theorem rewind_complete (x y : List Bool) (p q : ℕ) :
    ∃ t : ℕ, t≤ p+q+1 ∧ subroutine.step^[t] (rewindFrame x y p q)=rewindDone x y :=
  owned_intmulinputblockdescriptorsrewind_rewind_run_aux x y (p+q) p q rfl

end IntMul.InputBlockDescriptors

namespace IntMul.InputBlockDescriptors

private theorem owned_intmulinputblockdescriptorsnumeric_foldl_affine (x : List Bool) (a : ℕ) :
    x.foldl (fun acc b => 2*acc+b.toNat) a=2^x.length*a+val x := by
  induction x generalizing a with
  | nil => simp [val]
  | cons b xs ih =>
      simp only [List.foldl_cons,List.length_cons]
      rw [ih]
      have hv : val (b::xs)=2^xs.length*b.toNat+val xs := by
        simp only [val,List.foldl_cons,Nat.mul_zero,Nat.zero_add]
        exact ih b.toNat
      rw [hv,pow_succ];ring
private theorem owned_intmulinputblockdescriptorsnumeric_val_append (x y : List Bool) : val (x++y)=2^y.length*val x+val y := by
  unfold val;rw [List.foldl_append];exact owned_intmulinputblockdescriptorsnumeric_foldl_affine y _
private theorem owned_intmulinputblockdescriptorsnumeric_val_singleton (b : Bool) : val [b]=b.toNat := by simp [val]
private theorem val_reverse_little (x : List Bool) : val x.reverse=BinaryAdder.littleVal x := by
  induction x with
  | nil => simp [val,BinaryAdder.littleVal]
  | cons b xs ih =>
      rw [List.reverse_cons,owned_intmulinputblockdescriptorsnumeric_val_append,owned_intmulinputblockdescriptorsnumeric_val_singleton]
      simp only [List.length_singleton,pow_one,ih,BinaryAdder.littleVal];ring

private theorem descriptor_facts (x y : List Bool) (hp : 0< x.length+y.length) :
    val (widthWord x y)+1=x.length+y.length ∧
      (widthWord x y).length=Nat.clog 2 (x.length+y.length) ∧
      val (blockWord x y)+1=lg (x.length+y.length) ∧
      (blockWord x y).length=Nat.clog 2 (lg (x.length+y.length)) := by
  obtain ⟨_,_,_,_,_,_,hv⟩ := CanonicalWidthDescriptor.canonical_width_descriptor x y hp
  have hn : x.length+y.length-1+1=x.length+y.length := by omega
  have hl := (GrowingCounter.counter_width_logarithmic (x.length+y.length-1)).1
  rw [hn] at hl
  have hwidth : (widthWord x y).length=Nat.clog 2 (x.length+y.length) := by
    simpa only [widthWord,CanonicalWidthDescriptor.descriptorWord,List.length_reverse] using hl
  obtain ⟨_,_,_,_,_,_,hb,hbl⟩ := WordWidthCounter.count_word_width (widthWord x y)
  have hpositive : max (widthWord x y).length 1=lg (x.length+y.length) := by rw [hwidth];rfl
  refine ⟨hv,hwidth,?_,?_⟩
  · simpa only [blockWord,val_reverse_little,hpositive] using hb
  · simpa only [blockWord,List.length_reverse,hpositive] using hbl
end IntMul.InputBlockDescriptors

namespace IntMul.InputBlockDescriptors

private theorem owned_intmulinputblockdescriptorsprimary_descriptor_execution (x y : List Bool) (hp : 0< x.length+y.length) :
    ∃ t : ℕ, t≤ 18*(x.length+y.length)+7*(widthWord x y).length+10*(blockWord x y).length+50 ∧
      machine.step^[t] (initialFrame x y)=finalFrame x y := by
  obtain ⟨a,ha,hea,hha,hinput,houtput,hvalue⟩ := InputWidthPreparation.input_width_preparation x y hp
  have hwidth : subroutine.step^[a]
      (widthView (emptyBase x y) (InputWidthPreparation.initialFrame x y))=widthDone x y := by
    rw [width_run,hea];rfl
  obtain ⟨b,hb,heb⟩ := (FiniteCaller.simulate_run subroutine Phase .width .width dispatch
    (widthView (emptyBase x y) (InputWidthPreparation.initialFrame x y)) a).2 (by rw [hwidth];rfl)
  rw [hwidth,after_width] at heb
  obtain ⟨c,hc,hec,hhc,hsource,hout,hcounter,hlength⟩ := WordWidthCounter.count_word_width (widthWord x y)
  have hword : subroutine.step^[c] (wordIn x y)=wordDone x y := by
    rw [wordIn,word_run,hec];rfl
  obtain ⟨d,hd,hed⟩ := (FiniteCaller.simulate_run subroutine Phase .width .word dispatch
    (wordIn x y) c).2 (by rw [hword];rfl)
  rw [hword,after_word] at hed
  obtain ⟨e,he,hee⟩ := (FiniteCaller.simulate_run subroutine Phase .width .seek dispatch
    (seekFrame x y 0) ((littleBlock x y).length+1)).2 (by rw [seek_complete];rfl)
  rw [seek_complete,after_seek] at hee
  obtain ⟨f,hf,hef,hhf⟩ := CanonicalOutput.canonical_output (orderBase x y) (littleBlock x y)
  have horder : subroutine.step^[f] (orderIn x y)=orderDone x y := by
    rw [orderIn,order_run,hef];rfl
  obtain ⟨g,hg,heg⟩ := (FiniteCaller.simulate_run subroutine Phase .width .order dispatch
    (orderIn x y) f).2 (by rw [horder];rfl)
  rw [horder,after_order] at heg
  obtain ⟨h,hh,heh⟩ := rewind_complete x y ((widthWord x y).length+1) ((blockWord x y).length+1)
  obtain ⟨j,hj,hej⟩ := (FiniteCaller.simulate_run subroutine Phase .width .rewind dispatch
    (rewindFrame x y ((widthWord x y).length+1) ((blockWord x y).length+1)) h).2 (by rw [heh];rfl)
  rw [heh,final_handoff] at hej
  have hlen : (littleBlock x y).length=(blockWord x y).length := by simp [littleBlock,blockWord]
  refine ⟨j+(g+(e+(d+b))),?_,?_⟩
  · rw [hlen] at he hf;omega
  · rw [Function.iterate_add_apply,Function.iterate_add_apply,Function.iterate_add_apply,
      Function.iterate_add_apply,initial_handoff,heb,hed,hee,heg,hej]

/-- Actual width and logarithmic block-size descriptors from the original
operand input, with output empty and both retained descriptors rewound. -/
private theorem input_block_descriptors (x y : List Bool) (hp : 0< x.length+y.length) :
    ∃ t : ℕ, t≤ 18*(x.length+y.length)+7*Nat.clog 2 (x.length+y.length)+
        10*Nat.clog 2 (lg (x.length+y.length))+50 ∧
      machine.step^[t] (initialFrame x y)=finalFrame x y ∧
      (machine.step^[t] (initialFrame x y)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame x y)).cells machine.inTape=(initialFrame x y).cells machine.inTape ∧
      (machine.step^[t] (initialFrame x y)).cells machine.outTape=machine.tapeOf [] ∧
      val (widthWord x y)+1=x.length+y.length ∧
      val (blockWord x y)+1=lg (x.length+y.length) ∧
      (widthWord x y).length=Nat.clog 2 (x.length+y.length) ∧
      (blockWord x y).length=Nat.clog 2 (lg (x.length+y.length)) := by
  obtain ⟨t,ht,he⟩ := owned_intmulinputblockdescriptorsprimary_descriptor_execution x y hp
  obtain ⟨hvalue,hlength,hblock,hblocklength⟩ := descriptor_facts x y hp
  refine ⟨t,by simpa only [hlength,hblocklength] using ht,he,?_,?_,?_,hvalue,hblock,hlength,hblocklength⟩
  · rw [he];rfl
  · rw [he];simp [finalFrame,initialFrame,MultitapeTM.initCfg,MultitapeTM.inTape]
  · rw [he];simp [finalFrame,MultitapeTM.outTape]
end IntMul.InputBlockDescriptors


open IntMul IntMul.InputBlockDescriptors

theorem solution (x y : List Bool) (hp : 0< x.length+y.length) :
    ∃ t : ℕ, t≤ 18*(x.length+y.length)+7*Nat.clog 2 (x.length+y.length)+
        10*Nat.clog 2 (lg (x.length+y.length))+50 ∧
      machine.step^[t] (initialFrame x y)=finalFrame x y ∧
      (machine.step^[t] (initialFrame x y)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame x y)).cells machine.inTape=(initialFrame x y).cells machine.inTape ∧
      (machine.step^[t] (initialFrame x y)).cells machine.outTape=machine.tapeOf [] ∧
      val (widthWord x y)+1=x.length+y.length ∧
      val (blockWord x y)+1=lg (x.length+y.length) ∧
      (widthWord x y).length=Nat.clog 2 (x.length+y.length) ∧
      (blockWord x y).length=Nat.clog 2 (lg (x.length+y.length)) :=
  IntMul.InputBlockDescriptors.input_block_descriptors x y hp

#print axioms solution
