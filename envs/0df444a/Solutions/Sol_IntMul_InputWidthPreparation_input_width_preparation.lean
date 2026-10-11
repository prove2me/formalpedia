-- Prove2me | solution 1 for IntMul.InputWidthPreparation.input_width_preparation
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T15:05:26.929169+00:00
-- url     : https://prove2.me/submissions/a3f22c96-0671-4865-a3a8-d53bb3747272

import Definitions.Def_IntMul_InputWidthPreparation
import Mathlib.Tactic
import Theorems.Thm_IntMul_CanonicalWidthDescriptor_canonical_width_descriptor
import Theorems.Thm_IntMul_WidthPreparation_prepare_width
import Theorems.Thm_IntMul_FiniteCaller_simulate_run

set_option maxHeartbeats 1000000
set_option Elab.async false


set_option maxHeartbeats 1000000
set_option Elab.async false

namespace IntMul.InputWidthPreparation
open TapeCopy (Sym)

private theorem cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c;cases d;cases hs;cases hc;cases hh;rfl

private noncomputable def computeView (base : subroutine.Cfg) (c : CanonicalWidthDescriptor.machine.Cfg) : subroutine.Cfg where
  state := computeState c.state
  cells := fun i => if i=15 then c.cells 1 else if i=1 then base.cells i
    else if h : i.val< 15 then c.cells (computeIndex i h) else base.cells i
  head := fun i => if i=15 then c.head 1 else if i=1 then base.head i
    else if h : i.val< 15 then c.head (computeIndex i h) else base.head i

private theorem compute_step (base : subroutine.Cfg) (c : CanonicalWidthDescriptor.machine.Cfg) :
    subroutine.step (computeView base c)=computeView base (CanonicalWidthDescriptor.machine.step c) := by
  let a : Fin 16 → Sym := fun i => (computeView base c).cells i ((computeView base c).head i)
  let b : Fin 15 → Sym := fun j => c.cells j (c.head j)
  have ha : (fun j => a (computeTape j))=b := by funext j;fin_cases j <;> rfl
  have ht : transition (computeState c.state) a=(computeState (CanonicalWidthDescriptor.machine.δ c.state b).1,
      computeAction a (CanonicalWidthDescriptor.machine.δ c.state b).2) := by
    by_cases h : c.state=none
    · rw [h,CanonicalWidthDescriptor.machine.halt_fixed b]
      simp only [computeState,if_true,transition]
      congr 1
      funext i
      fin_cases i <;> rfl
    · conv_lhs => rw [computeState,if_neg h]
      change (computeState (CanonicalWidthDescriptor.machine.δ c.state (fun j => a (computeTape j))).1,
        computeAction a (CanonicalWidthDescriptor.machine.δ c.state (fun j => a (computeTape j))).2)=_
      rw [ha]
  change transition (computeView base c).state
    (fun i => (computeView base c).cells i ((computeView base c).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> first | rfl | exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> rfl

private theorem compute_run (base : subroutine.Cfg) (c : CanonicalWidthDescriptor.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (computeView base c)=computeView base (CanonicalWidthDescriptor.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,compute_step,Function.iterate_succ_apply']

private noncomputable def prepareView (c : WidthPreparation.machine.Cfg) : subroutine.Cfg where
  state := prepareState c.state
  cells := c.cells
  head := c.head

private theorem prepare_step (c : WidthPreparation.machine.Cfg) :
    subroutine.step (prepareView c)=prepareView (WidthPreparation.machine.step c) := by
  let a : Fin 16 → Sym := fun i => c.cells i (c.head i)
  have ht : transition (prepareState c.state) a=
      (prepareState (WidthPreparation.machine.δ c.state a).1,(WidthPreparation.machine.δ c.state a).2) := by
    by_cases h : c.state=.halt
    · rw [h,WidthPreparation.machine.halt_fixed a]
      simp only [prepareState,if_true,transition]
    · conv_lhs => rw [prepareState,if_neg h]
      rfl
  change transition (prepareView c).state (fun i => (prepareView c).cells i ((prepareView c).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl

private theorem prepare_run (c : WidthPreparation.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (prepareView c)=prepareView (WidthPreparation.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,prepare_step,Function.iterate_succ_apply']

end IntMul.InputWidthPreparation


namespace IntMul.InputWidthPreparation
open TapeCopy (Sym)

private noncomputable def emptyBase (x y : List Bool) : subroutine.Cfg where
  state := none
  cells := (initialFrame x y).cells
  head := (initialFrame x y).head
private noncomputable def computeDone (x y : List Bool) : subroutine.Cfg :=
  computeView (emptyBase x y) (CanonicalWidthDescriptor.finalFrame x y)
private noncomputable def rewindFrame (x y : List Bool) (p : ℕ) : subroutine.Cfg :=
  {computeDone x y with state := rewindState,head := Function.update (computeDone x y).head 15 p}
private noncomputable def rewindDone (x y : List Bool) : subroutine.Cfg :=
  {rewindFrame x y 0 with state := none}
private noncomputable def prepareBase (x y : List Bool) : WidthPreparation.machine.Cfg where
  state := .halt
  cells := (rewindDone x y).cells
  head := (rewindDone x y).head
private noncomputable def prepareIn (x y : List Bool) : subroutine.Cfg :=
  prepareView (WidthPreparation.initialFrame (prepareBase x y) (CanonicalWidthDescriptor.descriptorWord x y))
private noncomputable def prepareDone (x y : List Bool) : subroutine.Cfg :=
  prepareView (WidthPreparation.finalFrame (prepareBase x y) (CanonicalWidthDescriptor.descriptorWord x y))

private theorem initial_handoff (x y : List Bool) :
    initialFrame x y=FiniteCaller.embed subroutine Phase .compute .compute dispatch
      (computeView (emptyBase x y) (CanonicalWidthDescriptor.initialFrame x y)) := by
  apply cfg_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl

private theorem after_compute (x y : List Bool) :
    FiniteCaller.returned subroutine Phase .compute .compute dispatch (computeDone x y)=
      FiniteCaller.embed subroutine Phase .compute .rewind dispatch
        (rewindFrame x y ((CanonicalWidthDescriptor.descriptorWord x y).length+1)) := by
  apply cfg_ext
  · rfl
  · rfl
  · have h : (computeDone x y).head 15=(CanonicalWidthDescriptor.descriptorWord x y).length+1 := rfl
    change (computeDone x y).head=Function.update (computeDone x y).head 15 _
    rw [←h,Function.update_eq_self]

private theorem after_rewind (x y : List Bool) :
    FiniteCaller.returned subroutine Phase .compute .rewind dispatch (rewindDone x y)=
      FiniteCaller.embed subroutine Phase .compute .prepare dispatch (prepareIn x y) := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,FiniteCaller.embed,rewindDone,rewindFrame,
      prepareIn,prepareView,WidthPreparation.initialFrame,prepareBase,computeDone,computeView,
      computeIndex,CanonicalWidthDescriptor.finalFrame,emptyBase,initialFrame,MultitapeTM.initCfg,
      MultitapeTM.inTape] <;> rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,FiniteCaller.embed,rewindDone,rewindFrame,
      prepareIn,prepareView,WidthPreparation.initialFrame,prepareBase,computeDone,computeView,
      computeIndex,CanonicalWidthDescriptor.finalFrame,emptyBase,initialFrame,MultitapeTM.initCfg]

private theorem final_handoff (x y : List Bool) :
    FiniteCaller.returned subroutine Phase .compute .prepare dispatch (prepareDone x y)=finalFrame x y := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,prepareDone,prepareView,WidthPreparation.finalFrame,
      prepareBase,rewindDone,rewindFrame,computeDone,computeView,computeIndex,
      CanonicalWidthDescriptor.finalFrame,finalFrame,emptyBase,initialFrame,MultitapeTM.initCfg,
      MultitapeTM.inTape] <;> rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,prepareDone,prepareView,WidthPreparation.finalFrame,
      prepareBase,rewindDone,rewindFrame,computeDone,computeView,computeIndex,
      CanonicalWidthDescriptor.finalFrame,finalFrame,emptyBase,initialFrame,MultitapeTM.initCfg]

end IntMul.InputWidthPreparation


namespace IntMul.InputWidthPreparation
open TapeCopy (Sym)

private theorem owned_intmulinputwidthpreparationrewind_bit_not_start (b : Bool) : subroutine.bitSym b≠Sym.start := by cases b <;> decide

private theorem owned_intmulinputwidthpreparationrewind_bits_not_start (w : List Bool) (j : ℕ) :
    subroutine.tapeOf (w.map subroutine.bitSym) (j+1)≠Sym.start := by
  change (w.map subroutine.bitSym).getD j Sym.blank≠Sym.start
  by_cases h : j< (w.map subroutine.bitSym).length
  · rw [List.getD_eq_getElem _ _ h]
    simp only [List.getElem_map]
    exact owned_intmulinputwidthpreparationrewind_bit_not_start _
  · rw [List.getD_eq_default _ _ (by omega)]
    decide

private theorem rewind_step (x y : List Bool) (p : ℕ) :
    subroutine.step (rewindFrame x y (p+1))=rewindFrame x y p := by
  let a : Fin 16 → Sym := fun i => (rewindFrame x y (p+1)).cells i ((rewindFrame x y (p+1)).head i)
  have hi : a 15≠Sym.start := owned_intmulinputwidthpreparationrewind_bits_not_start (CanonicalWidthDescriptor.descriptorWord x y) p
  have ht : transition rewindState a=(rewindState,fun i => (a i,if i=15 then Move.left else Move.stay)) := by
    simp only [transition,rewindState,if_neg hi]
  change transition (rewindFrame x y (p+1)).state
    (fun i => (rewindFrame x y (p+1)).cells i ((rewindFrame x y (p+1)).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [rewindFrame]

private theorem rewind_run (x y : List Bool) (p : ℕ) :
    subroutine.step^[p] (rewindFrame x y p)=rewindFrame x y 0 := by
  induction p with
  | zero => rfl
  | succ p ih => rw [Function.iterate_succ_apply,rewind_step,ih]

private theorem rewind_halt (x y : List Bool) :
    subroutine.step (rewindFrame x y 0)=rewindDone x y := by
  let a : Fin 16 → Sym := fun i => (rewindFrame x y 0).cells i ((rewindFrame x y 0).head i)
  have hi : a 15=Sym.start := rfl
  have ht : transition rewindState a=(none,fun i => (a i,Move.stay)) := by
    simp only [transition,rewindState,if_pos hi]
  change transition (rewindFrame x y 0).state
    (fun i => (rewindFrame x y 0).cells i ((rewindFrame x y 0).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];rfl

private theorem rewind_complete (x y : List Bool) :
    subroutine.step^[(CanonicalWidthDescriptor.descriptorWord x y).length+2]
      (rewindFrame x y ((CanonicalWidthDescriptor.descriptorWord x y).length+1))=rewindDone x y := by
  rw [show (CanonicalWidthDescriptor.descriptorWord x y).length+2=
    ((CanonicalWidthDescriptor.descriptorWord x y).length+1)+1 by omega,
    Function.iterate_succ_apply',rewind_run,rewind_halt]

end IntMul.InputWidthPreparation


namespace IntMul.InputWidthPreparation

private theorem owned_intmulinputwidthpreparationnumeric_increment_length (bits : List Bool) :
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
      have hi := owned_intmulinputwidthpreparationnumeric_increment_length bits
      simp only [GrowingCounter.iterateCounter]
      omega

end IntMul.InputWidthPreparation


namespace IntMul.InputWidthPreparation

private theorem preparation_execution (x y : List Bool) (hp : 0< x.length+y.length) :
    ∃ t : ℕ, t≤ 15*(x.length+y.length)+3*(CanonicalWidthDescriptor.descriptorWord x y).length+24 ∧
      machine.step^[t] (initialFrame x y)=finalFrame x y := by
  obtain ⟨a,ha,hea,hha,hinput,houtput,hvalue⟩ := CanonicalWidthDescriptor.canonical_width_descriptor x y hp
  have hcompute : subroutine.step^[a]
      (computeView (emptyBase x y) (CanonicalWidthDescriptor.initialFrame x y))=computeDone x y := by
    rw [compute_run,hea];rfl
  obtain ⟨b,hb,heb⟩ := (FiniteCaller.simulate_run subroutine Phase .compute .compute dispatch
    (computeView (emptyBase x y) (CanonicalWidthDescriptor.initialFrame x y)) a).2
      (by rw [hcompute];rfl)
  rw [hcompute,after_compute] at heb
  obtain ⟨c,hc,hec⟩ := (FiniteCaller.simulate_run subroutine Phase .compute .rewind dispatch
    (rewindFrame x y ((CanonicalWidthDescriptor.descriptorWord x y).length+1))
      ((CanonicalWidthDescriptor.descriptorWord x y).length+2)).2 (by rw [rewind_complete];rfl)
  rw [rewind_complete,after_rewind] at hec
  have hnative := (WidthPreparation.prepare_width (prepareBase x y) (CanonicalWidthDescriptor.descriptorWord x y)).1
  have hprepare : subroutine.step^[2*(CanonicalWidthDescriptor.descriptorWord x y).length+4]
      (prepareIn x y)=prepareDone x y := by
    rw [prepareIn,prepare_run,hnative];rfl
  obtain ⟨e,he,hee⟩ := (FiniteCaller.simulate_run subroutine Phase .compute .prepare dispatch
    (prepareIn x y) (2*(CanonicalWidthDescriptor.descriptorWord x y).length+4)).2 (by rw [hprepare];rfl)
  rw [hprepare,final_handoff] at hee
  refine ⟨e+(c+b),by omega,?_⟩
  rw [Function.iterate_add_apply,Function.iterate_add_apply,initial_handoff,heb,hec,hee]

/-- Fully prepare retained width and both real countdown banks from original
operand input, retaining empty output and all unused scratch banks. -/
private theorem input_width_preparation (x y : List Bool) (hp : 0< x.length+y.length) :
    ∃ t : ℕ, t≤ 18*(x.length+y.length)+21 ∧
      machine.step^[t] (initialFrame x y)=finalFrame x y ∧
      (machine.step^[t] (initialFrame x y)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame x y)).cells machine.inTape=(initialFrame x y).cells machine.inTape ∧
      (machine.step^[t] (initialFrame x y)).cells machine.outTape=machine.tapeOf [] ∧
      val (CanonicalWidthDescriptor.descriptorWord x y)+1=x.length+y.length := by
  obtain ⟨t,ht,he⟩ := preparation_execution x y hp
  have hl := iterate_length (x.length+y.length-1) []
  simp only [List.length_nil,Nat.zero_add] at hl
  have hld : (CanonicalWidthDescriptor.descriptorWord x y).length≤ x.length+y.length-1 := by
    simpa only [CanonicalWidthDescriptor.descriptorWord,List.length_reverse] using hl
  obtain ⟨a,ha,hea,hha,hinput,houtput,hvalue⟩ := CanonicalWidthDescriptor.canonical_width_descriptor x y hp
  refine ⟨t,by omega,he,?_,?_,?_,hvalue⟩
  · rw [he];rfl
  · rw [he]
    simp [finalFrame,initialFrame,MultitapeTM.initCfg,MultitapeTM.inTape]
  · rw [he];simp [finalFrame,MultitapeTM.outTape]

end IntMul.InputWidthPreparation


open IntMul IntMul.InputWidthPreparation

theorem solution (x y : List Bool) (hp : 0< x.length+y.length) :
    ∃ t : ℕ, t≤ 18*(x.length+y.length)+21 ∧
      machine.step^[t] (initialFrame x y)=finalFrame x y ∧
      (machine.step^[t] (initialFrame x y)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame x y)).cells machine.inTape=(initialFrame x y).cells machine.inTape ∧
      (machine.step^[t] (initialFrame x y)).cells machine.outTape=machine.tapeOf [] ∧
      val (CanonicalWidthDescriptor.descriptorWord x y)+1=x.length+y.length :=
  IntMul.InputWidthPreparation.input_width_preparation x y hp

#print axioms solution
