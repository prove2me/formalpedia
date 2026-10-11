-- Prove2me | solution 1 for IntMul.CarryInitialization.initialize_carry
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T17:02:15.876245+00:00
-- url     : https://prove2.me/submissions/7fcbc1ef-6dc7-4876-b1a4-9956b992552e

import Definitions.Def_IntMul_CarryInitialization
import Theorems.Thm_IntMul_WidthPreparation_prepare_width
import Theorems.Thm_IntMul_ZeroCarry_initialize_zero_carry
import Theorems.Thm_IntMul_FiniteCaller_simulate_run
import Mathlib.Tactic

set_option maxHeartbeats 1000000
set_option Elab.async false

namespace IntMul.CarryInitialization
open TapeCopy (Sym)
private theorem cfg_ext (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c;cases d;cases hs;cases hc;cases hh;rfl

private theorem width_step (c : WidthPreparation.machine.Cfg) :
    subroutine.step (widthView c)=widthView (WidthPreparation.machine.step c) := by
  let a : Fin 16 → Sym := fun i => c.cells i (c.head i)
  have ht : transition (widthState c.state) a=(widthState (WidthPreparation.machine.δ c.state a).1,
      (WidthPreparation.machine.δ c.state a).2) := by
    by_cases h : c.state=.halt
    · rw [h,WidthPreparation.machine.halt_fixed a];rfl
    · conv_lhs => rw [widthState,if_neg h]
      rfl
  change transition (widthView c).state (fun i => (widthView c).cells i ((widthView c).head i))=_ at ht
  apply cfg_ext subroutine
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl

private theorem width_run (c : WidthPreparation.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (widthView c)=widthView (WidthPreparation.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,width_step,Function.iterate_succ_apply']

private theorem zero_read (base : machine.Cfg) (l : List Bool) (c : ZeroCarry.machine.Cfg) (j : Fin 4) :
    (zeroView base l c).cells (zeroTape j) ((zeroView base l c).head (zeroTape j))=c.cells j (c.head j) := by
  fin_cases j <;> simp [zeroView,zeroTape]

private theorem zero_step (base : machine.Cfg) (l : List Bool) (c : ZeroCarry.machine.Cfg) :
    subroutine.step (zeroView base l c)=zeroView base l (ZeroCarry.machine.step c) := by
  classical
  let a : Fin 16 → Sym := fun i => (zeroView base l c).cells i ((zeroView base l c).head i)
  have hread : (fun j => a (zeroTape j))=(fun j => c.cells j (c.head j)) := by
    funext j;exact zero_read base l c j
  have ht : transition (zeroState c.state) a=
      (zeroState (ZeroCarry.machine.δ c.state (fun j => c.cells j (c.head j))).1,
        zeroAction a (ZeroCarry.machine.δ c.state (fun j => c.cells j (c.head j))).2) := by
    by_cases h : c.state=ZeroCarry.machine.qHalt
    · rw [h,ZeroCarry.machine.halt_fixed]
      simp only [zeroState,ite_true,transition]
      congr 1;funext i;fin_cases i <;> simp [zeroAction,a,zeroView,zeroTape]
    · conv_lhs => rw [zeroState,if_neg h]
      change (zeroState (ZeroCarry.machine.δ c.state (fun j => a (zeroTape j))).1,
        zeroAction a (ZeroCarry.machine.δ c.state (fun j => a (zeroTape j))).2)=_
      rw [hread]
  change transition (zeroView base l c).state
    (fun i => (zeroView base l c).cells i ((zeroView base l c).head i))=_ at ht
  apply cfg_ext subroutine
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];funext i p
    fin_cases i <;> simp [zeroView,zeroAction,a,MultitapeTM.step]
  · simp only [MultitapeTM.step,ht];funext i
    fin_cases i <;> simp [zeroView,zeroAction,MultitapeTM.step]

private theorem zero_run (base : machine.Cfg) (l : List Bool) (c : ZeroCarry.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (zeroView base l c)=zeroView base l (ZeroCarry.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,zero_step,Function.iterate_succ_apply']
end IntMul.CarryInitialization

namespace IntMul.CarryInitialization
open TapeCopy (Sym)
private theorem after_width (base : machine.Cfg) (l : List Bool) :
    FiniteCaller.returned subroutine Bool false false dispatch
      (widthView (WidthPreparation.finalFrame (widthBase base) l))=
    FiniteCaller.embed subroutine Bool false true dispatch
      (zeroView base l (ZeroCarry.initialFrame (zeroBase base l) l)) := by
  apply cfg_ext machine
  · rfl
  · funext i;fin_cases i <;> simp [FiniteCaller.returned,FiniteCaller.embed,widthView,zeroView,
      ZeroCarry.initialFrame,ZeroCarry.zeroView,ZeroCarry.nativeBase,CountedZero.initialFrame,
      zeroBase,zeroTape,WidthPreparation.finalFrame,widthBase,WidthPreparation.descriptorTape] <;> rfl
  · funext i;fin_cases i <;> simp [FiniteCaller.returned,FiniteCaller.embed,widthView,zeroView,
      ZeroCarry.initialFrame,ZeroCarry.zeroView,ZeroCarry.nativeBase,CountedZero.initialFrame,
      zeroBase,zeroTape,WidthPreparation.finalFrame,widthBase]
private theorem owned_intmulcarryinitializationframes_bin_zero (n : ℕ) : bin n 0=List.replicate n false := by
  simp [bin,List.ofFn_const]
private theorem final_handoff (base : machine.Cfg) (l : List Bool) :
    FiniteCaller.returned subroutine Bool false true dispatch
      (zeroView base l (ZeroCarry.finalFrame (zeroBase base l) l))=finalFrame base l := by
  apply cfg_ext machine
  · rfl
  · funext i;fin_cases i <;> simp [FiniteCaller.returned,zeroView,ZeroCarry.finalFrame,ZeroCarry.nativeBase,
      CountedZero.finalFrame,CountedZero.frame,zeroBase,zeroTape,WidthPreparation.finalFrame,widthBase,
      WidthPreparation.descriptorTape,finalFrame,owned_intmulcarryinitializationframes_bin_zero] <;> rfl
  · funext i;fin_cases i <;> simp [FiniteCaller.returned,zeroView,ZeroCarry.finalFrame,ZeroCarry.nativeBase,
      CountedZero.finalFrame,CountedZero.frame,zeroBase,zeroTape,WidthPreparation.finalFrame,widthBase,finalFrame]
end IntMul.CarryInitialization

namespace IntMul.CarryInitialization
open TapeCopy (Sym)
private theorem initialize_carry (base : machine.Cfg) (l : List Bool) :
    ∃ t : ℕ, t≤ 7*(val l+1)+6*l.length+13 ∧
      machine.step^[t] (initialFrame base l)=finalFrame base l ∧
      (machine.step^[t] (initialFrame base l)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame base l)).cells machine.inTape=base.cells machine.inTape ∧
      (machine.step^[t] (initialFrame base l)).head machine.inTape=base.head machine.inTape ∧
      (machine.step^[t] (initialFrame base l)).cells 12=machine.tapeOf ((bin (val l+1) 0).map machine.bitSym) ∧
      (machine.step^[t] (initialFrame base l)).head 12=0 ∧
      (machine.step^[t] (initialFrame base l)).cells 15=machine.tapeOf (l.map machine.bitSym) ∧
      (machine.step^[t] (initialFrame base l)).head 15=0 ∧
      (∀ i : Fin 16, i.val≠3 → i.val≠4 → i.val≠12 → i.val≠15 →
        (machine.step^[t] (initialFrame base l)).cells i=base.cells i ∧
        (machine.step^[t] (initialFrame base l)).head i=base.head i) := by
  have hw := (WidthPreparation.prepare_width (widthBase base) l).1
  have hwidth : subroutine.step^[2*l.length+4]
      (widthView (WidthPreparation.initialFrame (widthBase base) l))=
      widthView (WidthPreparation.finalFrame (widthBase base) l) := by rw [width_run,hw]
  obtain ⟨a,ha,hea⟩ := (FiniteCaller.simulate_run subroutine Bool false false dispatch
    (widthView (WidthPreparation.initialFrame (widthBase base) l)) (2*l.length+4)).2
      (by rw [hwidth];rfl)
  rw [hwidth,after_width] at hea
  obtain ⟨b,hb,heb,hhalt,hinput,hhead,houtput,houthead⟩ :=
    ZeroCarry.initialize_zero_carry (zeroBase base l) l
  have hzero : subroutine.step^[b] (zeroView base l (ZeroCarry.initialFrame (zeroBase base l) l))=
      zeroView base l (ZeroCarry.finalFrame (zeroBase base l) l) := by rw [zero_run,heb]
  obtain ⟨c,hc,hec⟩ := (FiniteCaller.simulate_run subroutine Bool false true dispatch
    (zeroView base l (ZeroCarry.initialFrame (zeroBase base l) l)) b).2
      (by rw [hzero];simp [zeroView,zeroState,ZeroCarry.finalFrame])
  rw [hzero,final_handoff] at hec
  have he : machine.step^[c+a] (initialFrame base l)=finalFrame base l := by
    rw [Function.iterate_add_apply];change machine.step^[c]
      (machine.step^[a] (FiniteCaller.embed subroutine Bool false false dispatch
        (widthView (WidthPreparation.initialFrame (widthBase base) l))))=_
    rw [hea,hec]
  refine ⟨c+a,by omega,he,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals rw [he]
  · rfl
  · simp [finalFrame,WidthPreparation.finalFrame,widthBase,MultitapeTM.inTape]
  · simp [finalFrame,WidthPreparation.finalFrame,widthBase,MultitapeTM.inTape]
  · simp [finalFrame]
  · simp [finalFrame,WidthPreparation.finalFrame,widthBase]
  · simp [finalFrame,WidthPreparation.finalFrame,widthBase];rfl
  · simp [finalFrame,WidthPreparation.finalFrame,widthBase]
  · intro i h3 h4 h12 h15
    have hn3 : i≠3 := by intro h;subst i;contradiction
    have hn4 : i≠4 := by intro h;subst i;contradiction
    have hn12 : i≠12 := by intro h;subst i;contradiction
    have hn15 : i≠15 := by intro h;subst i;contradiction
    simp [finalFrame,WidthPreparation.finalFrame,widthBase,hn3,hn4,hn12,hn15]
end IntMul.CarryInitialization


open IntMul IntMul.CarryInitialization

theorem solution (base : machine.Cfg) (l : List Bool) :
    ∃ t : ℕ, t≤ 7*(val l+1)+6*l.length+13 ∧
      machine.step^[t] (initialFrame base l)=finalFrame base l ∧
      (machine.step^[t] (initialFrame base l)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame base l)).cells machine.inTape=base.cells machine.inTape ∧
      (machine.step^[t] (initialFrame base l)).head machine.inTape=base.head machine.inTape ∧
      (machine.step^[t] (initialFrame base l)).cells 12=machine.tapeOf ((bin (val l+1) 0).map machine.bitSym) ∧
      (machine.step^[t] (initialFrame base l)).head 12=0 ∧
      (machine.step^[t] (initialFrame base l)).cells 15=machine.tapeOf (l.map machine.bitSym) ∧
      (machine.step^[t] (initialFrame base l)).head 15=0 ∧
      (∀ i : Fin 16, i.val≠3 → i.val≠4 → i.val≠12 → i.val≠15 →
        (machine.step^[t] (initialFrame base l)).cells i=base.cells i ∧
        (machine.step^[t] (initialFrame base l)).head i=base.head i) :=
  IntMul.CarryInitialization.initialize_carry base l

#print axioms solution
