-- Prove2me | solution 1 for IntMul.ZeroCarry.initialize_zero_carry
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T16:45:38.768515+00:00
-- url     : https://prove2.me/submissions/af0ee994-a0b6-44de-b736-1fcb754ec110

import Definitions.Def_IntMul_ZeroCarry
import Theorems.Thm_IntMul_CountedZero_generate_zero_word
import Theorems.Thm_IntMul_FiniteCaller_simulate_run
import Mathlib.Tactic

set_option maxHeartbeats 1000000
set_option Elab.async false

namespace IntMul.ZeroCarry
open TapeCopy (Sym)
private theorem cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c;cases d;cases hs;cases hc;cases hh;rfl

private theorem zero_step (c : CountedZero.machine.Cfg) :
    subroutine.step (zeroView c)=zeroView (CountedZero.machine.step c) := by
  let a : Fin 4 → Sym := fun i => c.cells i (c.head i)
  have ht : transition (zeroState c.state) a=(zeroState (CountedZero.machine.δ c.state a).1,
      (CountedZero.machine.δ c.state a).2) := by
    by_cases h : c.state=.halt
    · rw [h,CountedZero.machine.halt_fixed a];rfl
    · conv_lhs => rw [zeroState,if_neg h]
      rfl
  change transition (zeroView c).state
    (fun i => (zeroView c).cells i ((zeroView c).head i))=_ at ht
  apply cfg_ext subroutine
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl

private theorem zero_run (c : CountedZero.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (zeroView c)=zeroView (CountedZero.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,zero_step,Function.iterate_succ_apply']

private theorem after_zero (base : machine.Cfg) (z : List Bool) :
    FiniteCaller.returned subroutine Bool false false dispatch
      (zeroView (CountedZero.finalFrame (nativeBase base) z))=
    FiniteCaller.embed subroutine Bool false true dispatch (rewindFrame base z (val z+2)) := by
  apply cfg_ext machine
  · rfl
  · rfl
  · funext i;fin_cases i <;> simp [FiniteCaller.returned,FiniteCaller.embed,zeroView,rewindFrame,
      CountedZero.finalFrame,CountedZero.frame]

private theorem final_handoff (base : machine.Cfg) (z : List Bool) :
    FiniteCaller.returned subroutine Bool false true dispatch (rewindDone base z)=finalFrame base z := by
  rfl
end IntMul.ZeroCarry

namespace IntMul.ZeroCarry
open TapeCopy (Sym)

private theorem owned_intmulzerocarryrewind_bits_not_start (w : List Bool) (j : ℕ) :
    subroutine.tapeOf (w.map subroutine.bitSym) (j+1)≠Sym.start := by
  change (w.map subroutine.bitSym).getD j Sym.blank≠Sym.start
  by_cases h : j< (w.map subroutine.bitSym).length
  · rw [List.getD_eq_getElem _ _ h,List.getElem_map]
    have hj : j< w.length := by simpa only [List.length_map] using h
    cases w[j] <;> decide
  · rw [List.getD_eq_default _ _ (by omega)];decide
private theorem owned_intmulzerocarryrewind_bits_start_iff (w : List Bool) (p : ℕ) :
    subroutine.tapeOf (w.map subroutine.bitSym) p=Sym.start ↔ p=0 := by
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p => simp [owned_intmulzerocarryrewind_bits_not_start w p]

private theorem rewind_step (base : machine.Cfg) (z : List Bool) (p : ℕ) :
    subroutine.step (rewindFrame base z (p+1))=rewindFrame base z p := by
  let a : Fin 4 → Sym := fun i => (rewindFrame base z (p+1)).cells i ((rewindFrame base z (p+1)).head i)
  have hn : a 1≠Sym.start := owned_intmulzerocarryrewind_bits_not_start (List.replicate (val z+1) false) p
  have ht : transition rewindState a=(rewindState,fun i => (a i,if i=1 then Move.left else Move.stay)) := by
    change (if a 1=Sym.start then (none,fun i => (a i,Move.stay))
      else (rewindState,fun i => (a i,if i=1 then Move.left else Move.stay)))=_
    rw [if_neg hn]
  change transition (rewindFrame base z (p+1)).state
    (fun i => (rewindFrame base z (p+1)).cells i ((rewindFrame base z (p+1)).head i))=_ at ht
  apply cfg_ext subroutine
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];funext i;fin_cases i <;> simp [rewindFrame,CountedZero.finalFrame,CountedZero.frame]

private theorem rewind_halt (base : machine.Cfg) (z : List Bool) :
    subroutine.step (rewindFrame base z 0)=rewindDone base z := by
  let a : Fin 4 → Sym := fun i => (rewindFrame base z 0).cells i ((rewindFrame base z 0).head i)
  have hi : a 1=Sym.start := rfl
  have ht : transition rewindState a=(none,fun i => (a i,Move.stay)) := by
    change (if a 1=Sym.start then (none,fun i => (a i,Move.stay))
      else (rewindState,fun i => (a i,if i=1 then Move.left else Move.stay)))=_
    rw [if_pos hi]
  change transition (rewindFrame base z 0).state
    (fun i => (rewindFrame base z 0).cells i ((rewindFrame base z 0).head i))=_ at ht
  apply cfg_ext subroutine
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];rfl

private theorem rewind_complete (base : machine.Cfg) (z : List Bool) (p : ℕ) :
    subroutine.step^[p+1] (rewindFrame base z p)=rewindDone base z := by
  induction p with
  | zero => rw [Function.iterate_one,rewind_halt]
  | succ p ih => rw [Function.iterate_succ_apply,rewind_step,ih]
end IntMul.ZeroCarry

namespace IntMul.ZeroCarry
open TapeCopy (Sym)

private theorem initialize_zero_carry (base : machine.Cfg) (z : List Bool) :
    ∃ t : ℕ, t≤ 7*(val z+1)+4*z.length+7 ∧
      machine.step^[t] (initialFrame base z)=finalFrame base z ∧
      (machine.step^[t] (initialFrame base z)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame base z)).cells machine.inTape=base.cells machine.inTape ∧
      (machine.step^[t] (initialFrame base z)).head machine.inTape=base.head machine.inTape ∧
      (machine.step^[t] (initialFrame base z)).cells machine.outTape=
        machine.tapeOf ((bin (val z+1) 0).map machine.bitSym) ∧
      (machine.step^[t] (initialFrame base z)).head machine.outTape=0 := by
  obtain ⟨a,ha,hea,hinput,hhead,houtput,hhalt,houthead⟩ :=
    CountedZero.generate_zero_word (nativeBase base) z
  have hzero : subroutine.step^[a] (zeroView (CountedZero.initialFrame (nativeBase base) z))=
      zeroView (CountedZero.finalFrame (nativeBase base) z) := by rw [zero_run,hea]
  obtain ⟨b,hb,heb⟩ := (FiniteCaller.simulate_run subroutine Bool false false dispatch
    (zeroView (CountedZero.initialFrame (nativeBase base) z)) a).2 (by rw [hzero];rfl)
  rw [hzero,after_zero] at heb
  have hrewind := rewind_complete base z (val z+2)
  obtain ⟨c,hc,hec⟩ := (FiniteCaller.simulate_run subroutine Bool false true dispatch
    (rewindFrame base z (val z+2)) ((val z+2)+1)).2 (by rw [hrewind];rfl)
  rw [hrewind,final_handoff] at hec
  have hrun : machine.step^[c+b] (initialFrame base z)=finalFrame base z := by
    rw [Function.iterate_add_apply];change machine.step^[c]
      (machine.step^[b] (FiniteCaller.embed subroutine Bool false false dispatch
        (zeroView (CountedZero.initialFrame (nativeBase base) z))))=_
    rw [heb,hec]
  rw [hea] at houtput
  refine ⟨c+b,by omega,hrun,?_,?_,?_,?_,?_⟩
  · rw [hrun];rfl
  · rw [hrun];rfl
  · rw [hrun];simp [finalFrame,CountedZero.finalFrame,CountedZero.frame,MultitapeTM.inTape,nativeBase]
  · rw [hrun];exact houtput
  · rw [hrun];simp [finalFrame,MultitapeTM.outTape]
end IntMul.ZeroCarry


open IntMul IntMul.ZeroCarry

theorem solution (base : machine.Cfg) (z : List Bool) :
    ∃ t : ℕ, t≤ 7*(val z+1)+4*z.length+7 ∧
      machine.step^[t] (initialFrame base z)=finalFrame base z ∧
      (machine.step^[t] (initialFrame base z)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame base z)).cells machine.inTape=base.cells machine.inTape ∧
      (machine.step^[t] (initialFrame base z)).head machine.inTape=base.head machine.inTape ∧
      (machine.step^[t] (initialFrame base z)).cells machine.outTape=
        machine.tapeOf ((bin (val z+1) 0).map machine.bitSym) ∧
      (machine.step^[t] (initialFrame base z)).head machine.outTape=0 :=
  IntMul.ZeroCarry.initialize_zero_carry base z

#print axioms solution
