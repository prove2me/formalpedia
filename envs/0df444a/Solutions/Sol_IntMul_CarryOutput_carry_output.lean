-- Prove2me | solution 1 for IntMul.CarryOutput.carry_output
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T13:05:42.676019+00:00
-- url     : https://prove2.me/submissions/c602ceae-5f31-46e1-9622-a3cbc27bfd53

import Definitions.Def_IntMul_CarryOutput
import Mathlib.Tactic
import Definitions.Def_IntMul_CarryNormalization
import Theorems.Thm_IntMul_CarryBatch_carry_batch
import Theorems.Thm_IntMul_CanonicalOutput_canonical_output
import Theorems.Thm_IntMul_FiniteCaller_simulate_run

set_option maxHeartbeats 1000000
set_option Elab.async false


namespace IntMul.CarryOutput

private theorem cfg_ext (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c;cases d;cases hs;cases hc;cases hh;rfl

private theorem batch_step (c : CarryBatch.machine.Cfg) :
    subroutine.step (batchView c)=batchView (CarryBatch.machine.step c) := by
  let a : Fin 15 → TapeCopy.Sym := fun i => c.cells i (c.head i)
  have ht : transition (batchState c.state) a=
      (batchState (CarryBatch.machine.δ c.state a).1,(CarryBatch.machine.δ c.state a).2) := by
    by_cases h : c.state=CarryBatch.machine.qHalt
    · rw [h,CarryBatch.machine.halt_fixed a]
      rfl
    · conv_lhs => rw [batchState,if_neg h]
      rfl
  change transition (batchView c).state
    (fun i => (batchView c).cells i ((batchView c).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl

private theorem batch_run (c : CarryBatch.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (batchView c)=batchView (CarryBatch.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,batch_step,Function.iterate_succ_apply']

private theorem output_step (c : CanonicalOutput.machine.Cfg) :
    subroutine.step (outputView c)=outputView (CanonicalOutput.machine.step c) := by
  let a : Fin 15 → TapeCopy.Sym := fun i => c.cells i (c.head i)
  have ht : transition (outputState c.state) a=
      (outputState (CanonicalOutput.machine.δ c.state a).1,(CanonicalOutput.machine.δ c.state a).2) := by
    by_cases h : c.state=CanonicalOutput.machine.qHalt
    · rw [h,CanonicalOutput.machine.halt_fixed a]
      rfl
    · conv_lhs => rw [outputState,if_neg h]
      rfl
  change transition (outputView c).state
    (fun i => (outputView c).cells i ((outputView c).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl

private theorem output_run (c : CanonicalOutput.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (outputView c)=outputView (CanonicalOutput.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,output_step,Function.iterate_succ_apply']

end IntMul.CarryOutput



namespace IntMul.CarryOutput

private theorem output_ready (pre : List Bool) (xs : List (List Bool)) (a y z l : List Bool) :
    (CanonicalOutput.initialFrame (outputBase pre xs a y z l)
      (a++(CarryBatch.scanWords z xs y).1)).cells=
      (CarryBatch.finalFrame pre xs a y z l).cells ∧
    (CanonicalOutput.initialFrame (outputBase pre xs a y z l)
      (a++(CarryBatch.scanWords z xs y).1)).head=
      (CarryBatch.finalFrame pre xs a y z l).head := by
  have hc1 : (outputBase pre xs a y z l).cells 1=
      CanonicalOutput.machine.tapeOf
        ((a++(CarryBatch.scanWords z xs y).1).map CanonicalOutput.machine.bitSym) := rfl
  have hc2 : (outputBase pre xs a y z l).cells 2=CanonicalOutput.machine.tapeOf [] := rfl
  have hh1 : (outputBase pre xs a y z l).head 1=
      (a++(CarryBatch.scanWords z xs y).1).length+1 := by
    simp [outputBase,CarryBatch.finalFrame]
  have hh2 : (outputBase pre xs a y z l).head 2=0 := rfl
  constructor
  · change Function.update (Function.update (outputBase pre xs a y z l).cells 1 _)
      2 _=(outputBase pre xs a y z l).cells
    rw [← hc1,Function.update_eq_self,← hc2,Function.update_eq_self]
  · change Function.update (Function.update (outputBase pre xs a y z l).head 1 _)
      2 _=(outputBase pre xs a y z l).head
    rw [← hh1,Function.update_eq_self,← hh2,Function.update_eq_self]

private theorem after_batch (pre : List Bool) (xs : List (List Bool)) (a y z l : List Bool) :
    FiniteCaller.returned subroutine Phase .carry .carry dispatch
      (batchView (CarryBatch.finalFrame pre xs a y z l))=
    FiniteCaller.embed subroutine Phase .carry .order dispatch
      (outputView (CanonicalOutput.initialFrame (outputBase pre xs a y z l)
        (a++(CarryBatch.scanWords z xs y).1))) := by
  have hr := output_ready pre xs a y z l
  apply cfg_ext
  · rfl
  · exact hr.1.symm
  · exact hr.2.symm

private theorem after_output (pre : List Bool) (xs : List (List Bool)) (a y z l : List Bool) :
    FiniteCaller.returned subroutine Phase .carry .order dispatch
      (outputView (CanonicalOutput.finalFrame (outputBase pre xs a y z l)
        (a++(CarryBatch.scanWords z xs y).1)))=finalFrame pre xs a y z l := by
  apply cfg_ext <;> rfl

end IntMul.CarryOutput



namespace IntMul.CarryOutput

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

end IntMul.CarryOutput



namespace IntMul.CarryOutput

/-- A complete physical carry pass with big-endian output return, retained
final carry and linear charged clock. Preparation remains an explicit caller
frame; all two-stage copies, erasures and finite caller returns are paid. -/
private theorem carry_output (pre : List Bool) (xs : List (List Bool)) (a y z l : List Bool)
    (hy : y.length=val l+1) (hx : ∀ w ∈ xs, w.length=val l+1)
    (hB : CarryStep.blockSize z ≤ val l+2) :
    ∃ t : ℕ,
      t ≤ xs.length*(41*(val l+1)+21*CarryStep.blockSize z+21*z.length+4*l.length+126)+8*a.length+21 ∧
      machine.step^[t] (initialFrame pre xs a y z l)=finalFrame pre xs a y z l ∧
      (machine.step^[t] (initialFrame pre xs a y z l)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame pre xs a y z l)).cells 1=
        machine.tapeOf
          ((a++(CarryNormalization.scan (2^CarryStep.blockSize z)
            (xs.map val) (val y)).1.flatMap
              (fun d => (bin (CarryStep.blockSize z) d).reverse)).reverse.map machine.bitSym) ∧
      val (CarryBatch.scanWords z xs y).2=
        (CarryNormalization.scan (2^CarryStep.blockSize z) (xs.map val) (val y)).2 := by
  obtain ⟨u,hu,heu,hhu,hbits,hcarry⟩ := CarryBatch.carry_batch pre xs a y z l hy hx hB
  have hnative : subroutine.step^[u] (batchView (CarryBatch.initialFrame pre xs a y z l))=
      batchView (CarryBatch.finalFrame pre xs a y z l) := by rw [batch_run,heu]
  obtain ⟨s,hs,hes⟩ := (FiniteCaller.simulate_run subroutine Phase .carry .carry dispatch
    (batchView (CarryBatch.initialFrame pre xs a y z l)) u).2 (by rw [hnative];rfl)
  rw [hnative,after_batch] at hes
  obtain ⟨v,hv,hev,hhv⟩ := CanonicalOutput.canonical_output (outputBase pre xs a y z l)
    (a++(CarryBatch.scanWords z xs y).1)
  have horder : subroutine.step^[v]
      (outputView (CanonicalOutput.initialFrame (outputBase pre xs a y z l)
        (a++(CarryBatch.scanWords z xs y).1)))=
      outputView (CanonicalOutput.finalFrame (outputBase pre xs a y z l)
        (a++(CarryBatch.scanWords z xs y).1)) := by rw [output_run,hev]
  obtain ⟨r,hr,her⟩ := (FiniteCaller.simulate_run subroutine Phase .carry .order dispatch
    (outputView (CanonicalOutput.initialFrame (outputBase pre xs a y z l)
      (a++(CarryBatch.scanWords z xs y).1))) v).2 (by rw [horder];rfl)
  rw [horder,after_output] at her
  have he : machine.step^[r+s] (initialFrame pre xs a y z l)=finalFrame pre xs a y z l := by
    rw [Function.iterate_add_apply]
    change machine.step^[r]
      (machine.step^[s] (FiniteCaller.embed subroutine Phase .carry .carry dispatch
        (batchView (CarryBatch.initialFrame pre xs a y z l))))=_
    rw [hes,her]
  have hlen := scan_length z xs y (val l+1) hx (by omega)
  refine ⟨r+s,?_,he,?_,?_,hcarry⟩
  · rw [List.length_append,hlen] at hv
    nlinarith
  · rw [he];rfl
  · rw [he]
    change (CanonicalOutput.finalFrame (outputBase pre xs a y z l)
      (a++(CarryBatch.scanWords z xs y).1)).cells 1=_
    simp only [CanonicalOutput.finalFrame,Function.update_of_ne (by decide : (1 : Fin 15)≠2),Function.update_self]
    rw [hbits]
    rfl

end IntMul.CarryOutput



open IntMul IntMul.CarryOutput

theorem solution (pre : List Bool) (xs : List (List Bool)) (a y z l : List Bool)
    (hy : y.length=val l+1) (hx : ∀ w ∈ xs, w.length=val l+1)
    (hB : CarryStep.blockSize z ≤ val l+2) :
    ∃ t : ℕ,
      t ≤ xs.length*(41*(val l+1)+21*CarryStep.blockSize z+21*z.length+4*l.length+126)+8*a.length+21 ∧
      machine.step^[t] (initialFrame pre xs a y z l)=finalFrame pre xs a y z l ∧
      (machine.step^[t] (initialFrame pre xs a y z l)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame pre xs a y z l)).cells 1=
        machine.tapeOf
          ((a++(CarryNormalization.scan (2^CarryStep.blockSize z)
            (xs.map val) (val y)).1.flatMap
              (fun d => (bin (CarryStep.blockSize z) d).reverse)).reverse.map machine.bitSym) ∧
      val (CarryBatch.scanWords z xs y).2=
        (CarryNormalization.scan (2^CarryStep.blockSize z) (xs.map val) (val y)).2 :=
  IntMul.CarryOutput.carry_output pre xs a y z l hy hx hB

#print axioms solution
