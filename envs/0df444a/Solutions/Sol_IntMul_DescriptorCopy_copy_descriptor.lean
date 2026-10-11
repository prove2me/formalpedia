-- Prove2me | solution 1 for IntMul.DescriptorCopy.copy_descriptor
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T17:36:28.007985+00:00
-- url     : https://prove2.me/submissions/2df75d58-42f1-42a8-8a99-12445914c823

import Definitions.Def_IntMul_DescriptorCopy
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic
namespace IntMul.DescriptorCopy
open TapeCopy (Sym)
private theorem cfg_ext (c d : machine.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c;cases d;cases hs;cases hc;cases hh;rfl
private theorem tape_append (M : MultitapeTM) (w : List M.Sym) (a : M.Sym) :
    Function.update (M.tapeOf w) (w.length + 1) a = M.tapeOf (w ++ [a]) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
      by_cases hp : p = w.length
      · subst p
        simp [MultitapeTM.tapeOf, List.getD_append_right]
      · have hne : p + 1 ≠ w.length + 1 := by omega
        rw [Function.update_of_ne hne]
        simp only [MultitapeTM.tapeOf]
        by_cases hlt : p < w.length
        · rw [List.getD_append _ _ _ _ hlt]
        · have hge : w.length ≤ p := by omega
          rw [List.getD_eq_default _ _ hge, List.getD_append_right _ _ _ _ hge]
          exact (List.getD_eq_default _ _ (by simp; omega)).symm

private theorem safe_right (s : Sym) : TapeAdder.safeStep s s .right=(s,.right) := by
  by_cases h : s=Sym.start <;> simp [TapeAdder.safeStep,h]
private theorem safe_bit_write (b : Bool) :
    TapeAdder.safeStep Sym.blank (machine.bitSym b) .right=(machine.bitSym b,.right) := by
  cases b <;> decide
private theorem bits_not_start (w : List Bool) (j : ℕ) :
    machine.tapeOf (w.map machine.bitSym) (j+1)≠Sym.start := by
  change (w.map machine.bitSym).getD j Sym.blank≠Sym.start
  by_cases h : j<(w.map machine.bitSym).length
  · rw [List.getD_eq_getElem _ _ h,List.getElem_map]
    have hj : j<w.length := by simpa only [List.length_map] using h
    cases w[j] <;> decide
  · rw [List.getD_eq_default _ _ (by omega)];decide
private theorem open_step (base : machine.Cfg) (w : List Bool) :
    machine.step (initialFrame base w)=copyFrame base w 0 := by
  have ht : transition (initialFrame base w).state
      (fun i => (initialFrame base w).cells i ((initialFrame base w).head i))=
      (.copy,fun i => ((initialFrame base w).cells i ((initialFrame base w).head i),
        if i=1 ∨ i=2 then Move.right else Move.stay)) := by
    simp only [initialFrame,transition,rawTransition]
    congr 1;funext i;fin_cases i
    · exact TapeAdder.safe_stay _
    · exact safe_right _
    · exact safe_right _
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];funext i;rw [Function.update_eq_self]
    fin_cases i <;> simp [initialFrame,copyFrame]
  · simp only [MultitapeTM.step,ht];funext i;fin_cases i <;> simp [initialFrame,copyFrame]
private theorem copy_step (base : machine.Cfg) (w : List Bool) (j : ℕ) (hj : j<w.length) :
    machine.step (copyFrame base w j)=copyFrame base w (j+1) := by
  let a : Fin 3 → Sym := fun i => (copyFrame base w j).cells i ((copyFrame base w j).head i)
  have hread : a 1=machine.bitSym w[j] := by
    change (w.map machine.bitSym).getD j machine.blank=_
    rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]
  have hlen : ((w.take j).map machine.bitSym).length=j := by simp [Nat.min_eq_left hj.le]
  have hblank : a 2=Sym.blank := by
    change ((w.take j).map machine.bitSym).getD j machine.blank=_
    exact List.getD_eq_default _ _ hlen.le
  have hbit : a 1=Sym.zero ∨ a 1=Sym.one := by rw [hread];cases w[j] <;> decide
  have ht : transition .copy a=(.copy,fun i =>
      (if i=2 then a 1 else a i,if i=1 ∨ i=2 then Move.right else Move.stay)) := by
    simp only [transition,rawTransition,if_pos hbit]
    congr 1;funext i;fin_cases i
    · exact TapeAdder.safe_stay _
    · exact safe_right _
    · change TapeAdder.safeStep (a 2) (a 1) Move.right=(a 1,Move.right)
      rw [hblank,hread];exact safe_bit_write w[j]
  change transition (copyFrame base w j).state
    (fun i => (copyFrame base w j).cells i ((copyFrame base w j).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];funext i;fin_cases i
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · change Function.update (machine.tapeOf ((w.take j).map machine.bitSym)) (j+1)
        (a 1)=machine.tapeOf ((w.take (j+1)).map machine.bitSym)
      rw [hread,List.take_succ_eq_append_getElem hj,List.map_append]
      have h := tape_append machine ((w.take j).map machine.bitSym) (machine.bitSym w[j])
      rw [hlen] at h;exact h
  · simp only [MultitapeTM.step,ht];funext i;fin_cases i <;> simp [copyFrame]
private theorem copy_run (base : machine.Cfg) (w : List Bool) (j : ℕ) (hj : j≤w.length) :
    machine.step^[j] (copyFrame base w 0)=copyFrame base w j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),copy_step base w j (by omega)]
private theorem end_step (base : machine.Cfg) (w : List Bool) :
    machine.step (copyFrame base w w.length)=rewindFrame base w w.length := by
  let a : Fin 3 → Sym := fun i => (copyFrame base w w.length).cells i ((copyFrame base w w.length).head i)
  have hr : a 1=Sym.blank := by
    change (w.map machine.bitSym).getD w.length machine.blank=_
    exact List.getD_eq_default _ _ (by simp)
  have h2 : a 2=Sym.blank := by
    change ((w.take w.length).map machine.bitSym).getD w.length machine.blank=_
    exact List.getD_eq_default _ _ (by simp)
  have ht : transition .copy a=(.rewind,fun i => (a i,if i=1 ∨ i=2 then Move.left else Move.stay)) := by
    simp only [transition,rawTransition,hr]
    rw [if_neg (by decide : ¬(Sym.blank=Sym.zero ∨ Sym.blank=Sym.one))]
    congr 1;funext i;fin_cases i
    · exact TapeAdder.safe_stay _
    · simp [TapeAdder.safeStep,hr]
    · simp [TapeAdder.safeStep,h2]
  change transition (copyFrame base w w.length).state
    (fun i => (copyFrame base w w.length).cells i ((copyFrame base w w.length).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];funext i;rw [Function.update_eq_self]
    fin_cases i <;> simp [copyFrame,rewindFrame]
  · simp only [MultitapeTM.step,ht];funext i;fin_cases i <;> simp [copyFrame,rewindFrame]
private theorem rewind_step (base : machine.Cfg) (w : List Bool) (p : ℕ) :
    machine.step (rewindFrame base w (p+1))=rewindFrame base w p := by
  let a : Fin 3 → Sym := fun i => (rewindFrame base w (p+1)).cells i ((rewindFrame base w (p+1)).head i)
  have hn : a 1≠Sym.start := bits_not_start w p
  have h2 : a 2≠Sym.start := bits_not_start w p
  have ht : transition .rewind a=(.rewind,fun i => (a i,if i=1 ∨ i=2 then Move.left else Move.stay)) := by
    simp only [transition,rawTransition,if_neg hn]
    congr 1;funext i;fin_cases i
    · exact TapeAdder.safe_stay _
    · simp [TapeAdder.safeStep,hn]
    · simp [TapeAdder.safeStep,h2]
  change transition (rewindFrame base w (p+1)).state
    (fun i => (rewindFrame base w (p+1)).cells i ((rewindFrame base w (p+1)).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];funext i;fin_cases i <;> simp [rewindFrame]
private theorem rewind_halt (base : machine.Cfg) (w : List Bool) :
    machine.step (rewindFrame base w 0)=finalFrame base w := by
  have ht : transition (rewindFrame base w 0).state
      (fun i => (rewindFrame base w 0).cells i ((rewindFrame base w 0).head i))=
      (.halt,fun i => ((rewindFrame base w 0).cells i ((rewindFrame base w 0).head i),Move.stay)) := by
    simp [rewindFrame,transition,rawTransition,TapeAdder.safe_stay,MultitapeTM.tapeOf]
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];rfl
private theorem rewind_run (base : machine.Cfg) (w : List Bool) (p : ℕ) :
    machine.step^[p+1] (rewindFrame base w p)=finalFrame base w := by
  induction p with
  | zero => rw [Function.iterate_one,rewind_halt]
  | succ p ih => rw [Function.iterate_succ_apply,rewind_step,ih]
private theorem copy_descriptor (base : machine.Cfg) (w : List Bool) :
    machine.step^[2*w.length+3] (initialFrame base w)=finalFrame base w ∧
      (machine.step^[2*w.length+3] (initialFrame base w)).state=machine.qHalt ∧
      (machine.step^[2*w.length+3] (initialFrame base w)).cells machine.inTape=base.cells machine.inTape ∧
      (machine.step^[2*w.length+3] (initialFrame base w)).head machine.inTape=base.head machine.inTape ∧
      (machine.step^[2*w.length+3] (initialFrame base w)).cells 1=machine.tapeOf (w.map machine.bitSym) ∧
      (machine.step^[2*w.length+3] (initialFrame base w)).cells 2=machine.tapeOf (w.map machine.bitSym) ∧
      (machine.step^[2*w.length+3] (initialFrame base w)).head 1=0 ∧
      (machine.step^[2*w.length+3] (initialFrame base w)).head 2=0 := by
  have hcopy : machine.step^[w.length+1] (initialFrame base w)=copyFrame base w w.length := by
    rw [Function.iterate_succ_apply,open_step,copy_run base w w.length le_rfl]
  have hend : machine.step^[w.length+2] (initialFrame base w)=rewindFrame base w w.length := by
    rw [show w.length+2=(w.length+1)+1 by omega,Function.iterate_succ_apply',hcopy,end_step]
  have he : machine.step^[2*w.length+3] (initialFrame base w)=finalFrame base w := by
    rw [show 2*w.length+3=(w.length+1)+(w.length+2) by omega,Function.iterate_add_apply,hend,rewind_run]
  refine ⟨he,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals rw [he]
  all_goals first | rfl | (simp [finalFrame,rewindFrame,MultitapeTM.inTape])
end IntMul.DescriptorCopy

open IntMul IntMul.DescriptorCopy

theorem solution (base : machine.Cfg) (w : List Bool) :
    machine.step^[2*w.length+3] (initialFrame base w)=finalFrame base w ∧
      (machine.step^[2*w.length+3] (initialFrame base w)).state=machine.qHalt ∧
      (machine.step^[2*w.length+3] (initialFrame base w)).cells machine.inTape=base.cells machine.inTape ∧
      (machine.step^[2*w.length+3] (initialFrame base w)).head machine.inTape=base.head machine.inTape ∧
      (machine.step^[2*w.length+3] (initialFrame base w)).cells 1=machine.tapeOf (w.map machine.bitSym) ∧
      (machine.step^[2*w.length+3] (initialFrame base w)).cells 2=machine.tapeOf (w.map machine.bitSym) ∧
      (machine.step^[2*w.length+3] (initialFrame base w)).head 1=0 ∧
      (machine.step^[2*w.length+3] (initialFrame base w)).head 2=0 :=
  IntMul.DescriptorCopy.copy_descriptor base w

#print axioms solution
