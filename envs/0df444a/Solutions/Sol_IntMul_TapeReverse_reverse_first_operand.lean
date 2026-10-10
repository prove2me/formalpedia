-- Prove2me | solution 1 for IntMul.TapeReverse.reverse_first_operand
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T09:18:09.36644+00:00
-- url     : https://prove2.me/submissions/6ed2cf14-bd69-480f-b026-88dd69b085c9

import Definitions.Def_IntMul_TapeReverse
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

namespace IntMul.TapeReverse

open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem cfg_ext (c d : machine.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem safe_right (s : Sym) : safeStep s s .right=(s,.right) := by
  by_cases h : s=Sym.start <;> simp [safeStep,h]

private theorem tapeOf_append_one (w : List Sym) (a : Sym) :
    Function.update (machine.tapeOf w) (w.length+1) a=machine.tapeOf (w++[a]) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
    by_cases hp : p=w.length
    · subst p
      simp [MultitapeTM.tapeOf]
    · rw [Function.update_of_ne (by omega : p+1≠w.length+1)]
      simp only [MultitapeTM.tapeOf]
      by_cases hlt : p < w.length
      · rw [List.getD_append _ _ _ _ hlt]
      · have hge : w.length ≤ p := by omega
        rw [List.getD_eq_default _ _ hge,List.getD_append_right _ _ _ _ hge]
        exact (List.getD_eq_default _ _ (by simp;omega)).symm

private theorem seek_transition (a : Fin 2 → Sym)
    (hb : a 0=Sym.zero ∨ a 0=Sym.one) :
    transition .seek a=(.seek,fun i => (a i,if i=0 then Move.right else Move.stay)) := by
  simp only [transition,rawTransition,if_pos hb]
  congr 1
  funext i
  fin_cases i
  · exact safe_right _
  · exact safe_stay _

private theorem start_step (x y : List Bool) :
    machine.step (machine.initCfg x y)=seekFrame x y 0 := by
  have ht : transition .start (fun i => (machine.initCfg x y).cells i 0)=
      (.seek,fun i => (Sym.start,if i=0 then Move.right else Move.stay)) := by
    simp only [transition,rawTransition]
    congr 1
    funext i
    fin_cases i <;> simp [MultitapeTM.initCfg,MultitapeTM.inTape,MultitapeTM.tapeOf,safeStep]
  change transition (machine.initCfg x y).state
    (fun i => (machine.initCfg x y).cells i ((machine.initCfg x y).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> exact Function.update_eq_self 0 _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> rfl

private theorem seek_step (x y : List Bool) (j : ℕ) (hj : j < x.length) :
    machine.step (seekFrame x y j)=seekFrame x y (j+1) := by
  have hinput : (seekFrame x y j).cells 0 ((seekFrame x y j).head 0)=machine.bitSym x[j] := by
    change (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD j Sym.blank=_
    rw [List.getD_append _ _ _ _ (by simpa using hj),
      List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]
  have hb : (seekFrame x y j).cells 0 ((seekFrame x y j).head 0)=Sym.zero ∨
      (seekFrame x y j).cells 0 ((seekFrame x y j).head 0)=Sym.one := by
    rw [hinput]
    cases x[j] <;> decide
  have ht := seek_transition (fun i => (seekFrame x y j).cells i ((seekFrame x y j).head i)) hb
  change transition (seekFrame x y j).state
    (fun i => (seekFrame x y j).cells i ((seekFrame x y j).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [seekFrame]

private theorem seek_run (x y : List Bool) (j : ℕ) (hj : j ≤ x.length) :
    machine.step^[j+1] (machine.initCfg x y)=seekFrame x y j := by
  induction j with
  | zero => simpa using start_step x y
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),seek_step x y j (by omega)]

private theorem turn_step (x y : List Bool) :
    machine.step (seekFrame x y x.length)=frame x y x.length .copy := by
  have hsep : (seekFrame x y x.length).cells 0 ((seekFrame x y x.length).head 0)=Sym.sep := by
    change (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD x.length Sym.blank=_
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have ht : transition .seek (fun i => (seekFrame x y x.length).cells i
      ((seekFrame x y x.length).head i))=
      (.copy,fun i => ((seekFrame x y x.length).cells i ((seekFrame x y x.length).head i),
        if i=0 then Move.left else Move.right)) := by
    simp only [transition,rawTransition,hsep]
    simp only [if_neg (by decide : ¬(Sym.sep=Sym.zero ∨ Sym.sep=Sym.one)),ite_true]
    congr 1
    funext i
    fin_cases i
    · simp [hsep,safeStep]
    · exact safe_right _
  change transition (seekFrame x y x.length).state
    (fun i => (seekFrame x y x.length).cells i ((seekFrame x y x.length).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    fin_cases i <;> simp [seekFrame,frame]
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [seekFrame,frame]

private theorem copy_transition (a : Fin 2 → Sym) (b : Bool)
    (hi : a 0=machine.bitSym b) (ho : a 1=Sym.blank) :
    transition .copy a=(.copy,fun i => (machine.bitSym b,if i=0 then Move.left else Move.right)) := by
  have hb : a 0=Sym.zero ∨ a 0=Sym.one := by rw [hi]; cases b <;> decide
  simp only [transition,rawTransition,if_pos hb]
  congr 1
  funext i
  fin_cases i
  · cases b <;> simp [hi,safeStep,MultitapeTM.bitSym]
  · cases b <;> simp [ho,hi,safeStep,MultitapeTM.bitSym]

private theorem copy_step (x y : List Bool) (j : ℕ) (hj : j+1 ≤ x.length) :
    machine.step (frame x y (j+1) .copy)=frame x y j .copy := by
  have hinput : (frame x y (j+1) .copy).cells 0 ((frame x y (j+1) .copy).head 0)=
      machine.bitSym x[j] := by
    change (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD j Sym.blank=_
    rw [List.getD_append _ _ _ _ (by simp;omega),
      List.getD_eq_getElem _ _ (by simp;omega),List.getElem_map]
  have hlen : ((x.drop (j+1)).reverse.map machine.bitSym).length=x.length-(j+1) := by simp
  have hout : (frame x y (j+1) .copy).cells 1 ((frame x y (j+1) .copy).head 1)=Sym.blank := by
    change ((x.drop (j+1)).reverse.map machine.bitSym).getD (x.length-(j+1)) Sym.blank=Sym.blank
    exact List.getD_eq_default _ _ hlen.le
  have ht := copy_transition (fun i => (frame x y (j+1) .copy).cells i
    ((frame x y (j+1) .copy).head i)) x[j] hinput hout
  change transition (frame x y (j+1) .copy).state
    (fun i => (frame x y (j+1) .copy).cells i ((frame x y (j+1) .copy).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · rw [←hinput]
      exact Function.update_eq_self _ _
    · change Function.update (machine.tapeOf ((x.drop (j+1)).reverse.map machine.bitSym))
        (x.length-(j+1)+1) (machine.bitSym x[j])=machine.tapeOf ((x.drop j).reverse.map machine.bitSym)
      have hdrop : x.drop j=x[j]::x.drop (j+1) := List.drop_eq_getElem_cons (by omega)
      rw [hdrop,List.reverse_cons,List.map_append,List.map_singleton]
      have hw := tapeOf_append_one ((x.drop (j+1)).reverse.map machine.bitSym) (machine.bitSym x[j])
      rw [hlen] at hw
      exact hw
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [frame]
    omega

private theorem copy_run (x y : List Bool) (j : ℕ) (hj : j ≤ x.length) :
    machine.step^[j] (frame x y j .copy)=frame x y 0 .copy := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply,copy_step x y j hj,ih (by omega)]

private theorem halt_step (x y : List Bool) :
    machine.step (frame x y 0 .copy)=frame x y 0 .halt := by
  have hi : (frame x y 0 .copy).cells 0 ((frame x y 0 .copy).head 0)=Sym.start := rfl
  have ht : transition .copy (fun i => (frame x y 0 .copy).cells i ((frame x y 0 .copy).head i))=
      (.halt,fun i => ((frame x y 0 .copy).cells i ((frame x y 0 .copy).head i),Move.stay)) := by
    simp only [transition,rawTransition,hi]
    rw [if_neg (by decide : ¬(Sym.start=Sym.zero ∨ Sym.start=Sym.one))]
    simp only [safe_stay]
  change transition (frame x y 0 .copy).state
    (fun i => (frame x y 0 .copy).cells i ((frame x y 0 .copy).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    rfl

/-- One fixed two-tape, five-symbol, four-state machine reverses its first
operand in exactly 2|x|+3 transitions, with the full terminal frame proved. -/
private theorem reverse_first_operand (x y : List Bool) :
    machine.HaltsWithOutput x y (2*x.length+3) x.reverse ∧
      machine.step^[2*x.length+3] (machine.initCfg x y)=frame x y 0 .halt := by
  have he : machine.step^[2*x.length+3] (machine.initCfg x y)=frame x y 0 .halt := by
    have hsetup : machine.step^[x.length+2] (machine.initCfg x y)=frame x y x.length .copy := by
      rw [show x.length+2=(x.length+1)+1 by omega,Function.iterate_succ_apply',
        seek_run x y x.length le_rfl,turn_step]
    rw [show 2*x.length+3=1+(x.length+(x.length+2)) by omega,
      Function.iterate_add_apply,Function.iterate_add_apply,hsetup,copy_run x y x.length le_rfl,
      Function.iterate_one,halt_step]
  refine ⟨?_,he⟩
  unfold MultitapeTM.HaltsWithOutput
  rw [he]
  exact ⟨rfl,rfl⟩

end IntMul.TapeReverse


open IntMul.TapeReverse

theorem solution (x y : List Bool) :
    machine.HaltsWithOutput x y (2*x.length+3) x.reverse ∧
      machine.step^[2*x.length+3] (machine.initCfg x y)=frame x y 0 .halt :=
  IntMul.TapeReverse.reverse_first_operand x y

#print axioms solution
