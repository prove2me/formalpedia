-- Prove2me | solution 1 for IntMul.WidthPreparation.prepare_width
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T13:50:56.499091+00:00
-- url     : https://prove2.me/submissions/1dc481dc-d78e-4d2a-b33f-b5d57acd5d00

import Definitions.Def_IntMul_WidthPreparation
import Mathlib.Tactic

set_option maxHeartbeats 1000000
set_option Elab.async false


namespace IntMul.WidthPreparation

private theorem cfg_ext (c d : machine.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c;cases d;cases hs;cases hc;cases hh;rfl
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem safe_right (s : Sym) : safeStep s s .right=(s,.right) := by
  by_cases hs : s=Sym.start <;> simp [safeStep,hs]

private theorem safe_left (s : Sym) (hs : s≠Sym.start) : safeStep s s .left=(s,.left) := by
  simp [safeStep,hs]

private theorem bit_not_start (b : Bool) : machine.bitSym b≠Sym.start := by cases b <;> decide

private theorem bits_read (w : List Bool) (j : ℕ) (hj : j < w.length) :
    machine.tapeOf (w.map machine.bitSym) (j+1)=machine.bitSym w[j] := by
  change (w.map machine.bitSym).getD j Sym.blank=_
  rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]

private theorem bits_blank (w : List Bool) :
    machine.tapeOf (w.map machine.bitSym) (w.length+1)=Sym.blank := by
  change (w.map machine.bitSym).getD w.length Sym.blank=Sym.blank
  exact List.getD_eq_default _ _ (by simp)

private theorem tape_not_start (w : List Sym) (hw : ∀ a ∈ w, a≠Sym.start) (j : ℕ) :
    machine.tapeOf w (j+1)≠Sym.start := by
  change w.getD j Sym.blank≠Sym.start
  by_cases hj : j < w.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact hw _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    decide

private theorem tape_append_one (w : List Sym) (a : Sym) :
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


end IntMul.WidthPreparation


namespace IntMul.WidthPreparation

private def openFrame (base : machine.Cfg) (d : List Bool) : machine.Cfg :=
  {initialFrame base d with
    state := .open
    head := Function.update (Function.update (Function.update base.head 15 1) 3 1) 4 1}

private def copyFrame (base : machine.Cfg) (d : List Bool) (j : ℕ) : machine.Cfg where
  state := .copy
  cells := Function.update (Function.update (Function.update base.cells 15 (machine.tapeOf (d.map machine.bitSym)))
    3 (machine.tapeOf (TapeCopy.Sym.sep::(d.take j).map machine.bitSym)))
      4 (machine.tapeOf (TapeCopy.Sym.sep::(d.take j).map machine.bitSym))
  head := Function.update (Function.update (Function.update base.head 15 (j+1)) 3 (j+2)) 4 (j+2)

private def rewindFrame (base : machine.Cfg) (d : List Bool) (p : ℕ) : machine.Cfg :=
  {finalFrame base d with
    state := .rewind
    head := Function.update (finalFrame base d).head 15 p}

end IntMul.WidthPreparation


namespace IntMul.WidthPreparation
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem advance_step (base : machine.Cfg) (d : List Bool) :
    machine.step (initialFrame base d)=openFrame base d := by
  let s : Fin 16 → Sym := fun i => (initialFrame base d).cells i ((initialFrame base d).head i)
  have ht : transition .advance s=(.open,fun i => (s i,if i=3 ∨ i=4 ∨ i=15 then Move.right else Move.stay)) := by
    simp only [transition,rawTransition]
    congr 1
    funext i
    by_cases h : i=3 ∨ i=4 ∨ i=15
    · simp only [if_pos h];exact safe_right _
    · simp only [if_neg h];exact safe_stay _
  change transition (initialFrame base d).state
    (fun i => (initialFrame base d).cells i ((initialFrame base d).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [initialFrame,openFrame]

private theorem open_step (base : machine.Cfg) (d : List Bool) :
    machine.step (openFrame base d)=copyFrame base d 0 := by
  let s : Fin 16 → Sym := fun i => (openFrame base d).cells i ((openFrame base d).head i)
  have h3 : s 3=Sym.blank := rfl
  have h4 : s 4=Sym.blank := rfl
  have ht : transition .open s=(.copy,fun i =>
      (if i=3 ∨ i=4 then Sym.sep else s i,if i=3 ∨ i=4 then Move.right else Move.stay)) := by
    simp only [transition,rawTransition]
    congr 1
    funext i
    by_cases h3' : i=3
    · subst i;simp [h3,safeStep]
    · by_cases h4' : i=4
      · subst i;simp [h4,safeStep]
      · have hd : ¬(i=3 ∨ i=4) := fun h => h.elim h3' h4'
        simp only [if_neg hd];exact safe_stay _
  change transition (openFrame base d).state
    (fun i => (openFrame base d).cells i ((openFrame base d).head i))=_ at ht
  have hp : Function.update (machine.tapeOf []) 1 Sym.sep=machine.tapeOf [Sym.sep] := by
    simpa using tape_append_one [] Sym.sep
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [s,openFrame,initialFrame,copyFrame,hp,Function.update_eq_self]
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [openFrame,initialFrame,copyFrame]

end IntMul.WidthPreparation



namespace IntMul.WidthPreparation
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem owned_intmulwidthpreparationcopy_copy_transition (s : Fin 16 → Sym) (b : Bool)
    (hi : s 15=machine.bitSym b) (h3 : s 3=Sym.blank) (h4 : s 4=Sym.blank) :
    transition .copy s=(.copy,fun i =>
      (if i=3 ∨ i=4 then machine.bitSym b else s i,
        if i=3 ∨ i=4 ∨ i=15 then Move.right else Move.stay)) := by
  have hb : s 15=Sym.zero ∨ s 15=Sym.one := by rw [hi];cases b <;> decide
  simp only [transition,rawTransition,if_pos hb]
  congr 1
  funext i
  by_cases h3' : i=3
  · subst i;cases b <;> simp [hi,h3,safeStep,MultitapeTM.bitSym]
  · by_cases h4' : i=4
    · subst i;cases b <;> simp [hi,h4,safeStep,MultitapeTM.bitSym]
    · have hd : ¬(i=3 ∨ i=4) := fun h => h.elim h3' h4'
      simp only [if_neg hd]
      by_cases h15 : i=15
      · subst i;simp only [or_true,if_true];exact safe_right _
      · have hall : ¬(i=3 ∨ i=4 ∨ i=15) := by
          intro h;rcases h with h|h|h
          · exact h3' h
          · exact h4' h
          · exact h15 h
        simp only [if_neg hall];exact safe_stay _

private theorem copy_step (base : machine.Cfg) (d : List Bool) (j : ℕ) (hj : j < d.length) :
    machine.step (copyFrame base d j)=copyFrame base d (j+1) := by
  let s : Fin 16 → Sym := fun i => (copyFrame base d j).cells i ((copyFrame base d j).head i)
  have hi : s 15=machine.bitSym d[j] := bits_read d j hj
  have hl : (Sym.sep::(d.take j).map machine.bitSym).length=j+1 := by simp [Nat.min_eq_left hj.le]
  have h3 : s 3=Sym.blank := by
    change (Sym.sep::(d.take j).map machine.bitSym).getD (j+1) Sym.blank=Sym.blank
    exact List.getD_eq_default _ _ hl.le
  have h4 : s 4=Sym.blank := h3
  have ht := owned_intmulwidthpreparationcopy_copy_transition s d[j] hi h3 h4
  change transition (copyFrame base d j).state
    (fun i => (copyFrame base d j).cells i ((copyFrame base d j).head i))=_ at ht
  have hp : Function.update (machine.tapeOf (Sym.sep::(d.take j).map machine.bitSym))
      (j+2) (machine.bitSym d[j])=machine.tapeOf (Sym.sep::(d.take (j+1)).map machine.bitSym) := by
    have hn : Sym.sep::(d.take (j+1)).map machine.bitSym=
        (Sym.sep::(d.take j).map machine.bitSym)++[machine.bitSym d[j]] := by
      rw [List.take_succ_eq_append_getElem hj,List.map_append]
      rfl
    rw [hn]
    have h := tape_append_one (Sym.sep::(d.take j).map machine.bitSym) (machine.bitSym d[j])
    rw [hl] at h
    simpa only [Nat.add_assoc] using h
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases h3' : i=3
    · subst i;exact hp
    · by_cases h4' : i=4
      · subst i;exact hp
      · simp [s,copyFrame,h3',h4',Function.update_eq_self]
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [copyFrame] <;> omega

private theorem copy_run (base : machine.Cfg) (d : List Bool) (j : ℕ) (hj : j ≤ d.length) :
    machine.step^[j] (copyFrame base d 0)=copyFrame base d j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),copy_step base d j (by omega)]

end IntMul.WidthPreparation



namespace IntMul.WidthPreparation
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem finish_step (base : machine.Cfg) (d : List Bool) :
    machine.step (copyFrame base d d.length)=rewindFrame base d d.length := by
  let s : Fin 16 → Sym := fun i => (copyFrame base d d.length).cells i
    ((copyFrame base d d.length).head i)
  have hi : s 15=Sym.blank := bits_blank d
  have h3 : s 3=Sym.blank := by
    change (Sym.sep::(d.take d.length).map machine.bitSym).getD (d.length+1) Sym.blank=Sym.blank
    exact List.getD_eq_default _ _ (by simp)
  have h4 : s 4=Sym.blank := h3
  have ht : transition .copy s=(.rewind,fun i =>
      (if i=3 ∨ i=4 then Sym.sep else s i,
        if i=3 ∨ i=4 ∨ i=15 then Move.left else Move.stay)) := by
    simp only [transition,rawTransition,hi]
    rw [if_neg (by decide : ¬(Sym.blank=Sym.zero ∨ Sym.blank=Sym.one))]
    congr 1
    funext i
    by_cases h3' : i=3
    · subst i;simp [h3,safeStep]
    · by_cases h4' : i=4
      · subst i;simp [h4,safeStep]
      · have hd : ¬(i=3 ∨ i=4) := fun h => h.elim h3' h4'
        simp only [if_neg hd]
        by_cases h15 : i=15
        · subst i;simp only [or_true,if_true];exact safe_left _ (by rw [hi];decide)
        · have hall : ¬(i=3 ∨ i=4 ∨ i=15) := by
            intro h;rcases h with h|h|h
            · exact h3' h
            · exact h4' h
            · exact h15 h
          simp only [if_neg hall];exact safe_stay _
  change transition (copyFrame base d d.length).state
    (fun i => (copyFrame base d d.length).cells i ((copyFrame base d d.length).head i))=_ at ht
  have hp : Function.update (machine.tapeOf (Sym.sep::d.map machine.bitSym)) (d.length+2) Sym.sep=
      descriptorTape d := by
    simpa [descriptorTape] using tape_append_one (Sym.sep::d.map machine.bitSym) Sym.sep
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases h3' : i=3
    · subst i;simpa [copyFrame,rewindFrame,finalFrame] using hp
    · by_cases h4' : i=4
      · subst i;simpa [copyFrame,rewindFrame,finalFrame] using hp
      · simp [s,copyFrame,rewindFrame,finalFrame,h3',h4',Function.update_eq_self]
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [copyFrame,rewindFrame,finalFrame] <;> omega

private theorem rewind_step (base : machine.Cfg) (d : List Bool) (p : ℕ) :
    machine.step (rewindFrame base d (p+1))=rewindFrame base d p := by
  let s : Fin 16 → Sym := fun i => (rewindFrame base d (p+1)).cells i
    ((rewindFrame base d (p+1)).head i)
  have hi : s 15≠Sym.start := by
    change machine.tapeOf (d.map machine.bitSym) (p+1)≠Sym.start
    apply tape_not_start
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact bit_not_start b
  have ht : transition .rewind s=(.rewind,fun i => (s i,if i=15 then Move.left else Move.stay)) := by
    simp only [transition,rawTransition,if_neg hi]
    congr 1
    funext i
    by_cases h : i=15
    · subst i;simp only [if_true];exact safe_left _ hi
    · simp only [if_neg h];exact safe_stay _
  change transition (rewindFrame base d (p+1)).state
    (fun i => (rewindFrame base d (p+1)).cells i ((rewindFrame base d (p+1)).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [rewindFrame] <;> omega

private theorem rewind_run (base : machine.Cfg) (d : List Bool) (p : ℕ) :
    machine.step^[p] (rewindFrame base d p)=rewindFrame base d 0 := by
  induction p with
  | zero => rfl
  | succ p ih => rw [Function.iterate_succ_apply,rewind_step,ih]

private theorem rewind_halt (base : machine.Cfg) (d : List Bool) :
    machine.step (rewindFrame base d 0)=finalFrame base d := by
  let s : Fin 16 → Sym := fun i => (rewindFrame base d 0).cells i ((rewindFrame base d 0).head i)
  have hi : s 15=Sym.start := rfl
  have ht : transition .rewind s=(.halt,fun i => (s i,Move.stay)) := by
    simp only [transition,rawTransition,hi,if_true,safe_stay]
  change transition (rewindFrame base d 0).state
    (fun i => (rewindFrame base d 0).cells i ((rewindFrame base d 0).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    have hh : (finalFrame base d).head 15=0 := rfl
    change Function.update (finalFrame base d).head 15 0=(finalFrame base d).head
    rw [← hh,Function.update_eq_self]

end IntMul.WidthPreparation



namespace IntMul.WidthPreparation

/-- Complete real preparation of two countdown/template banks from a
retained width descriptor, including both delimiters, rewind and halt. -/
private theorem prepare_width (base : machine.Cfg) (d : List Bool) :
    machine.step^[2*d.length+4] (initialFrame base d)=finalFrame base d ∧
      (machine.step^[2*d.length+4] (initialFrame base d)).state=machine.qHalt := by
  have hs : machine.step^[d.length+2] (initialFrame base d)=copyFrame base d d.length := by
    rw [show d.length+2=(d.length+1)+1 by omega,Function.iterate_succ_apply,
      Function.iterate_succ_apply,advance_step,open_step,copy_run base d d.length (by omega)]
  have hf : machine.step^[d.length+3] (initialFrame base d)=rewindFrame base d d.length := by
    rw [show d.length+3=(d.length+2)+1 by omega,Function.iterate_succ_apply',hs,finish_step]
  have he : machine.step^[2*d.length+4] (initialFrame base d)=finalFrame base d := by
    rw [show 2*d.length+4=1+(d.length+(d.length+3)) by omega,
      Function.iterate_add_apply,Function.iterate_add_apply,hf,rewind_run]
    simpa only [Function.iterate_one] using rewind_halt base d
  exact ⟨he,by rw [he];rfl⟩

end IntMul.WidthPreparation



open IntMul IntMul.WidthPreparation

theorem solution (base : machine.Cfg) (d : List Bool) :
    machine.step^[2*d.length+4] (initialFrame base d)=finalFrame base d ∧
      (machine.step^[2*d.length+4] (initialFrame base d)).state=machine.qHalt :=
  IntMul.WidthPreparation.prepare_width base d

#print axioms solution
