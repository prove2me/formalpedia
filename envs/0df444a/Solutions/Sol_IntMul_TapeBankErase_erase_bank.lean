-- Prove2me | solution 1 for IntMul.TapeBankErase.erase_bank
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T11:54:21.63699+00:00
-- url     : https://prove2.me/submissions/e336eda4-12e8-41cd-9822-44e4128a0891

import Definitions.Def_IntMul_TapeBankErase
import Mathlib.Tactic


namespace IntMul.TapeBankErase
open TapeCopy (Sym)

private theorem cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c;cases d;cases hs;cases hc;cases hh;rfl

private def erasedTape (w : List Sym) (j p : ℕ) : Sym :=
  if p=0 then .start else if p ≤ j then .blank else w.getD (p-1) .blank

private def sweepFrame (m : ℕ) (bank : Fin (m+2)) (hb : 1 ≤ bank.val)
    (base : (machine m bank hb).Cfg) (w : List Sym) (j : ℕ) : (machine m bank hb).Cfg where
  state := .sweep
  cells := Function.update base.cells bank (erasedTape w j)
  head := Function.update base.head bank (j+1)

private def restoreFrame (m : ℕ) (bank : Fin (m+2)) (hb : 1 ≤ bank.val)
    (base : (machine m bank hb).Cfg) (j : ℕ) : (machine m bank hb).Cfg where
  state := .restore
  cells := Function.update base.cells bank ((machine m bank hb).tapeOf [])
  head := Function.update base.head bank j

private theorem erased_zero (m : ℕ) (bank : Fin (m+2)) (hb : 1 ≤ bank.val) (w : List Sym) :
    erasedTape w 0=(machine m bank hb).tapeOf w := by
  funext p
  cases p with
  | zero => rfl
  | succ p => simp [erasedTape,MultitapeTM.tapeOf]

private theorem erased_full (m : ℕ) (bank : Fin (m+2)) (hb : 1 ≤ bank.val) (w : List Sym) :
    erasedTape w w.length=(machine m bank hb).tapeOf [] := by
  funext p
  cases p with
  | zero => rfl
  | succ p =>
    change (if p+1=0 then Sym.start else if p+1 ≤ w.length then Sym.blank
      else w.getD (p+1-1) Sym.blank)=Sym.blank
    rw [if_neg (by omega)]
    by_cases hp : p+1 ≤ w.length
    · rw [if_pos hp]
    · rw [if_neg hp,List.getD_eq_default _ _ (by omega)]

private theorem erased_current (w : List Sym) (j : ℕ) :
    erasedTape w j (j+1)=w.getD j Sym.blank := by
  simp [erasedTape]

private theorem erased_next (w : List Sym) (j : ℕ) :
    Function.update (erasedTape w j) (j+1) Sym.blank=erasedTape w (j+1) := by
  funext p
  cases p with
  | zero =>
    rw [Function.update_of_ne (by omega : 0≠j+1)]
    rfl
  | succ p =>
    by_cases hp : p=j
    · subst p
      simp [erasedTape]
    · rw [Function.update_of_ne (by omega : p+1≠j+1)]
      simp only [erasedTape,show p+1≠0 by omega,if_false]
      by_cases hj : p < j
      · rw [if_pos (by omega : p+1 ≤ j),if_pos (by omega : p+1 ≤ j+1)]
      · rw [if_neg (by omega : ¬p+1 ≤ j),if_neg (by omega : ¬p+1 ≤ j+1)]

private theorem word_not_start (w : List Sym) (hw : ValidWord w) (j : ℕ) :
    w.getD j Sym.blank≠Sym.start := by
  by_cases hj : j < w.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact (hw _ (List.getElem_mem hj)).1
  · rw [List.getD_eq_default _ _ (by omega)]
    decide

private theorem word_nonblank (w : List Sym) (hw : ValidWord w) (j : ℕ) (hj : j < w.length) :
    w.getD j Sym.blank≠Sym.blank := by
  rw [List.getD_eq_getElem _ _ hj]
  exact (hw _ (List.getElem_mem hj)).2

private theorem tape_not_start (m : ℕ) (bank : Fin (m+2)) (hb : 1 ≤ bank.val)
    (w : List Sym) (hw : ValidWord w) (j : ℕ) :
    (machine m bank hb).tapeOf w (j+1)≠Sym.start := word_not_start w hw j

end IntMul.TapeBankErase



namespace IntMul.TapeBankErase
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem safe_right (s : Sym) : safeStep s s .right=(s,.right) := by
  by_cases hs : s=Sym.start <;> simp [safeStep,hs]

private theorem safe_left (s : Sym) (hs : s≠Sym.start) : safeStep s s .left=(s,.left) := by
  simp [safeStep,hs]

private theorem rewind_step (m : ℕ) (bank : Fin (m+2)) (hb : 1 ≤ bank.val)
    (base : (machine m bank hb).Cfg) (w : List Sym) (hw : ValidWord w) (j : ℕ) :
    (machine m bank hb).step (initialFrame m bank hb base w (j+1))=
      initialFrame m bank hb base w j := by
  let a : Fin (m+2) → Sym := fun i => (initialFrame m bank hb base w (j+1)).cells i
    ((initialFrame m bank hb base w (j+1)).head i)
  have ho : a bank≠Sym.start := by
    simpa only [a,initialFrame,Function.update_self] using tape_not_start m bank hb w hw j
  have ht : transition m bank .rewind a=(.rewind,
      fun i => (a i,if i=bank then Move.left else Move.stay)) := by
    simp only [transition,rawTransition,if_neg ho]
    congr 1
    funext i
    by_cases hi : i=bank
    · simp only [hi,if_true]
      exact safe_left _ ho
    · simp only [if_neg hi]
      exact safe_stay _
  change transition m bank (initialFrame m bank hb base w (j+1)).state
    (fun i => (initialFrame m bank hb base w (j+1)).cells i
      ((initialFrame m bank hb base w (j+1)).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=bank <;> simp [initialFrame,hi]

private theorem rewind_run (m : ℕ) (bank : Fin (m+2)) (hb : 1 ≤ bank.val)
    (base : (machine m bank hb).Cfg) (w : List Sym) (hw : ValidWord w) (j : ℕ) :
    (machine m bank hb).step^[j] (initialFrame m bank hb base w j)=
      initialFrame m bank hb base w 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply,rewind_step m bank hb base w hw,ih]

private theorem rewind_open_step (m : ℕ) (bank : Fin (m+2)) (hb : 1 ≤ bank.val)
    (base : (machine m bank hb).Cfg) (w : List Sym) :
    (machine m bank hb).step (initialFrame m bank hb base w 0)=sweepFrame m bank hb base w 0 := by
  let a : Fin (m+2) → Sym := fun i => (initialFrame m bank hb base w 0).cells i
    ((initialFrame m bank hb base w 0).head i)
  have ho : a bank=Sym.start := by simp [a,initialFrame,MultitapeTM.tapeOf]
  have ht : transition m bank .rewind a=(.sweep,
      fun i => (a i,if i=bank then Move.right else Move.stay)) := by
    simp only [transition,rawTransition,if_pos ho]
    congr 1
    funext i
    by_cases hi : i=bank
    · simp only [hi,if_true]
      exact safe_right _
    · simp only [if_neg hi]
      exact safe_stay _
  change transition m bank (initialFrame m bank hb base w 0).state
    (fun i => (initialFrame m bank hb base w 0).cells i
      ((initialFrame m bank hb base w 0).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    simp only [initialFrame,sweepFrame]
    rw [erased_zero m bank hb w]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=bank <;> simp [initialFrame,sweepFrame,hi]

end IntMul.TapeBankErase



namespace IntMul.TapeBankErase
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem sweep_step (m : ℕ) (bank : Fin (m+2)) (hb : 1 ≤ bank.val)
    (base : (machine m bank hb).Cfg) (w : List Sym) (hw : ValidWord w)
    (j : ℕ) (hj : j < w.length) :
    (machine m bank hb).step (sweepFrame m bank hb base w j)=sweepFrame m bank hb base w (j+1) := by
  let a : Fin (m+2) → Sym := fun i => (sweepFrame m bank hb base w j).cells i
    ((sweepFrame m bank hb base w j).head i)
  have hv : a bank=w.getD j Sym.blank := by
    simp only [a,sweepFrame,Function.update_self,erased_current]
  have hblank : a bank≠Sym.blank := by rw [hv];exact word_nonblank w hw j hj
  have hstart : a bank≠Sym.start := by rw [hv];exact word_not_start w hw j
  have ht : transition m bank .sweep a=(.sweep,
      fun i => (if i=bank then Sym.blank else a i,if i=bank then Move.right else Move.stay)) := by
    simp only [transition,rawTransition,if_neg hblank]
    congr 1
    funext i
    by_cases hi : i=bank
    · subst i
      simp [safeStep,hstart]
    · simp only [if_neg hi]
      exact safe_stay _
  change transition m bank (sweepFrame m bank hb base w j).state
    (fun i => (sweepFrame m bank hb base w j).cells i
      ((sweepFrame m bank hb base w j).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=bank
    · subst i
      simpa only [sweepFrame,Function.update_self,if_true] using erased_next w j
    · rw [if_neg hi,Function.update_eq_self]
      simp [sweepFrame,hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=bank <;> simp [sweepFrame,hi]

private theorem sweep_run (m : ℕ) (bank : Fin (m+2)) (hb : 1 ≤ bank.val)
    (base : (machine m bank hb).Cfg) (w : List Sym) (hw : ValidWord w)
    (j : ℕ) (hj : j ≤ w.length) :
    (machine m bank hb).step^[j] (sweepFrame m bank hb base w 0)=sweepFrame m bank hb base w j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),sweep_step m bank hb base w hw j (by omega)]

private theorem sweep_turn_step (m : ℕ) (bank : Fin (m+2)) (hb : 1 ≤ bank.val)
    (base : (machine m bank hb).Cfg) (w : List Sym) :
    (machine m bank hb).step (sweepFrame m bank hb base w w.length)=
      restoreFrame m bank hb base w.length := by
  let a : Fin (m+2) → Sym := fun i => (sweepFrame m bank hb base w w.length).cells i
    ((sweepFrame m bank hb base w w.length).head i)
  have ho : a bank=Sym.blank := by
    simp only [a,sweepFrame,Function.update_self,erased_current]
    exact List.getD_eq_default _ _ le_rfl
  have ht : transition m bank .sweep a=(.restore,
      fun i => (a i,if i=bank then Move.left else Move.stay)) := by
    simp only [transition,rawTransition,if_pos ho]
    congr 1
    funext i
    by_cases hi : i=bank
    · simp only [hi,if_true]
      apply safe_left
      rw [ho]
      decide
    · simp only [if_neg hi]
      exact safe_stay _
  change transition m bank (sweepFrame m bank hb base w w.length).state
    (fun i => (sweepFrame m bank hb base w w.length).cells i
      ((sweepFrame m bank hb base w w.length).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    simp only [sweepFrame,restoreFrame]
    rw [erased_full m bank hb w]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=bank <;> simp [sweepFrame,restoreFrame,hi]

end IntMul.TapeBankErase



namespace IntMul.TapeBankErase
open TapeCopy (Sym)
open TapeAdder (safe_stay)

private theorem restore_step (m : ℕ) (bank : Fin (m+2)) (hb : 1 ≤ bank.val)
    (base : (machine m bank hb).Cfg) (j : ℕ) :
    (machine m bank hb).step (restoreFrame m bank hb base (j+1))=
      restoreFrame m bank hb base j := by
  let a : Fin (m+2) → Sym := fun i => (restoreFrame m bank hb base (j+1)).cells i
    ((restoreFrame m bank hb base (j+1)).head i)
  have ho : a bank=Sym.blank := by simp [a,restoreFrame,MultitapeTM.tapeOf]
  have hstart : a bank≠Sym.start := by rw [ho];decide
  have ht : transition m bank .restore a=(.restore,
      fun i => (a i,if i=bank then Move.left else Move.stay)) := by
    simp only [transition,rawTransition,if_neg hstart]
    congr 1
    funext i
    by_cases hi : i=bank
    · simp only [hi,if_true]
      exact safe_left _ hstart
    · simp only [if_neg hi]
      exact safe_stay _
  change transition m bank (restoreFrame m bank hb base (j+1)).state
    (fun i => (restoreFrame m bank hb base (j+1)).cells i
      ((restoreFrame m bank hb base (j+1)).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=bank <;> simp [restoreFrame,hi]

private theorem restore_run (m : ℕ) (bank : Fin (m+2)) (hb : 1 ≤ bank.val)
    (base : (machine m bank hb).Cfg) (j : ℕ) :
    (machine m bank hb).step^[j] (restoreFrame m bank hb base j)=restoreFrame m bank hb base 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply,restore_step,ih]

private theorem restore_halt_step (m : ℕ) (bank : Fin (m+2)) (hb : 1 ≤ bank.val)
    (base : (machine m bank hb).Cfg) :
    (machine m bank hb).step (restoreFrame m bank hb base 0)=finalFrame m bank hb base := by
  let a : Fin (m+2) → Sym := fun i => (restoreFrame m bank hb base 0).cells i
    ((restoreFrame m bank hb base 0).head i)
  have ho : a bank=Sym.start := by simp [a,restoreFrame,MultitapeTM.tapeOf]
  have ht : transition m bank .restore a=(.halt,fun i => (a i,Move.stay)) := by
    simp [transition,rawTransition,ho,safe_stay]
  change transition m bank (restoreFrame m bank hb base 0).state
    (fun i => (restoreFrame m bank hb base 0).cells i
      ((restoreFrame m bank hb base 0).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];rfl

end IntMul.TapeBankErase



namespace IntMul.TapeBankErase
open TapeCopy (Sym)

/-- Actual complete workspace erasure on one selected work bank. Every rewind,
opening, blank write, final turn and halt transition is charged, while all
other physical caller banks and their head positions are retained exactly. -/
private theorem erase_bank (m : ℕ) (bank : Fin (m+2)) (hb : 1 ≤ bank.val)
    (base : (machine m bank hb).Cfg) (w : List Sym) (hw : ValidWord w) (h : ℕ) :
    (machine m bank hb).step^[h+2*w.length+3] (initialFrame m bank hb base w h)=
      finalFrame m bank hb base ∧
    ((machine m bank hb).step^[h+2*w.length+3] (initialFrame m bank hb base w h)).state=
      (machine m bank hb).qHalt := by
  have h₁ : (machine m bank hb).step^[h+1] (initialFrame m bank hb base w h)=
      sweepFrame m bank hb base w 0 := by
    rw [Function.iterate_succ_apply',rewind_run m bank hb base w hw,rewind_open_step]
  have h₂ : (machine m bank hb).step^[w.length+1] (sweepFrame m bank hb base w 0)=
      restoreFrame m bank hb base w.length := by
    rw [Function.iterate_succ_apply',sweep_run m bank hb base w hw w.length le_rfl,sweep_turn_step]
  have h₃ : (machine m bank hb).step^[w.length+1] (restoreFrame m bank hb base w.length)=
      finalFrame m bank hb base := by
    rw [Function.iterate_succ_apply',restore_run,restore_halt_step]
  have h₁₂ : (machine m bank hb).step^[(w.length+1)+(h+1)] (initialFrame m bank hb base w h)=
      restoreFrame m bank hb base w.length := by
    rw [Function.iterate_add_apply,h₁,h₂]
  have he : (machine m bank hb).step^[h+2*w.length+3] (initialFrame m bank hb base w h)=
      finalFrame m bank hb base := by
    rw [show h+2*w.length+3=(w.length+1)+((w.length+1)+(h+1)) by omega,
      Function.iterate_add_apply,h₁₂,h₃]
  refine ⟨he,?_⟩
  rw [he]
  rfl

end IntMul.TapeBankErase



open IntMul IntMul.TapeBankErase
open IntMul.TapeCopy (Sym)

theorem solution (m : ℕ) (bank : Fin (m+2)) (hb : 1 ≤ bank.val)
    (base : (machine m bank hb).Cfg) (w : List Sym) (hw : ValidWord w) (h : ℕ) :
    (machine m bank hb).step^[h+2*w.length+3] (initialFrame m bank hb base w h)=
      finalFrame m bank hb base ∧
    ((machine m bank hb).step^[h+2*w.length+3] (initialFrame m bank hb base w h)).state=
      (machine m bank hb).qHalt :=
  IntMul.TapeBankErase.erase_bank m bank hb base w hw h

#print axioms solution
