-- Prove2me | solution 1 for IntMul.TapeStack.push_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T21:48:56.842904+00:00
-- url     : https://prove2.me/submissions/52a0b8b4-97e6-42cb-a43b-6ae0ca0a7d99

import Definitions.Def_IntMul_TapeStack
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic


namespace IntMul.TapeStack

open IntMul.TapeCopy (Sym)

private theorem local_boundary (base : ℕ → Sym) (offset : ℕ) (w : List Sym) :
    localTape base offset w offset = .sep := by simp [localTape]

private theorem local_payload (base : ℕ → Sym) (offset : ℕ) (w : List Sym) (p : ℕ) :
    localTape base offset w (offset + p + 1) = w.getD p .blank := by
  simp only [localTape,if_neg (by omega : ¬offset + p + 1 < offset),
    if_neg (by omega : offset + p + 1 ≠ offset)]
  congr 1
  omega

private theorem local_append_one (base : ℕ → Sym) (offset : ℕ) (w : List Sym) (a : Sym) :
    Function.update (localTape base offset w) (offset + w.length + 1) a =
      localTape base offset (w ++ [a]) := by
  classical
  funext p
  by_cases he : p = offset + w.length + 1
  · subst p
    rw [Function.update_self,local_payload]
    simp
  · rw [Function.update_of_ne he]
    by_cases hp : p < offset
    · simp only [localTape,if_pos hp]
    · by_cases hs : p = offset
      · simp only [localTape,if_neg hp,if_pos hs]
      · simp only [localTape,if_neg hp,if_neg hs]
        by_cases hlt : p - offset - 1 < w.length
        · rw [List.getD_append _ _ _ _ hlt]
        · have hge : w.length ≤ p - offset - 1 := by omega
          rw [List.getD_eq_default _ _ hge,List.getD_append_right _ _ _ _ hge,
            List.getD_eq_default _ _ (by simp; omega)]

private theorem local_erase_last (base : ℕ → Sym) (offset : ℕ) (w : List Sym) (a : Sym) :
    Function.update (localTape base offset (w ++ [a])) (offset + w.length + 1) .blank =
      localTape base offset w := by
  classical
  rw [←local_append_one,Function.update_idem]
  have hb : localTape base offset w (offset + w.length + 1) = .blank := by
    rw [local_payload,List.getD_eq_default _ _ le_rfl]
  rw [←hb]
  exact Function.update_eq_self _ _

private theorem erased_read (base : ℕ → Sym) (offset : ℕ) (w : List Bool) (j : ℕ) :
    erasedTape base offset w j (offset + j + 1) = (w.map machine.bitSym).getD j .blank := by
  simp only [erasedTape,if_neg (by omega : ¬offset + j + 1 < offset),
    if_neg (by omega : offset + j + 1 ≠ offset),if_neg (by omega : ¬offset + j + 1 < offset + j + 1)]
  congr 1
  omega

private theorem erased_step (base : ℕ → Sym) (offset : ℕ) (w : List Bool) (j : ℕ) :
    Function.update (erasedTape base offset w j) (offset + j + 1) .blank =
      erasedTape base offset w (j + 1) := by
  classical
  funext p
  by_cases he : p = offset + j + 1
  · subst p
    simp [erasedTape,show ¬offset + j + 1 < offset by omega,show offset + j + 1 ≠ offset by omega]
  · rw [Function.update_of_ne he]
    by_cases hp : p < offset
    · simp only [erasedTape,if_pos hp]
    · by_cases hs : p = offset
      · simp only [erasedTape,if_neg hp,if_pos hs]
      · simp only [erasedTape,if_neg hp,if_neg hs]
        by_cases hj : p < offset + j + 1
        · simp only [if_pos hj,if_pos (by omega : p < offset + (j + 1) + 1)]
        · simp only [if_neg hj,if_neg (by omega : ¬p < offset + (j + 1) + 1)]

private theorem erased_initial (base : ℕ → Sym) (offset : ℕ) (w : List Bool) :
    erasedTape base offset w 0 = localTape base offset (w.map machine.bitSym) := by
  funext p
  by_cases hp : p < offset
  · simp only [erasedTape,localTape,if_pos hp]
  · by_cases hs : p = offset
    · simp only [erasedTape,localTape,if_neg hp,if_pos hs]
    · simp only [erasedTape,localTape,if_neg hp,if_neg hs,if_neg (by omega : ¬p < offset + 0 + 1)]

private theorem erased_finished (base : ℕ → Sym) (offset : ℕ) (w : List Bool) :
    erasedTape base offset w w.length = localTape base offset [] := by
  funext p
  by_cases hp : p < offset
  · simp only [erasedTape,localTape,if_pos hp]
  · by_cases hs : p = offset
    · simp only [erasedTape,localTape,if_neg hp,if_pos hs]
    · simp only [erasedTape,localTape,if_neg hp,if_neg hs,List.getD_nil]
      by_cases hj : p < offset + w.length + 1
      · simp only [if_pos hj]
      · rw [if_neg hj,List.getD_eq_default _ _ (by simp; omega)]

end IntMul.TapeStack



namespace IntMul.TapeStack

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep safe_stay)

private theorem part1_cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem part1_push_bit_transition (a : Fin 4 → Sym) (b : Bool)
    (hs : a 1 = machine.bitSym b) (ht : a 2 = .blank) :
    transition .pushCopy a = (.pushCopy,fun i =>
      (if i = 1 then .blank else if i = 2 then machine.bitSym b else a i,
        if i = 1 ∨ i = 2 then .right else .stay)) := by
  have hb : a 1 = .zero ∨ a 1 = .one := by rw [hs]; cases b <;> simp [MultitapeTM.bitSym]
  simp only [transition,rawTransition,if_pos hb]
  congr 1
  funext i
  fin_cases i
  · exact safe_stay (a 0)
  · change safeStep (a 1) .blank .right = (.blank,.right)
    rw [hs]
    cases b <;> rfl
  · change safeStep (a 2) (a 1) .right = (machine.bitSym b,.right)
    rw [ht,hs]
    cases b <;> rfl
  · exact safe_stay (a 3)

private theorem part1_push_bit_step (base : machine.Cfg) (sigma rho tau : ℕ)
    (w : List Bool) (j : ℕ) (hj : j < w.length) :
    machine.step (pushFrame base sigma rho tau w j) = pushFrame base sigma rho tau w (j + 1) := by
  have hs : (pushFrame base sigma rho tau w j).cells 1
      ((pushFrame base sigma rho tau w j).head 1) = machine.bitSym w[j] := by
    change erasedTape (base.cells 1) sigma w j (sigma + j + 1) = _
    rw [erased_read,List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]
  have hl : (w.take j).length = j := by simp [Nat.min_eq_left hj.le]
  have ht : (pushFrame base sigma rho tau w j).cells 2
      ((pushFrame base sigma rho tau w j).head 2) = .blank := by
    change localTape (base.cells 2) rho ((w.take j).map machine.bitSym) (rho + j + 1) = _
    rw [local_payload,List.getD_eq_default _ _ (by simp [hl])]
  have hd := part1_push_bit_transition
    (fun i => (pushFrame base sigma rho tau w j).cells i ((pushFrame base sigma rho tau w j).head i)) w[j] hs ht
  change transition (pushFrame base sigma rho tau w j).state
    (fun i => (pushFrame base sigma rho tau w j).cells i ((pushFrame base sigma rho tau w j).head i)) = _ at hd
  apply part1_cfg_ext
  · simp only [MultitapeTM.step,hd]
    rfl
  · simp only [MultitapeTM.step,hd]
    funext i
    fin_cases i
    · change Function.update (base.cells 0) (base.head 0) (base.cells 0 (base.head 0)) = _
      exact Function.update_eq_self _ _
    · change Function.update (erasedTape (base.cells 1) sigma w j) (sigma + j + 1) .blank = _
      exact erased_step _ _ _ _
    · change Function.update (localTape (base.cells 2) rho ((w.take j).map machine.bitSym))
        (rho + j + 1) (machine.bitSym w[j]) = localTape (base.cells 2) rho ((w.take (j + 1)).map machine.bitSym)
      rw [List.take_succ_eq_append_getElem hj]
      simpa only [hl,List.length_map,List.map_append,List.map_singleton] using
        local_append_one (base.cells 2) rho ((w.take j).map machine.bitSym) (machine.bitSym w[j])
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,hd]
    funext i
    fin_cases i <;> simp [pushFrame,Nat.add_assoc]

private theorem part1_push_copy_run (base : machine.Cfg) (sigma rho tau : ℕ)
    (w : List Bool) (j : ℕ) (hj : j ≤ w.length) :
    machine.step^[j] (pushFrame base sigma rho tau w 0) = pushFrame base sigma rho tau w j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),part1_push_bit_step base sigma rho tau w j (by omega)]

private theorem part1_push_end_transition (a : Fin 4 → Sym) (hs : a 1 = .blank) (ht : a 2 = .blank) :
    transition .pushCopy a = (.pushRewind,fun i =>
      (if i = 2 then .sep else a i,if i = 1 then .left else if i = 2 then .right else .stay)) := by
  have hb : ¬(a 1 = .zero ∨ a 1 = .one) := by simp [hs]
  simp only [transition,rawTransition,if_neg hb]
  congr 1
  funext i
  fin_cases i
  · exact safe_stay (a 0)
  · change safeStep (a 1) (a 1) .left = (a 1,.left)
    rw [hs]
    rfl
  · change safeStep (a 2) .sep .right = (.sep,.right)
    rw [ht]
    rfl
  · exact safe_stay (a 3)

private theorem part1_push_end_step (base : machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) :
    machine.step (pushFrame base sigma rho tau w w.length) = pushRewindFrame base sigma rho tau w w.length := by
  have hs : (pushFrame base sigma rho tau w w.length).cells 1
      ((pushFrame base sigma rho tau w w.length).head 1) = .blank := by
    change erasedTape (base.cells 1) sigma w w.length (sigma + w.length + 1) = _
    rw [erased_read,List.getD_eq_default _ _ (by simp)]
  have ht : (pushFrame base sigma rho tau w w.length).cells 2
      ((pushFrame base sigma rho tau w w.length).head 2) = .blank := by
    change localTape (base.cells 2) rho ((w.take w.length).map machine.bitSym) (rho + w.length + 1) = _
    rw [List.take_length,local_payload,List.getD_eq_default _ _ (by simp)]
  have hd := part1_push_end_transition
    (fun i => (pushFrame base sigma rho tau w w.length).cells i ((pushFrame base sigma rho tau w w.length).head i)) hs ht
  change transition (pushFrame base sigma rho tau w w.length).state
    (fun i => (pushFrame base sigma rho tau w w.length).cells i ((pushFrame base sigma rho tau w w.length).head i)) = _ at hd
  apply part1_cfg_ext
  · simp only [MultitapeTM.step,hd]
    rfl
  · simp only [MultitapeTM.step,hd]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · change Function.update (erasedTape (base.cells 1) sigma w w.length) (sigma + w.length + 1)
        (erasedTape (base.cells 1) sigma w w.length (sigma + w.length + 1)) = localTape (base.cells 1) sigma []
      rw [Function.update_eq_self]
      exact erased_finished _ _ _
    · change Function.update (localTape (base.cells 2) rho ((w.take w.length).map machine.bitSym))
        (rho + w.length + 1) .sep = localTape (base.cells 2) rho (w.map machine.bitSym ++ [.sep])
      rw [List.take_length]
      simpa only [List.length_map] using local_append_one (base.cells 2) rho (w.map machine.bitSym) .sep
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,hd]
    funext i
    fin_cases i <;> simp [pushFrame,pushRewindFrame,frame]
    all_goals omega

private theorem part1_push_left_transition (a : Fin 4 → Sym) (hs : a 1 = .blank) :
    transition .pushRewind a = (.pushRewind,fun i => (a i,if i = 1 then .left else .stay)) := by
  simp only [transition,rawTransition,if_neg (by simp [hs] : a 1 ≠ .sep)]
  congr 1
  funext i
  fin_cases i
  · exact safe_stay (a 0)
  · change safeStep (a 1) (a 1) .left = (a 1,.left)
    rw [hs]
    rfl
  · exact safe_stay (a 2)
  · exact safe_stay (a 3)

private theorem part1_push_left_step (base : machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) (p : ℕ) :
    machine.step (pushRewindFrame base sigma rho tau w (p + 1)) = pushRewindFrame base sigma rho tau w p := by
  have hs : (pushRewindFrame base sigma rho tau w (p + 1)).cells 1
      ((pushRewindFrame base sigma rho tau w (p + 1)).head 1) = .blank := by
    change localTape (base.cells 1) sigma [] (sigma + (p + 1)) = _
    rw [show sigma + (p + 1) = sigma + p + 1 by omega,local_payload,List.getD_nil]
  have hd := part1_push_left_transition
    (fun i => (pushRewindFrame base sigma rho tau w (p + 1)).cells i
      ((pushRewindFrame base sigma rho tau w (p + 1)).head i)) hs
  change transition (pushRewindFrame base sigma rho tau w (p + 1)).state
    (fun i => (pushRewindFrame base sigma rho tau w (p + 1)).cells i
      ((pushRewindFrame base sigma rho tau w (p + 1)).head i)) = _ at hd
  apply part1_cfg_ext
  · simp only [MultitapeTM.step,hd]
    rfl
  · simp only [MultitapeTM.step,hd]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,hd]
    funext i
    fin_cases i <;> simp [pushRewindFrame,frame]
    all_goals omega

private theorem part1_push_marker_transition (a : Fin 4 → Sym) (hs : a 1 = .sep) :
    transition .pushRewind a = (.halt,fun i => (a i,if i = 1 then .right else .stay)) := by
  simp only [transition,rawTransition,if_pos hs]
  congr 1
  funext i
  fin_cases i
  · exact safe_stay (a 0)
  · change safeStep (a 1) (a 1) .right = (a 1,.right)
    rw [hs]
    rfl
  · exact safe_stay (a 2)
  · exact safe_stay (a 3)

private theorem part1_push_marker_step (base : machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) :
    machine.step (pushRewindFrame base sigma rho tau w 0) = pushDoneFrame base sigma rho tau w := by
  have hs : (pushRewindFrame base sigma rho tau w 0).cells 1
      ((pushRewindFrame base sigma rho tau w 0).head 1) = .sep := by
    change localTape (base.cells 1) sigma [] (sigma + 0) = _
    rw [Nat.add_zero,local_boundary]
  have hd := part1_push_marker_transition
    (fun i => (pushRewindFrame base sigma rho tau w 0).cells i
      ((pushRewindFrame base sigma rho tau w 0).head i)) hs
  change transition (pushRewindFrame base sigma rho tau w 0).state
    (fun i => (pushRewindFrame base sigma rho tau w 0).cells i
      ((pushRewindFrame base sigma rho tau w 0).head i)) = _ at hd
  apply part1_cfg_ext
  · simp only [MultitapeTM.step,hd]
    rfl
  · simp only [MultitapeTM.step,hd]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,hd]
    funext i
    fin_cases i <;> simp [pushRewindFrame,pushDoneFrame,frame]

private theorem part1_push_rewind_run (base : machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) (p : ℕ) :
    machine.step^[p + 1] (pushRewindFrame base sigma rho tau w p) = pushDoneFrame base sigma rho tau w := by
  induction p with
  | zero => simpa using part1_push_marker_step base sigma rho tau w
  | succ p ih => rw [Function.iterate_succ_apply,part1_push_left_step base sigma rho tau w p,ih]

/-- Copy to the parked stack, erase the source and restore its head. The
exact bound has no dependence on any saved prefix or older stack frames. -/
private theorem push_correct (base : machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) :
    machine.step^[2 * w.length + 2] (pushFrame base sigma rho tau w 0) =
      pushDoneFrame base sigma rho tau w := by
  have hc : machine.step^[w.length + 1] (pushFrame base sigma rho tau w 0) =
      pushRewindFrame base sigma rho tau w w.length := by
    rw [Function.iterate_succ_apply',part1_push_copy_run base sigma rho tau w w.length le_rfl,part1_push_end_step]
  rw [show 2 * w.length + 2 = (w.length + 1) + (w.length + 1) by omega,
    Function.iterate_add_apply,hc,part1_push_rewind_run]

end IntMul.TapeStack


open IntMul IntMul.TapeStack

theorem solution (base : machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) :
    machine.step^[2 * w.length + 2] (pushFrame base sigma rho tau w 0) =
      pushDoneFrame base sigma rho tau w :=
  IntMul.TapeStack.push_correct base sigma rho tau w

#print axioms solution
