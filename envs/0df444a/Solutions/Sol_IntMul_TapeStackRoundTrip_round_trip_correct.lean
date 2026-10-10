-- Prove2me | solution 1 for IntMul.TapeStackRoundTrip.round_trip_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T21:59:25.681055+00:00
-- url     : https://prove2.me/submissions/5edc3645-aa8f-485b-884c-ff6af47b7497

import Definitions.Def_IntMul_TapeStackRoundTrip
import Theorems.Thm_IntMul_FiniteCaller_simulate_run
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



namespace IntMul.TapeStack

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep safe_stay)

private theorem part2_cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem part2_delimiter_transition (a : Fin 4 → Sym) (hs : a 2 = .blank) :
    transition .popDelimiter a = (.popPayload,fun i => (a i,if i = 2 then .left else .stay)) := by
  simp only [transition,rawTransition]
  congr 1
  funext i
  fin_cases i
  · exact safe_stay (a 0)
  · exact safe_stay (a 1)
  · change safeStep (a 2) (a 2) .left = (a 2,.left)
    rw [hs]
    rfl
  · exact safe_stay (a 3)

private theorem part2_delimiter_step (base : machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) :
    machine.step (popStartFrame base sigma rho tau w) = popDelimiterFrame base sigma rho tau w := by
  have hs : (popStartFrame base sigma rho tau w).cells 2 ((popStartFrame base sigma rho tau w).head 2) = .blank := by
    change localTape (base.cells 2) rho (w.map machine.bitSym ++ [.sep]) (rho + (w.length + 2)) = _
    rw [show rho + (w.length + 2) = rho + (w.length + 1) + 1 by omega,local_payload,
      List.getD_eq_default _ _ (by simp)]
  have hd := part2_delimiter_transition
    (fun i => (popStartFrame base sigma rho tau w).cells i ((popStartFrame base sigma rho tau w).head i)) hs
  change transition (popStartFrame base sigma rho tau w).state
    (fun i => (popStartFrame base sigma rho tau w).cells i ((popStartFrame base sigma rho tau w).head i)) = _ at hd
  apply part2_cfg_ext
  · simp only [MultitapeTM.step,hd]
    rfl
  · simp only [MultitapeTM.step,hd]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,hd]
    funext i
    fin_cases i <;> simp [popStartFrame,popDelimiterFrame,frame,if_true,if_false]
    all_goals omega

private theorem part2_payload_transition (a : Fin 4 → Sym) (hs : a 2 = .sep) :
    transition .popPayload a = (.popPark,fun i => (if i = 2 then .blank else a i,if i = 2 then .left else .stay)) := by
  simp only [transition,rawTransition]
  congr 1
  funext i
  fin_cases i
  · exact safe_stay (a 0)
  · exact safe_stay (a 1)
  · change safeStep (a 2) .blank .left = (.blank,.left)
    rw [hs]
    rfl
  · exact safe_stay (a 3)

private theorem part2_payload_step (base : machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) :
    machine.step (popDelimiterFrame base sigma rho tau w) = parkFrame base sigma rho tau w [] := by
  have hs : (popDelimiterFrame base sigma rho tau w).cells 2 ((popDelimiterFrame base sigma rho tau w).head 2) = .sep := by
    change localTape (base.cells 2) rho (w.map machine.bitSym ++ [.sep]) (rho + (w.length + 1)) = _
    rw [show rho + (w.length + 1) = rho + w.length + 1 by omega,local_payload]
    simp
  have hd := part2_payload_transition
    (fun i => (popDelimiterFrame base sigma rho tau w).cells i ((popDelimiterFrame base sigma rho tau w).head i)) hs
  change transition (popDelimiterFrame base sigma rho tau w).state
    (fun i => (popDelimiterFrame base sigma rho tau w).cells i ((popDelimiterFrame base sigma rho tau w).head i)) = _ at hd
  apply part2_cfg_ext
  · simp only [MultitapeTM.step,hd]
    rfl
  · simp only [MultitapeTM.step,hd]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · change Function.update (localTape (base.cells 2) rho (w.map machine.bitSym ++ [.sep]))
        (rho + (w.length + 1)) .blank = localTape (base.cells 2) rho (w.map machine.bitSym)
      simpa only [List.length_map,Nat.add_assoc] using local_erase_last (base.cells 2) rho (w.map machine.bitSym) .sep
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,hd]
    funext i
    fin_cases i <;> simp [popDelimiterFrame,parkFrame,frame,if_true,if_false,List.length_nil]
    all_goals omega

private theorem part2_park_bit_transition (a : Fin 4 → Sym) (b : Bool)
    (hs : a 2 = machine.bitSym b) (ht : a 3 = .blank) :
    transition .popPark a = (.popPark,fun i =>
      (if i = 2 then .blank else if i = 3 then machine.bitSym b else a i,
        if i = 2 then .left else if i = 3 then .right else .stay)) := by
  have hb : a 2 = .zero ∨ a 2 = .one := by rw [hs]; cases b <;> simp [MultitapeTM.bitSym]
  simp only [transition,rawTransition,if_pos hb]
  congr 1
  funext i
  fin_cases i
  · exact safe_stay (a 0)
  · exact safe_stay (a 1)
  · change safeStep (a 2) .blank .left = (.blank,.left)
    rw [hs]
    cases b <;> rfl
  · change safeStep (a 3) (a 2) .right = (machine.bitSym b,.right)
    rw [ht,hs]
    cases b <;> rfl

private theorem part2_park_bit_step (base : machine.Cfg) (sigma rho tau : ℕ) (left done : List Bool) (b : Bool) :
    machine.step (parkFrame base sigma rho tau (left ++ [b]) done) =
      parkFrame base sigma rho tau left (done ++ [b]) := by
  have hs : (parkFrame base sigma rho tau (left ++ [b]) done).cells 2
      ((parkFrame base sigma rho tau (left ++ [b]) done).head 2) = machine.bitSym b := by
    change localTape (base.cells 2) rho ((left ++ [b]).map machine.bitSym) (rho + (left ++ [b]).length) = _
    rw [List.length_append,List.length_singleton,show rho + (left.length + 1) = rho + left.length + 1 by omega,local_payload,List.map_append,List.map_singleton]
    simp
  have ht : (parkFrame base sigma rho tau (left ++ [b]) done).cells 3
      ((parkFrame base sigma rho tau (left ++ [b]) done).head 3) = .blank := by
    change localTape (base.cells 3) tau (done.map machine.bitSym) (tau + (done.length + 1)) = _
    rw [show tau + (done.length + 1) = tau + done.length + 1 by omega,local_payload,
      List.getD_eq_default _ _ (by simp)]
  have hd := part2_park_bit_transition
    (fun i => (parkFrame base sigma rho tau (left ++ [b]) done).cells i
      ((parkFrame base sigma rho tau (left ++ [b]) done).head i)) b hs ht
  change transition (parkFrame base sigma rho tau (left ++ [b]) done).state
    (fun i => (parkFrame base sigma rho tau (left ++ [b]) done).cells i
      ((parkFrame base sigma rho tau (left ++ [b]) done).head i)) = _ at hd
  apply part2_cfg_ext
  · simp only [MultitapeTM.step,hd]
    rfl
  · simp only [MultitapeTM.step,hd]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · change Function.update (localTape (base.cells 2) rho ((left ++ [b]).map machine.bitSym))
        (rho + (left ++ [b]).length) .blank = localTape (base.cells 2) rho (left.map machine.bitSym)
      simpa only [List.map_append,List.map_singleton,List.length_append,List.length_singleton,List.length_map,Nat.add_assoc] using
        local_erase_last (base.cells 2) rho (left.map machine.bitSym) (machine.bitSym b)
    · change Function.update (localTape (base.cells 3) tau (done.map machine.bitSym))
        (tau + (done.length + 1)) (machine.bitSym b) = localTape (base.cells 3) tau ((done ++ [b]).map machine.bitSym)
      simpa only [List.map_append,List.map_singleton,List.length_map,Nat.add_assoc] using
        local_append_one (base.cells 3) tau (done.map machine.bitSym) (machine.bitSym b)
  · simp only [MultitapeTM.step,hd]
    funext i
    fin_cases i <;> simp [parkFrame,frame,if_true,if_false,List.length_append,List.length_singleton]
    all_goals omega

private theorem part2_park_marker_transition (a : Fin 4 → Sym) (hs : a 2 = .sep) (ht : a 3 = .blank) :
    transition .popPark a = (.popOutput,fun i =>
      (a i,if i = 2 then .right else if i = 3 then .left else .stay)) := by
  have hb : ¬(a 2 = .zero ∨ a 2 = .one) := by simp [hs]
  simp only [transition,rawTransition,if_neg hb,if_pos hs]
  congr 1
  funext i
  fin_cases i
  · exact safe_stay (a 0)
  · exact safe_stay (a 1)
  · change safeStep (a 2) (a 2) .right = (a 2,.right)
    rw [hs]
    rfl
  · change safeStep (a 3) (a 3) .left = (a 3,.left)
    rw [ht]
    rfl

private theorem part2_park_marker_step (base : machine.Cfg) (sigma rho tau : ℕ) (done : List Bool) :
    machine.step (parkFrame base sigma rho tau [] done) = outputFrame base sigma rho tau done [] := by
  have hs : (parkFrame base sigma rho tau [] done).cells 2
      ((parkFrame base sigma rho tau [] done).head 2) = .sep := by
    change localTape (base.cells 2) rho [] (rho + 0) = _
    rw [Nat.add_zero,local_boundary]
  have ht : (parkFrame base sigma rho tau [] done).cells 3
      ((parkFrame base sigma rho tau [] done).head 3) = .blank := by
    change localTape (base.cells 3) tau (done.map machine.bitSym) (tau + (done.length + 1)) = _
    rw [show tau + (done.length + 1) = tau + done.length + 1 by omega,local_payload,
      List.getD_eq_default _ _ (by simp)]
  have hd := part2_park_marker_transition
    (fun i => (parkFrame base sigma rho tau [] done).cells i
      ((parkFrame base sigma rho tau [] done).head i)) hs ht
  change transition (parkFrame base sigma rho tau [] done).state
    (fun i => (parkFrame base sigma rho tau [] done).cells i
      ((parkFrame base sigma rho tau [] done).head i)) = _ at hd
  apply part2_cfg_ext
  · simp only [MultitapeTM.step,hd]
    rfl
  · simp only [MultitapeTM.step,hd]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,hd]
    funext i
    fin_cases i <;> simp [parkFrame,outputFrame,frame,if_true,if_false,List.length_nil]
    all_goals omega

/-- A reverse scan physically transfers a frame to temporary storage and
erases the parked suffix, stopping at the preceding separator. -/
private theorem park_reverse_run (base : machine.Cfg) (sigma rho tau : ℕ) (w done : List Bool) :
    machine.step^[w.length + 1] (parkFrame base sigma rho tau w.reverse done) =
      outputFrame base sigma rho tau (done ++ w) [] := by
  induction w generalizing done with
  | nil => simpa using part2_park_marker_step base sigma rho tau done
  | cons b rest ih =>
      rw [List.length_cons,show rest.length + 1 + 1 = (rest.length + 1) + 1 by omega,
        Function.iterate_succ_apply,List.reverse_cons,part2_park_bit_step,ih]
      simp only [List.append_assoc,List.singleton_append]

/-- Both entry transitions are charged; the trailing stack delimiter is erased. -/
private theorem pop_enter_correct (base : machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) :
    machine.step^[2] (popStartFrame base sigma rho tau w) = parkFrame base sigma rho tau w [] := by
  rw [show 2 = 1 + 1 by rfl,Function.iterate_add_apply,Function.iterate_one,
    part2_delimiter_step,part2_payload_step]

end IntMul.TapeStack



namespace IntMul.TapeStack

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep safe_stay)

private theorem part3_cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem part3_output_bit_transition (a : Fin 4 → Sym) (b : Bool)
    (hs : a 3 = machine.bitSym b) (ht : a 1 = .blank) :
    transition .popOutput a = (.popOutput,fun i =>
      (if i = 3 then .blank else if i = 1 then machine.bitSym b else a i,
        if i = 3 then .left else if i = 1 then .right else .stay)) := by
  have hb : a 3 = .zero ∨ a 3 = .one := by rw [hs]; cases b <;> simp [MultitapeTM.bitSym]
  simp only [transition,rawTransition,if_pos hb]
  congr 1
  funext i
  fin_cases i
  · exact safe_stay (a 0)
  · change safeStep (a 1) (a 3) .right = (machine.bitSym b,.right)
    rw [ht,hs]
    cases b <;> rfl
  · exact safe_stay (a 2)
  · change safeStep (a 3) .blank .left = (.blank,.left)
    rw [hs]
    cases b <;> rfl

private theorem part3_output_bit_step (base : machine.Cfg) (sigma rho tau : ℕ) (left done : List Bool) (b : Bool) :
    machine.step (outputFrame base sigma rho tau (left ++ [b]) done) =
      outputFrame base sigma rho tau left (done ++ [b]) := by
  have hs : (outputFrame base sigma rho tau (left ++ [b]) done).cells 3
      ((outputFrame base sigma rho tau (left ++ [b]) done).head 3) = machine.bitSym b := by
    change localTape (base.cells 3) tau ((left ++ [b]).map machine.bitSym) (tau + (left ++ [b]).length) = _
    rw [List.length_append,List.length_singleton,show tau + (left.length + 1) = tau + left.length + 1 by omega,
      local_payload,List.map_append,List.map_singleton]
    simp
  have ht : (outputFrame base sigma rho tau (left ++ [b]) done).cells 1
      ((outputFrame base sigma rho tau (left ++ [b]) done).head 1) = .blank := by
    change localTape (base.cells 1) sigma (done.map machine.bitSym) (sigma + (done.length + 1)) = _
    rw [show sigma + (done.length + 1) = sigma + done.length + 1 by omega,local_payload,
      List.getD_eq_default _ _ (by simp)]
  have hd := part3_output_bit_transition
    (fun i => (outputFrame base sigma rho tau (left ++ [b]) done).cells i
      ((outputFrame base sigma rho tau (left ++ [b]) done).head i)) b hs ht
  change transition (outputFrame base sigma rho tau (left ++ [b]) done).state
    (fun i => (outputFrame base sigma rho tau (left ++ [b]) done).cells i
      ((outputFrame base sigma rho tau (left ++ [b]) done).head i)) = _ at hd
  apply part3_cfg_ext
  · simp only [MultitapeTM.step,hd]
    rfl
  · simp only [MultitapeTM.step,hd]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · change Function.update (localTape (base.cells 1) sigma (done.map machine.bitSym))
        (sigma + (done.length + 1)) (machine.bitSym b) = localTape (base.cells 1) sigma ((done ++ [b]).map machine.bitSym)
      simpa only [List.map_append,List.map_singleton,List.length_map,Nat.add_assoc] using
        local_append_one (base.cells 1) sigma (done.map machine.bitSym) (machine.bitSym b)
    · exact Function.update_eq_self _ _
    · change Function.update (localTape (base.cells 3) tau ((left ++ [b]).map machine.bitSym))
        (tau + (left ++ [b]).length) .blank = localTape (base.cells 3) tau (left.map machine.bitSym)
      simpa only [List.map_append,List.map_singleton,List.length_append,List.length_singleton,List.length_map,Nat.add_assoc] using
        local_erase_last (base.cells 3) tau (left.map machine.bitSym) (machine.bitSym b)
  · simp only [MultitapeTM.step,hd]
    funext i
    fin_cases i <;> simp [outputFrame,frame]
    all_goals omega

private theorem part3_output_marker_transition (a : Fin 4 → Sym) (hs : a 3 = .sep) (ht : a 1 = .blank) :
    transition .popOutput a = (.popRewind,fun i =>
      (a i,if i = 3 then .right else if i = 1 then .left else .stay)) := by
  have hb : ¬(a 3 = .zero ∨ a 3 = .one) := by simp [hs]
  simp only [transition,rawTransition,if_neg hb,if_pos hs]
  congr 1
  funext i
  fin_cases i
  · exact safe_stay (a 0)
  · change safeStep (a 1) (a 1) .left = (a 1,.left)
    rw [ht]
    rfl
  · exact safe_stay (a 2)
  · change safeStep (a 3) (a 3) .right = (a 3,.right)
    rw [hs]
    rfl

private theorem part3_output_marker_step (base : machine.Cfg) (sigma rho tau : ℕ) (done : List Bool) :
    machine.step (outputFrame base sigma rho tau [] done) =
      popRewindFrame base sigma rho tau done done.length := by
  have hs : (outputFrame base sigma rho tau [] done).cells 3
      ((outputFrame base sigma rho tau [] done).head 3) = .sep := by
    change localTape (base.cells 3) tau [] (tau + 0) = _
    rw [Nat.add_zero,local_boundary]
  have ht : (outputFrame base sigma rho tau [] done).cells 1
      ((outputFrame base sigma rho tau [] done).head 1) = .blank := by
    change localTape (base.cells 1) sigma (done.map machine.bitSym) (sigma + (done.length + 1)) = _
    rw [show sigma + (done.length + 1) = sigma + done.length + 1 by omega,local_payload,
      List.getD_eq_default _ _ (by simp)]
  have hd := part3_output_marker_transition
    (fun i => (outputFrame base sigma rho tau [] done).cells i
      ((outputFrame base sigma rho tau [] done).head i)) hs ht
  change transition (outputFrame base sigma rho tau [] done).state
    (fun i => (outputFrame base sigma rho tau [] done).cells i
      ((outputFrame base sigma rho tau [] done).head i)) = _ at hd
  apply part3_cfg_ext
  · simp only [MultitapeTM.step,hd]
    rfl
  · simp only [MultitapeTM.step,hd]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,hd]
    funext i
    fin_cases i <;> simp [outputFrame,popRewindFrame,frame]
    all_goals omega

/-- The second physical reverse scan restores the original bit order and
erases every temporary payload cell. -/
private theorem output_reverse_run (base : machine.Cfg) (sigma rho tau : ℕ) (w done : List Bool) :
    machine.step^[w.length + 1] (outputFrame base sigma rho tau w.reverse done) =
      popRewindFrame base sigma rho tau (done ++ w) (done ++ w).length := by
  induction w generalizing done with
  | nil => simpa using part3_output_marker_step base sigma rho tau done
  | cons b rest ih =>
      rw [List.length_cons,show rest.length + 1 + 1 = (rest.length + 1) + 1 by omega,
        Function.iterate_succ_apply,List.reverse_cons,part3_output_bit_step,ih]
      simp only [List.append_assoc,List.singleton_append]

private theorem part3_rewind_bit_transition (a : Fin 4 → Sym) (b : Bool) (hs : a 1 = machine.bitSym b) :
    transition .popRewind a = (.popRewind,fun i => (a i,if i = 1 then .left else .stay)) := by
  have hb : a 1 ≠ .sep := by rw [hs]; cases b <;> simp [MultitapeTM.bitSym]
  simp only [transition,rawTransition,if_neg hb]
  congr 1
  funext i
  fin_cases i
  · exact safe_stay (a 0)
  · change safeStep (a 1) (a 1) .left = (a 1,.left)
    rw [hs]
    cases b <;> rfl
  · exact safe_stay (a 2)
  · exact safe_stay (a 3)

private theorem part3_rewind_bit_step (base : machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) (p : ℕ)
    (hp : p < w.length) :
    machine.step (popRewindFrame base sigma rho tau w (p + 1)) = popRewindFrame base sigma rho tau w p := by
  have hs : (popRewindFrame base sigma rho tau w (p + 1)).cells 1
      ((popRewindFrame base sigma rho tau w (p + 1)).head 1) = machine.bitSym w[p] := by
    change localTape (base.cells 1) sigma (w.map machine.bitSym) (sigma + (p + 1)) = _
    rw [show sigma + (p + 1) = sigma + p + 1 by omega,local_payload,
      List.getD_eq_getElem _ _ (by simpa using hp),List.getElem_map]
  have hd := part3_rewind_bit_transition
    (fun i => (popRewindFrame base sigma rho tau w (p + 1)).cells i
      ((popRewindFrame base sigma rho tau w (p + 1)).head i)) w[p] hs
  change transition (popRewindFrame base sigma rho tau w (p + 1)).state
    (fun i => (popRewindFrame base sigma rho tau w (p + 1)).cells i
      ((popRewindFrame base sigma rho tau w (p + 1)).head i)) = _ at hd
  apply part3_cfg_ext
  · simp only [MultitapeTM.step,hd]
    rfl
  · simp only [MultitapeTM.step,hd]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,hd]
    funext i
    fin_cases i <;> simp [popRewindFrame,frame]
    all_goals omega

private theorem part3_rewind_marker_transition (a : Fin 4 → Sym) (hs : a 1 = .sep) :
    transition .popRewind a = (.halt,fun i => (a i,if i = 1 then .right else .stay)) := by
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

private theorem part3_rewind_marker_step (base : machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) :
    machine.step (popRewindFrame base sigma rho tau w 0) = popDoneFrame base sigma rho tau w := by
  have hs : (popRewindFrame base sigma rho tau w 0).cells 1
      ((popRewindFrame base sigma rho tau w 0).head 1) = .sep := by
    change localTape (base.cells 1) sigma (w.map machine.bitSym) (sigma + 0) = _
    rw [Nat.add_zero,local_boundary]
  have hd := part3_rewind_marker_transition
    (fun i => (popRewindFrame base sigma rho tau w 0).cells i
      ((popRewindFrame base sigma rho tau w 0).head i)) hs
  change transition (popRewindFrame base sigma rho tau w 0).state
    (fun i => (popRewindFrame base sigma rho tau w 0).cells i
      ((popRewindFrame base sigma rho tau w 0).head i)) = _ at hd
  apply part3_cfg_ext
  · simp only [MultitapeTM.step,hd]
    rfl
  · simp only [MultitapeTM.step,hd]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,hd]
    funext i
    fin_cases i <;> simp [popRewindFrame,popDoneFrame,frame]

private theorem part3_rewind_run (base : machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) (p : ℕ) (hp : p ≤ w.length) :
    machine.step^[p + 1] (popRewindFrame base sigma rho tau w p) = popDoneFrame base sigma rho tau w := by
  induction p with
  | zero => simpa using part3_rewind_marker_step base sigma rho tau w
  | succ p ih => rw [Function.iterate_succ_apply,part3_rewind_bit_step base sigma rho tau w p (by omega),ih (by omega)]

private theorem output_correct (base : machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) :
    machine.step^[2 * w.length + 2] (outputFrame base sigma rho tau w.reverse []) =
      popDoneFrame base sigma rho tau w := by
  have hc := output_reverse_run base sigma rho tau w []
  simp only [List.nil_append] at hc
  rw [show 2 * w.length + 2 = (w.length + 1) + (w.length + 1) by omega,
    Function.iterate_add_apply,hc,part3_rewind_run base sigma rho tau w w.length le_rfl]

end IntMul.TapeStack



namespace IntMul.TapeStack

/-- Pop restores the exact original word, clears the parked suffix and
scratch, and returns all local heads. Older stack prefixes are never scanned. -/
private theorem pop_correct (base : machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) :
    machine.step^[3 * w.length + 5] (popStartFrame base sigma rho tau w) =
      popDoneFrame base sigma rho tau w := by
  have hr := park_reverse_run base sigma rho tau w.reverse []
  simp only [List.reverse_reverse,List.length_reverse,List.nil_append] at hr
  have hp : machine.step^[w.length + 1 + 2] (popStartFrame base sigma rho tau w) =
      outputFrame base sigma rho tau w.reverse [] := by
    rw [Function.iterate_add_apply,pop_enter_correct,hr]
  rw [show 3 * w.length + 5 = (2 * w.length + 2) + (w.length + 1 + 2) by omega,
    Function.iterate_add_apply,hp,output_correct]

/-- The restored frame has the original source word and blank stack/scratch
suffixes; every cell before each local boundary is retained. -/
private theorem pop_saved_data (base : machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) :
    (popDoneFrame base sigma rho tau w).cells 0 = base.cells 0 ∧
    (popDoneFrame base sigma rho tau w).head 0 = base.head 0 ∧
    (∀ p, p < sigma → (popDoneFrame base sigma rho tau w).cells 1 p = base.cells 1 p) ∧
    (∀ p, p < rho → (popDoneFrame base sigma rho tau w).cells 2 p = base.cells 2 p) ∧
    (∀ p, p < tau → (popDoneFrame base sigma rho tau w).cells 3 p = base.cells 3 p) := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · intro p hp
    simp [popDoneFrame,frame,localTape,hp]
  constructor
  · intro p hp
    simp [popDoneFrame,frame,localTape,hp]
  · intro p hp
    simp [popDoneFrame,frame,localTape,hp]

end IntMul.TapeStack



namespace IntMul.TapeStackRoundTrip

/-- Actual finite-control push-to-pop dispatch and final global halt are
included, preserving the complete restored source and older stack prefixes. -/
private theorem round_trip_correct (base : TapeStack.machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) :
    ∃ t : ℕ, t ≤ 5 * w.length + 9 ∧
      machine.step^[t] (initialFrame base sigma rho tau w) = finalFrame base sigma rho tau w := by
  have hp := TapeStack.push_correct base sigma rho tau w
  have hh : (TapeStack.machine.step^[2 * w.length + 2]
      (TapeStack.pushFrame base sigma rho tau w 0)).state = TapeStack.machine.qHalt := by rw [hp]; rfl
  obtain ⟨p,hpbound,hprun⟩ :=
    (FiniteCaller.simulate_run TapeStack.machine Bool false false dispatch
      (TapeStack.pushFrame base sigma rho tau w 0) (2 * w.length + 2)).2 hh
  rw [hp] at hprun
  change machine.step^[p] (initialFrame base sigma rho tau w) =
    FiniteCaller.embed TapeStack.machine Bool false true dispatch
      (TapeStack.popStartFrame base sigma rho tau w) at hprun
  have ho := TapeStack.pop_correct base sigma rho tau w
  have hh₂ : (TapeStack.machine.step^[3 * w.length + 5]
      (TapeStack.popStartFrame base sigma rho tau w)).state = TapeStack.machine.qHalt := by rw [ho]; rfl
  obtain ⟨q,hqbound,hqrun⟩ :=
    (FiniteCaller.simulate_run TapeStack.machine Bool false true dispatch
      (TapeStack.popStartFrame base sigma rho tau w) (3 * w.length + 5)).2 hh₂
  rw [ho] at hqrun
  change machine.step^[q] (FiniteCaller.embed TapeStack.machine Bool false true dispatch
    (TapeStack.popStartFrame base sigma rho tau w)) = finalFrame base sigma rho tau w at hqrun
  refine ⟨q + p,by omega,?_⟩
  rw [Function.iterate_add_apply,hprun,hqrun]

/-- The terminal source is exactly the initial source, and the stack and
scratch are both restored to their original blank suffixes and head offsets. -/
private theorem restored_data (base : TapeStack.machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) :
    (finalFrame base sigma rho tau w).cells = (initialFrame base sigma rho tau w).cells ∧
    (finalFrame base sigma rho tau w).head = (initialFrame base sigma rho tau w).head := by
  constructor
  · funext i
    fin_cases i
    · rfl
    · change TapeStack.localTape (base.cells 1) sigma (w.map TapeStack.machine.bitSym) =
        TapeStack.erasedTape (base.cells 1) sigma w 0
      exact (TapeStack.erased_initial _ _ _).symm
    · rfl
    · rfl
  · funext i
    fin_cases i <;> rfl

end IntMul.TapeStackRoundTrip


open IntMul IntMul.TapeStackRoundTrip

theorem solution (base : TapeStack.machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) :
    ∃ t : ℕ, t ≤ 5 * w.length + 9 ∧
      machine.step^[t] (initialFrame base sigma rho tau w) = finalFrame base sigma rho tau w :=
  IntMul.TapeStackRoundTrip.round_trip_correct base sigma rho tau w

#print axioms solution
