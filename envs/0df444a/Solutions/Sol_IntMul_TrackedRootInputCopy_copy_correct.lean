-- Prove2me | solution 1 for IntMul.TrackedRootInputCopy.copy_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T23:09:08.110048+00:00
-- url     : https://prove2.me/submissions/f73634ed-a82c-4620-a650-a069501cdb90

import Definitions.Def_IntMul_TrackedRootInputCopy
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic
open IntMul.TrackedBankPreparation (inputWord)


namespace IntMul.TrackedRootInputCopy

open IntMul.TrackedBankedSimulation (Sym)
open IntMul.TrackedBankPreparation (sourceTape inputWord)

/-- The reserved buffer boundary stays physically fresh until child setup. -/
private theorem source_boundary (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List M.Sym) :
    sourceTape M base sigma w sigma = some (M.blank,false) := by simp [sourceTape]

private theorem source_payload (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ)
    (w : List M.Sym) (p : ℕ) :
    sourceTape M base sigma w (sigma + p + 1) = some (w.getD p M.blank,decide (p < w.length)) := by
  simp only [sourceTape,if_neg (by omega : ¬sigma + p + 1 < sigma),
    if_neg (by omega : sigma + p + 1 ≠ sigma),show sigma + p + 1 - sigma - 1 = p by omega]

private theorem source_append (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ)
    (w : List M.Sym) (a : M.Sym) :
    Function.update (sourceTape M base sigma w) (sigma + w.length + 1) (some (a,true)) =
      sourceTape M base sigma (w ++ [a]) := by
  classical
  funext p
  by_cases hp : p < sigma
  · rw [Function.update_of_ne (by omega : p ≠ sigma + w.length + 1)]
    simp only [sourceTape,if_pos hp]
  · by_cases he : p = sigma + w.length + 1
    · subst p
      rw [Function.update_self,source_payload]
      simp
    · rw [Function.update_of_ne he]
      by_cases hs : p = sigma
      · subst p
        rw [source_boundary,source_boundary]
      · have hn : p = sigma + (p - sigma - 1) + 1 := by omega
        rw [hn,source_payload,source_payload]
        have hq : p - sigma - 1 ≠ w.length := by omega
        simp only [List.length_append,List.length_singleton]
        by_cases hl : p - sigma - 1 < w.length
        · rw [List.getD_append _ _ _ _ hl]
          simp only [hl,show p - sigma - 1 < w.length + 1 by omega,decide_true]
        · have hb : w.length ≤ p - sigma - 1 := by omega
          rw [List.getD_eq_default _ _ hb,List.getD_append_right _ _ _ _ hb,
            List.getD_eq_default _ _ (by simp; omega)]
          simp only [hl,show ¬p - sigma - 1 < w.length + 1 by omega,decide_false]

private theorem tagged_input_word (M : MultitapeTM) (x y : List Bool) :
    x.map (machine M).bitSym ++ (machine M).sep :: y.map (machine M).bitSym =
      (inputWord M x y).map (fun s => some (s,true)) := by
  have h : (machine M).bitSym = fun b => some (M.bitSym b,true) := by
    funext b
    cases b <;> rfl
  simp only [inputWord,List.map_append,List.map_cons,List.map_map,h]
  rfl

private theorem initial_input_payload (M : MultitapeTM) (x y : List Bool) (j : ℕ)
    (hj : j < (inputWord M x y).length) :
    ((machine M).initCfg x y).cells ⟨0,by change 0 < M.k + 2; omega⟩ (j + 1) =
      some ((inputWord M x y)[j],true) := by
  change (x.map (machine M).bitSym ++ (machine M).sep :: y.map (machine M).bitSym).getD j (some (M.blank,false)) = _
  rw [tagged_input_word,List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]

private theorem initial_input_end (M : MultitapeTM) (x y : List Bool) :
    ((machine M).initCfg x y).cells ⟨0,by change 0 < M.k + 2; omega⟩
      ((inputWord M x y).length + 1) = some (M.blank,false) := by
  change (x.map (machine M).bitSym ++ (machine M).sep :: y.map (machine M).bitSym).getD
    (inputWord M x y).length (some (M.blank,false)) = _
  rw [tagged_input_word]
  exact List.getD_eq_default _ _ (by simp)

private theorem initial_empty (M : MultitapeTM) (x y : List Bool) (i : Fin (M.k + 2)) (hi : i.val ≠ 0) :
    ((machine M).initCfg x y).cells i = (machine M).tapeOf [] := by
  simp only [MultitapeTM.initCfg]
  rw [if_neg (by intro h; exact hi (congrArg Fin.val h))]

private theorem source_empty_initial (M : MultitapeTM) (x y : List Bool) (i : Fin (M.k + 2)) (hi : i.val ≠ 0) :
    sourceTape M (((machine M).initCfg x y).cells i) 1 [] = ((machine M).initCfg x y).cells i := by
  rw [initial_empty M x y i hi]
  funext p
  cases p with
  | zero => simp [sourceTape,MultitapeTM.tapeOf]
  | succ p => simp [sourceTape,MultitapeTM.tapeOf]

private theorem source_global_marker (M : MultitapeTM) (x y : List Bool) (i : Fin (M.k + 2)) :
    sourceTape M (((machine M).initCfg x y).cells i) 1 (inputWord M x y) 0 = none := by
  simp only [sourceTape,show 0 < 1 by omega,if_true,MultitapeTM.initCfg]
  split <;> rfl

private theorem source_nonzero (M : MultitapeTM) (base : ℕ → Sym M) (w : List M.Sym) (p : ℕ)
    (hp : 0 < p) : sourceTape M base 1 w p ≠ none := by
  by_cases he : p = 1
  · subst p
    simp [sourceTape]
  · simp [sourceTape,show ¬p < 1 by omega,he]

private theorem tape_word_letter (M : MultitapeTM) (x y : List Bool) (a : M.Sym)
    (ha : a ∈ inputWord M x y) : a = M.zero ∨ a = M.one ∨ a = M.sep := by
  simp only [inputWord,List.mem_append,List.mem_cons,List.mem_map] at ha
  rcases ha with ⟨b,_,rfl⟩ | (ha | ⟨b,_,rfl⟩)
  · cases b <;> simp [MultitapeTM.bitSym]
  · exact Or.inr (Or.inr ha)
  · cases b <;> simp [MultitapeTM.bitSym]

private theorem word_index_letter (M : MultitapeTM) (x y : List Bool) (j : ℕ)
    (hj : j < (inputWord M x y).length) :
    (inputWord M x y)[j] = M.zero ∨ (inputWord M x y)[j] = M.one ∨ (inputWord M x y)[j] = M.sep :=
  tape_word_letter M x y _ (List.getElem_mem hj)

end IntMul.TrackedRootInputCopy



namespace IntMul.TrackedRootInputCopy

open IntMul.TrackedBankedSimulation (Sym)
open IntMul.TrackedBankPreparation (inputWord sourceTape)

private theorem copy_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem copy_protect_right (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .right = (a,.right) := by cases a <;> rfl

private theorem copy_protect_stay (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .stay = (a,.stay) := by cases a <;> rfl

private theorem start_step (M : MultitapeTM) (x y : List Bool) :
    (machine M).step ((machine M).initCfg x y) = gapFrame M x y := by
  have ht : ∀ a, transition M .start a = (.gap,fun i => (a i,.right)) := by
    intro a
    simp only [transition,rawTransition,copy_protect_right]
  apply copy_cfg_ext
  · simp only [MultitapeTM.step,MultitapeTM.initCfg,ht,gapFrame]
  · funext i
    simp only [MultitapeTM.step,MultitapeTM.initCfg,ht,gapFrame]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,MultitapeTM.initCfg,ht,gapFrame]

private theorem gap_step (M : MultitapeTM) (x y : List Bool) :
    (machine M).step (gapFrame M x y) = copyFrame M x y 0 := by
  have ht : ∀ a, transition M .gap a = (.copy,fun i => (a i,if i.val = 1 then .right else .stay)) := by
    intro a
    simp only [transition,rawTransition]
    congr 1
    funext i
    split <;> first | exact copy_protect_right M _ | exact copy_protect_stay M _
  apply copy_cfg_ext
  · simp [MultitapeTM.step,gapFrame,copyFrame,ht]
  · funext i
    simp only [MultitapeTM.step,gapFrame,ht,Function.update_eq_self,copyFrame,List.take_zero]
    by_cases hi : i.val = 1
    · simp only [if_pos hi]
      exact (source_empty_initial M x y i (by omega)).symm
    · simp only [if_neg hi]
  · funext i
    simp only [MultitapeTM.step,gapFrame,ht,copyFrame]
    by_cases hi : i.val = 1
    · simp [hi]
    · simp [hi]

private theorem copy_copy_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Sym M)
    (s : M.Sym) (letter : s = M.zero ∨ s = M.one ∨ s = M.sep)
    (source : a ⟨0,by change 0 < M.k + 2; omega⟩ = some (s,true))
    (target : a ⟨1,by change 1 < M.k + 2; omega⟩ = some (M.blank,false)) :
    transition M .copy a = (.copy,fun i =>
      (if i.val = 1 then some (s,true) else a i,if i.val = 0 ∨ i.val = 1 then .right else .stay)) := by
  classical
  have hb : TrackedBankedSimulation.decode M (a ⟨0,by change 0 < M.k + 2; omega⟩) = M.zero ∨
      TrackedBankedSimulation.decode M (a ⟨0,by change 0 < M.k + 2; omega⟩) = M.one ∨
      TrackedBankedSimulation.decode M (a ⟨0,by change 0 < M.k + 2; omega⟩) = M.sep := by
    rw [source]
    simp only [TrackedBankedSimulation.decode]
    rcases letter with h | h | h <;> simp only [h,or_true,true_or]
  simp only [transition,rawTransition,if_pos hb]
  congr 1
  funext i
  by_cases hi : i.val = 1
  · have he : i = ⟨1,by change 1 < M.k + 2; omega⟩ := Fin.ext hi
    simp only [if_pos hi,if_pos (Or.inr hi)]
    rw [he,target,source]
    rfl
  · simp only [if_neg hi]
    split
    · exact copy_protect_right M _
    · exact copy_protect_stay M _

/-- Each copy transition reads one real input symbol and writes one mutable
buffer cell. The input is unchanged and every other bank stays fresh. -/
private theorem copy_step (M : MultitapeTM) (x y : List Bool) (j : ℕ)
    (hj : j < (inputWord M x y).length) :
    (machine M).step (copyFrame M x y j) = copyFrame M x y (j + 1) := by
  let w := inputWord M x y
  have hjw : j < w.length := hj
  have hl : (w.take j).length = j := by simp [Nat.min_eq_left hjw.le]
  have hs : (copyFrame M x y j).cells ⟨0,by change 0 < M.k + 2; omega⟩
      ((copyFrame M x y j).head ⟨0,by change 0 < M.k + 2; omega⟩) = some (w[j],true) := by
    change ((machine M).initCfg x y).cells ⟨0,by change 0 < M.k + 2; omega⟩ (j + 1) = _
    exact initial_input_payload M x y j hj
  have hd : (copyFrame M x y j).cells ⟨1,by change 1 < M.k + 2; omega⟩
      ((copyFrame M x y j).head ⟨1,by change 1 < M.k + 2; omega⟩) = some (M.blank,false) := by
    change sourceTape M (((machine M).initCfg x y).cells ⟨1,by change 1 < M.k + 2; omega⟩) 1 (w.take j) (j + 2) = _
    have hread := source_payload M (((machine M).initCfg x y).cells ⟨1,by change 1 < M.k + 2; omega⟩) 1 (w.take j) j
    simpa only [hl,show 1 + j + 1 = j + 2 by omega,List.getD_eq_default _ _ (by omega : (w.take j).length ≤ j),
      show ¬j < j by omega,decide_false] using hread
  have ht := copy_copy_transition M
    (fun i => (copyFrame M x y j).cells i ((copyFrame M x y j).head i)) w[j]
    (word_index_letter M x y j hj) hs hd
  change transition M (copyFrame M x y j).state
    (fun i => (copyFrame M x y j).cells i ((copyFrame M x y j).head i)) = _ at ht
  apply copy_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · funext i
    simp only [MultitapeTM.step,ht]
    by_cases hi : i.val = 1
    · simp only [if_pos hi,copyFrame,if_pos hi,if_neg (by omega : i.val ≠ 0)]
      change Function.update (sourceTape M (((machine M).initCfg x y).cells i) 1 (w.take j))
        (j + 2) (some (w[j],true)) = sourceTape M (((machine M).initCfg x y).cells i) 1 (w.take (j + 1))
      rw [List.take_succ_eq_append_getElem hjw]
      simpa only [hl,show 1 + j + 1 = j + 2 by omega] using
        source_append M (((machine M).initCfg x y).cells i) 1 (w.take j) w[j]
    · simp only [if_neg hi]
      rw [Function.update_eq_self]
      simp only [copyFrame,if_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    simp only [copyFrame]
    by_cases hz : i.val = 0
    · simp [hz]
    · by_cases hi : i.val = 1
      · simp [hz,hi]
      · simp [hz,hi]

private theorem copy_run (M : MultitapeTM) (x y : List Bool) (j : ℕ)
    (hj : j ≤ (inputWord M x y).length) :
    (machine M).step^[j] (copyFrame M x y 0) = copyFrame M x y j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),copy_step M x y j (by omega)]

end IntMul.TrackedRootInputCopy



namespace IntMul.TrackedRootInputCopy

open IntMul.TrackedBankedSimulation (Sym)
open IntMul.TrackedBankPreparation (inputWord sourceTape)

private theorem rewind_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem rewind_protect_stay (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .stay = (a,.stay) := by cases a <;> rfl

private theorem rewind_protect_right (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .right = (a,.right) := by cases a <;> rfl

private theorem rewind_protect_left (M : MultitapeTM) (a : Sym M) (ha : a ≠ none) :
    TrackedBankCleanup.protect M a a .left = (a,.left) := by
  cases a with
  | none => exact False.elim (ha rfl)
  | some s => rfl

private theorem rewind_blank_not_letter (M : MultitapeTM) :
    ¬(M.blank = M.zero ∨ M.blank = M.one ∨ M.blank = M.sep) := by
  have h := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at h
  aesop

private theorem rewind_copy_end_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Sym M)
    (h0 : a ⟨0,by change 0 < M.k + 2; omega⟩ = some (M.blank,false))
    (h1 : a ⟨1,by change 1 < M.k + 2; omega⟩ ≠ none) :
    transition M .copy a = (.rewind,fun i => (a i,if i.val = 1 then .left else .stay)) := by
  classical
  have hn : ¬(TrackedBankedSimulation.decode M (a ⟨0,by change 0 < M.k + 2; omega⟩) = M.zero ∨
      TrackedBankedSimulation.decode M (a ⟨0,by change 0 < M.k + 2; omega⟩) = M.one ∨
      TrackedBankedSimulation.decode M (a ⟨0,by change 0 < M.k + 2; omega⟩) = M.sep) := by
    rw [h0]
    exact rewind_blank_not_letter M
  simp only [transition,rawTransition,if_neg hn]
  congr 1
  funext i
  by_cases hi : i.val = 1
  · have he : i = ⟨1,by change 1 < M.k + 2; omega⟩ := Fin.ext hi
    simp only [if_pos hi]
    exact rewind_protect_left M (a i) (by simpa only [he] using h1)
  · simp only [if_neg hi,rewind_protect_stay]

private theorem copy_end (M : MultitapeTM) (x y : List Bool) :
    (machine M).step (copyFrame M x y (inputWord M x y).length) =
      rewindFrame M x y ((inputWord M x y).length + 1) := by
  have h0 : (copyFrame M x y (inputWord M x y).length).cells ⟨0,by change 0 < M.k + 2; omega⟩
      ((copyFrame M x y (inputWord M x y).length).head ⟨0,by change 0 < M.k + 2; omega⟩) = some (M.blank,false) := by
    change ((machine M).initCfg x y).cells ⟨0,by change 0 < M.k + 2; omega⟩ ((inputWord M x y).length + 1) = _
    exact initial_input_end M x y
  have h1 : (copyFrame M x y (inputWord M x y).length).cells ⟨1,by change 1 < M.k + 2; omega⟩
      ((copyFrame M x y (inputWord M x y).length).head ⟨1,by change 1 < M.k + 2; omega⟩) ≠ none := by
    change sourceTape M (((machine M).initCfg x y).cells ⟨1,by change 1 < M.k + 2; omega⟩) 1 ((inputWord M x y).take (inputWord M x y).length)
      ((inputWord M x y).length + 2) ≠ none
    exact source_nonzero M _ _ _ (by omega)
  have ht := rewind_copy_end_transition M
    (fun i => (copyFrame M x y (inputWord M x y).length).cells i
      ((copyFrame M x y (inputWord M x y).length).head i)) h0 h1
  change transition M (copyFrame M x y (inputWord M x y).length).state _ = _ at ht
  apply rewind_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · funext i
    simp only [MultitapeTM.step,ht,rewindFrame,Function.update_eq_self]
  · simp only [MultitapeTM.step,ht]
    funext i
    simp only [copyFrame,rewindFrame]
    by_cases hz : i.val = 0
    · simp [hz]
    · by_cases hi : i.val = 1
      · simp [hz,hi]
      · simp [hz,hi]

private theorem rewind_rewind_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Sym M)
    (h : a ⟨1,by change 1 < M.k + 2; omega⟩ ≠ none) :
    transition M .rewind a = (.rewind,fun i => (a i,if i.val = 1 then .left else .stay)) := by
  classical
  simp only [transition,rawTransition,if_neg h]
  congr 1
  funext i
  by_cases hi : i.val = 1
  · have he : i = ⟨1,by change 1 < M.k + 2; omega⟩ := Fin.ext hi
    simp only [if_pos hi]
    exact rewind_protect_left M _ (by simpa only [he] using h)
  · simp only [if_neg hi,rewind_protect_stay]

private theorem rewind_step (M : MultitapeTM) (x y : List Bool) (p : ℕ) (hp : 0 < p) :
    (machine M).step (rewindFrame M x y p) = rewindFrame M x y (p - 1) := by
  have hb : (rewindFrame M x y p).cells ⟨1,by change 1 < M.k + 2; omega⟩
      ((rewindFrame M x y p).head ⟨1,by change 1 < M.k + 2; omega⟩) ≠ none := by
    change sourceTape M (((machine M).initCfg x y).cells ⟨1,by change 1 < M.k + 2; omega⟩) 1 ((inputWord M x y).take (inputWord M x y).length) p ≠ none
    exact source_nonzero M _ _ p hp
  have ht := rewind_rewind_transition M
    (fun i => (rewindFrame M x y p).cells i ((rewindFrame M x y p).head i)) hb
  change transition M (rewindFrame M x y p).state _ = _ at ht
  apply rewind_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    simp only [Function.update_eq_self,rewindFrame]
  · simp only [MultitapeTM.step,ht]
    funext i
    simp only [rewindFrame]
    by_cases hz : i.val = 0
    · simp [hz]
    · by_cases hi : i.val = 1
      · simp [hz,hi]
      · simp [hz,hi]

private theorem rewind_run (M : MultitapeTM) (x y : List Bool) (p : ℕ) :
    (machine M).step^[p] (rewindFrame M x y p) = rewindFrame M x y 0 := by
  induction p with
  | zero => rfl
  | succ p ih =>
      rw [Function.iterate_succ_apply,rewind_step M x y (p + 1) (by omega)]
      simpa only [Nat.add_sub_cancel] using ih

private theorem rewind_end (M : MultitapeTM) (x y : List Bool) :
    (machine M).step (rewindFrame M x y 0) = finalFrame M x y := by
  have hb : (rewindFrame M x y 0).cells ⟨1,by change 1 < M.k + 2; omega⟩
      ((rewindFrame M x y 0).head ⟨1,by change 1 < M.k + 2; omega⟩) = none := by
    change sourceTape M (((machine M).initCfg x y).cells ⟨1,by change 1 < M.k + 2; omega⟩) 1 ((inputWord M x y).take (inputWord M x y).length) 0 = none
    rw [List.take_length]
    exact source_global_marker M x y _
  have ht : transition M .rewind
      (fun i => (rewindFrame M x y 0).cells i ((rewindFrame M x y 0).head i)) =
      (.halt,fun i => ((rewindFrame M x y 0).cells i ((rewindFrame M x y 0).head i),
        if i.val = 1 then .right else .stay)) := by
    simp only [transition,rawTransition,if_pos hb]
    congr 1
    funext i
    split <;> first | exact rewind_protect_right M _ | exact rewind_protect_stay M _
  change transition M (rewindFrame M x y 0).state _ = _ at ht
  apply rewind_cfg_ext
  · simp only [MultitapeTM.step,ht,finalFrame]
  · simp only [MultitapeTM.step,ht]
    funext i
    simp only [Function.update_eq_self,finalFrame,rewindFrame]
  · simp only [MultitapeTM.step,ht]
    funext i
    simp only [rewindFrame,finalFrame]
    by_cases hz : i.val = 0
    · simp [hz]
    · by_cases hi : i.val = 1
      · simp [hz,hi]
      · simp [hz,hi]

/-- From the machine's real native initial configuration, physically copy
the entire x#y word, retain root input, rewind the mutable buffer and park
all fresh child heads at cell one in exactly 2*inputLength+5 transitions. -/
private theorem copy_correct (M : MultitapeTM) (x y : List Bool) :
    (machine M).step^[2 * (inputWord M x y).length + 5] ((machine M).initCfg x y) =
      finalFrame M x y := by
  have hstart : (machine M).step^[2] ((machine M).initCfg x y) = copyFrame M x y 0 := by
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',Function.iterate_zero_apply,start_step,gap_step]
  have hcopy : (machine M).step^[(inputWord M x y).length + 2] ((machine M).initCfg x y) =
      copyFrame M x y (inputWord M x y).length := by
    rw [Function.iterate_add_apply,hstart,copy_run M x y _ le_rfl]
  have hdispatch : (machine M).step^[(inputWord M x y).length + 3] ((machine M).initCfg x y) =
      rewindFrame M x y ((inputWord M x y).length + 1) := by
    rw [show (inputWord M x y).length + 3 = ((inputWord M x y).length + 2) + 1 by omega,
      Function.iterate_succ_apply',hcopy,copy_end]
  have hrewind : (machine M).step^[2 * (inputWord M x y).length + 4] ((machine M).initCfg x y) =
      rewindFrame M x y 0 := by
    rw [show 2 * (inputWord M x y).length + 4 =
      ((inputWord M x y).length + 1) + ((inputWord M x y).length + 3) by omega,
      Function.iterate_add_apply,hdispatch,rewind_run]
  rw [show 2 * (inputWord M x y).length + 5 = (2 * (inputWord M x y).length + 4) + 1 by omega,
    Function.iterate_succ_apply',hrewind,rewind_end]

end IntMul.TrackedRootInputCopy


open IntMul IntMul.TrackedRootInputCopy

theorem solution (M : MultitapeTM) (x y : List Bool) :
    (machine M).step^[2 * (inputWord M x y).length + 5] ((machine M).initCfg x y) =
      finalFrame M x y :=
  IntMul.TrackedRootInputCopy.copy_correct M x y

#print axioms solution
