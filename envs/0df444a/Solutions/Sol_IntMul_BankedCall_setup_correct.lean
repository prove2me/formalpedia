-- Prove2me | solution 1 for IntMul.BankedCall.setup_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T21:00:48.165974+00:00
-- url     : https://prove2.me/submissions/9f77bc88-5709-46c7-b700-bce950a1ed84

import Definitions.Def_IntMul_BankedCall
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic


namespace IntMul.BankedCall

private theorem cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem protect_right (M : MultitapeTM) (a : Option M.Sym) :
    BankedSimulation.protect M a (BankedSimulation.decode M a) .right = (a,.right) := by
  cases a <;> rfl

private theorem protect_stay (M : MultitapeTM) (a : Option M.Sym) :
    BankedSimulation.protect M a (BankedSimulation.decode M a) .stay = (a,.stay) := by
  cases a <;> rfl

private theorem protect_left (M : MultitapeTM) (a : Option M.Sym) (h : a ≠ none) :
    BankedSimulation.protect M a (BankedSimulation.decode M a) .left = (a,.left) := by
  cases a with
  | none => exact False.elim (h rfl)
  | some s => rfl

private theorem bit_map_some (M : MultitapeTM) (x : List Bool) :
    (x.map M.bitSym).map some = x.map (machine M).bitSym := by
  rw [List.map_map]
  congr 1
  funext b
  cases b <;> rfl

private theorem init_cells (M : MultitapeTM) (x y : List Bool) (i : Fin (M.k + 2)) :
    ((machine M).initCfg x y).cells i =
      if i.val = 0 then (machine M).tapeOf ((inputWord M x y).map some)
      else (machine M).tapeOf [] := by
  classical
  have hz : i = (machine M).inTape ↔ i.val = 0 := by
    constructor
    · intro h
      exact congrArg Fin.val h
    · intro h
      apply Fin.ext
      exact h
  simp only [MultitapeTM.initCfg,hz,inputWord,List.map_append,List.map_cons,bit_map_some]

private theorem bank_append_one (M : MultitapeTM) (w : List M.Sym) (a : M.Sym) :
    Function.update (bankTape M w) (w.length + 2) (some a) = bankTape M (w ++ [a]) := by
  classical
  funext p
  by_cases he : p = w.length + 2
  · subst p
    simp [bankTape,MultitapeTM.tapeOf]
  · rw [Function.update_of_ne he]
    by_cases hp : p = 0
    · simp [bankTape,hp]
    · simp only [bankTape,if_neg hp]
      cases p with
      | zero => contradiction
      | succ p =>
          simp only [Nat.add_sub_cancel,MultitapeTM.tapeOf]
          cases p with
          | zero => rfl
          | succ p =>
              change some (w.getD p M.blank) = some ((w ++ [a]).getD p M.blank)
              by_cases hlt : p < w.length
              · rw [List.getD_append _ _ _ _ hlt]
              · have hge : w.length ≤ p := by omega
                rw [List.getD_eq_default _ _ hge,List.getD_append_right _ _ _ _ hge]
                rw [List.getD_eq_default _ _ (by simp; omega)]

private noncomputable def markFrame (M : MultitapeTM) (x y : List Bool) : (machine M).Cfg where
  state := .inl .mark
  cells := ((machine M).initCfg x y).cells
  head := fun _ => 1

private noncomputable def copyFrame (M : MultitapeTM) (x y : List Bool) (j : ℕ) : (machine M).Cfg where
  state := .inl .copyInput
  cells := fun i =>
    if i.val = 0 then (machine M).tapeOf ((inputWord M x y).map some)
    else if i.val = 1 then (machine M).tapeOf []
    else if i.val = 2 then bankTape M ((inputWord M x y).take j)
    else bankTape M []
  head := fun i => if i.val = 0 then j + 1 else if i.val = 2 then j + 2 else 1

private noncomputable def returnFrame (M : MultitapeTM) (x y : List Bool) (pos : ℕ) : (machine M).Cfg where
  state := .inl .rewindInput
  cells := (readyFrame M x y).cells
  head := fun i => if i.val = 0 then (inputWord M x y).length + 1 else if i.val = 2 then pos else 1

private theorem start_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Option M.Sym) :
    transition M (.inl .start) a = (.inl .mark,fun i => (a i,.right)) := by
  classical
  simp [transition,rawTransition,protect_right]

private theorem start_step (M : MultitapeTM) (x y : List Bool) :
    (machine M).step ((machine M).initCfg x y) = markFrame M x y := by
  have ht := start_transition M (fun i => ((machine M).initCfg x y).cells i 0)
  change transition M ((machine M).initCfg x y).state
    (fun i => ((machine M).initCfg x y).cells i (((machine M).initCfg x y).head i)) = _ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    rfl

private theorem mark_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Option M.Sym)
    (blank : ∀ i, 2 ≤ i.val → a i = some M.blank) :
    transition M (.inl .mark) a = (.inl .copyInput,fun i =>
      (if 2 ≤ i.val then some M.startSym else a i,if i.val = 2 then .right else .stay)) := by
  classical
  simp only [transition,rawTransition]
  congr 1
  funext i
  by_cases hi : 2 ≤ i.val
  · simp only [if_pos hi]
    rw [blank i hi]
    by_cases he : i.val = 2 <;> simp [he,BankedSimulation.protect,BankedSimulation.decode]
  · have hn : i.val ≠ 2 := by omega
    simp only [if_neg hi,if_neg hn,protect_stay]

private theorem mark_step (M : MultitapeTM) (x y : List Bool) :
    (machine M).step (markFrame M x y) = copyFrame M x y 0 := by
  have hb : ∀ i, 2 ≤ i.val → (markFrame M x y).cells i ((markFrame M x y).head i) = some M.blank := by
    intro i hi
    change ((machine M).initCfg x y).cells i 1 = _
    rw [init_cells,if_neg (by omega : i.val ≠ 0)]
    rfl
  have ht := mark_transition M
    (fun i => (markFrame M x y).cells i ((markFrame M x y).head i)) hb
  change transition M (markFrame M x y).state
    (fun i => (markFrame M x y).cells i ((markFrame M x y).head i)) = _ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : 2 ≤ i.val
    · rw [if_pos hi]
      change Function.update (((machine M).initCfg x y).cells i) 1 (some M.startSym) = _
      rw [init_cells,if_neg (by omega : i.val ≠ 0)]
      have he : (copyFrame M x y 0).cells i = bankTape M [] := by
        simp only [copyFrame,if_neg (by omega : i.val ≠ 0),if_neg (by omega : i.val ≠ 1),
          List.take_zero,ite_self]
      rw [he]
      funext p
      by_cases hp : p = 1
      · subst p
        rfl
      · rw [Function.update_of_ne hp]
        cases p with
        | zero => rfl
        | succ p =>
            cases p with
            | zero => contradiction
            | succ p => rfl
    · rw [if_neg hi]
      change Function.update (((machine M).initCfg x y).cells i) 1
        (((machine M).initCfg x y).cells i 1) = _
      rw [Function.update_eq_self,init_cells]
      have hh : i.val = 0 ∨ i.val = 1 := by omega
      rcases hh with h | h
      · simp only [if_pos h,copyFrame]
      · simp only [if_neg (by omega : i.val ≠ 0),copyFrame,if_pos h]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases he : i.val = 2
    · simp only [markFrame,copyFrame,if_pos he,if_neg (by omega : i.val ≠ 0)]
    · simp only [markFrame,copyFrame,if_neg he,ite_self]

private theorem word_letter (M : MultitapeTM) (x y : List Bool) (a : M.Sym)
    (ha : a ∈ inputWord M x y) : a = M.zero ∨ a = M.one ∨ a = M.sep := by
  simp only [inputWord,List.mem_append,List.mem_cons,List.mem_map] at ha
  rcases ha with ⟨b,_,rfl⟩ | (ha | ⟨b,_,rfl⟩)
  · cases b <;> simp [MultitapeTM.bitSym]
  · exact Or.inr (Or.inr ha)
  · cases b <;> simp [MultitapeTM.bitSym]

private theorem bank_payload (M : MultitapeTM) (w : List M.Sym) (p : ℕ) :
    bankTape M w (p + 2) = some (w.getD p M.blank) := by
  simp [bankTape,MultitapeTM.tapeOf]

private theorem copy_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Option M.Sym)
    (s : M.Sym) (letter : s = M.zero ∨ s = M.one ∨ s = M.sep)
    (source : a ⟨0,by omega⟩ = some s)
    (target : a ⟨2,by have := M.two_le_k; omega⟩ = some M.blank) :
    transition M (.inl .copyInput) a = (.inl .copyInput,fun i =>
      (if i.val = 2 then some s else a i,if i.val = 0 ∨ i.val = 2 then .right else .stay)) := by
  classical
  have hb : a ⟨0,by omega⟩ = some M.zero ∨ a ⟨0,by omega⟩ = some M.one ∨
      a ⟨0,by omega⟩ = some M.sep := by
    rw [source]
    rcases letter with h | h | h <;> simp only [h,or_true,true_or]
  simp only [transition,rawTransition,if_pos hb]
  congr 1
  funext i
  by_cases ht : i.val = 2
  · have he : i = ⟨2,by have := M.two_le_k; omega⟩ := Fin.ext ht
    have hh : i.val = 0 ∨ i.val = 2 := Or.inr ht
    simp only [if_pos ht,if_pos hh]
    rw [he,target,source]
    rfl
  · simp only [if_neg ht]
    by_cases hs : i.val = 0
    · simp only [if_pos (Or.inl hs),protect_right]
    · simp only [if_neg (by tauto : ¬(i.val = 0 ∨ i.val = 2)),protect_stay]

private theorem copy_step (M : MultitapeTM) (x y : List Bool) (j : ℕ)
    (hj : j < (inputWord M x y).length) :
    (machine M).step (copyFrame M x y j) = copyFrame M x y (j + 1) := by
  classical
  let w := inputWord M x y
  have hjw : j < w.length := hj
  have hs : (copyFrame M x y j).cells ⟨0,by change 0 < M.k + 2; omega⟩
      ((copyFrame M x y j).head ⟨0,by change 0 < M.k + 2; omega⟩) = some w[j] := by
    change (w.map some).getD j (some M.blank) = _
    rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]
  have hl : (w.take j).length = j := by simp [Nat.min_eq_left hjw.le]
  have ht : (copyFrame M x y j).cells ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩
      ((copyFrame M x y j).head ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩) = some M.blank := by
    change bankTape M (w.take j) (j + 2) = _
    rw [bank_payload,List.getD_eq_default _ _ (by omega)]
  have hd := copy_transition M
    (fun i => (copyFrame M x y j).cells i ((copyFrame M x y j).head i)) w[j]
      (word_letter M x y w[j] (by exact List.getElem_mem hj)) hs ht
  change transition M (copyFrame M x y j).state
    (fun i => (copyFrame M x y j).cells i ((copyFrame M x y j).head i)) = _ at hd
  apply cfg_ext
  · simp only [MultitapeTM.step,hd]
    rfl
  · simp only [MultitapeTM.step,hd]
    funext i
    by_cases hi : i.val = 2
    · simp only [if_pos hi]
      change Function.update ((copyFrame M x y j).cells i)
        ((copyFrame M x y j).head i) (some w[j]) = _
      simp only [copyFrame,if_neg (by omega : i.val ≠ 0),if_neg (by omega : i.val ≠ 1),if_pos hi]
      change Function.update (bankTape M (w.take j)) (j + 2) (some w[j]) = bankTape M (w.take (j + 1))
      rw [List.take_succ_eq_append_getElem hj]
      simpa only [hl] using bank_append_one M (w.take j) w[j]
    · simp only [if_neg hi]
      rw [Function.update_eq_self]
      simp only [copyFrame,if_neg hi]
  · simp only [MultitapeTM.step,hd]
    funext i
    by_cases hi : i.val = 0
    · have h₂ : i.val ≠ 2 := by omega
      simp only [copyFrame,if_pos hi,if_neg h₂,if_pos (Or.inl hi)]
    · by_cases h₂ : i.val = 2
      · simp only [copyFrame,if_neg hi,if_pos h₂,if_pos (Or.inr h₂)]
      · simp only [copyFrame,if_neg hi,if_neg h₂,if_neg (by tauto : ¬(i.val = 0 ∨ i.val = 2))]

private theorem copy_run (M : MultitapeTM) (x y : List Bool) (j : ℕ)
    (hj : j ≤ (inputWord M x y).length) :
    (machine M).step^[j] (copyFrame M x y 0) = copyFrame M x y j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),copy_step M x y j (by omega)]

private theorem blank_ne_letters (M : MultitapeTM) :
    M.blank ≠ M.zero ∧ M.blank ≠ M.one ∧ M.blank ≠ M.sep := by
  have h := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at h
  aesop

private theorem word_not_start (M : MultitapeTM) (x y : List Bool) (j : ℕ)
    (hj : j < (inputWord M x y).length) : (inputWord M x y)[j] ≠ M.startSym := by
  have h := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at h
  have hl := word_letter M x y (inputWord M x y)[j] (List.getElem_mem hj)
  aesop

private theorem copy_end_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Option M.Sym)
    (source : a ⟨0,by omega⟩ = some M.blank)
    (target : a ⟨2,by have := M.two_le_k; omega⟩ = some M.blank) :
    transition M (.inl .copyInput) a = (.inl .rewindInput,fun i =>
      (a i,if i.val = 2 then .left else .stay)) := by
  classical
  have hb : ¬(a ⟨0,by omega⟩ = some M.zero ∨ a ⟨0,by omega⟩ = some M.one ∨
      a ⟨0,by omega⟩ = some M.sep) := by
    rw [source]
    simp only [Option.some.injEq,not_or]
    exact blank_ne_letters M
  simp only [transition,rawTransition,if_neg hb]
  congr 1
  funext i
  by_cases hi : i.val = 2
  · simp only [if_pos hi]
    have he : i = ⟨2,by have := M.two_le_k; omega⟩ := Fin.ext hi
    rw [he,target]
    rfl
  · simp only [if_neg hi,protect_stay]

private theorem copy_end_step (M : MultitapeTM) (x y : List Bool) :
    (machine M).step (copyFrame M x y (inputWord M x y).length) =
      returnFrame M x y ((inputWord M x y).length + 1) := by
  let w := inputWord M x y
  change (machine M).step (copyFrame M x y w.length) = returnFrame M x y (w.length + 1)
  have hs : (copyFrame M x y w.length).cells ⟨0,by change 0 < M.k + 2; omega⟩
      ((copyFrame M x y w.length).head ⟨0,by change 0 < M.k + 2; omega⟩) = some M.blank := by
    change (w.map some).getD w.length (some M.blank) = _
    exact List.getD_eq_default _ _ (by simp)
  have ht : (copyFrame M x y w.length).cells ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩
      ((copyFrame M x y w.length).head ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩) = some M.blank := by
    change bankTape M (w.take w.length) (w.length + 2) = _
    rw [List.take_length,bank_payload,List.getD_eq_default _ _ le_rfl]
  have hd := copy_end_transition M
    (fun i => (copyFrame M x y w.length).cells i ((copyFrame M x y w.length).head i)) hs ht
  change transition M (copyFrame M x y w.length).state
    (fun i => (copyFrame M x y w.length).cells i ((copyFrame M x y w.length).head i)) = _ at hd
  apply cfg_ext
  · simp only [MultitapeTM.step,hd]
    rfl
  · simp only [MultitapeTM.step,hd]
    funext i
    rw [Function.update_eq_self]
    simp only [w,copyFrame,returnFrame,readyFrame,List.take_length]
  · simp only [MultitapeTM.step,hd]
    funext i
    by_cases hi : i.val = 0
    · simp only [w,copyFrame,returnFrame,if_pos hi,if_neg (by omega : i.val ≠ 2)]
    · by_cases h₂ : i.val = 2
      · simp only [copyFrame,returnFrame,if_neg hi,if_pos h₂]
        omega
      · simp only [copyFrame,returnFrame,if_neg hi,if_neg h₂]

private theorem return_left_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Option M.Sym)
    (h : a ⟨2,by have := M.two_le_k; omega⟩ ≠ some M.startSym)
    (hn : a ⟨2,by have := M.two_le_k; omega⟩ ≠ none) :
    transition M (.inl .rewindInput) a = (.inl .rewindInput,fun i =>
      (a i,if i.val = 2 then .left else .stay)) := by
  classical
  simp only [transition,rawTransition,if_neg h]
  congr 1
  funext i
  by_cases hi : i.val = 2
  · simp only [if_pos hi]
    have he : i = ⟨2,by have := M.two_le_k; omega⟩ := Fin.ext hi
    rw [he]
    exact protect_left M _ hn
  · simp only [if_neg hi,protect_stay]

private theorem return_left_step (M : MultitapeTM) (x y : List Bool) (j : ℕ)
    (hj : j < (inputWord M x y).length) :
    (machine M).step (returnFrame M x y (j + 2)) = returnFrame M x y (j + 1) := by
  let w := inputWord M x y
  have hr : (returnFrame M x y (j + 2)).cells ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩
      ((returnFrame M x y (j + 2)).head ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩) = some w[j] := by
    change bankTape M w (j + 2) = _
    rw [bank_payload,List.getD_eq_getElem _ _ hj]
  have hm : (returnFrame M x y (j + 2)).cells ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩
      ((returnFrame M x y (j + 2)).head ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩) ≠ some M.startSym := by
    rw [hr]
    exact fun he => word_not_start M x y j hj (Option.some.inj he)
  have hn : (returnFrame M x y (j + 2)).cells ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩
      ((returnFrame M x y (j + 2)).head ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩) ≠ none := by
    rw [hr]
    exact Option.some_ne_none _
  have hd := return_left_transition M
    (fun i => (returnFrame M x y (j + 2)).cells i ((returnFrame M x y (j + 2)).head i)) hm hn
  change transition M (returnFrame M x y (j + 2)).state
    (fun i => (returnFrame M x y (j + 2)).cells i ((returnFrame M x y (j + 2)).head i)) = _ at hd
  apply cfg_ext
  · simp only [MultitapeTM.step,hd]
    rfl
  · simp only [MultitapeTM.step,hd]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,hd]
    funext i
    by_cases hi : i.val = 0
    · simp only [returnFrame,if_pos hi,if_neg (by omega : i.val ≠ 2)]
    · by_cases h₂ : i.val = 2
      · simp only [returnFrame,if_neg hi,if_pos h₂]
        omega
      · simp only [returnFrame,if_neg hi,if_neg h₂]

private theorem return_marker_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Option M.Sym)
    (h : a ⟨2,by have := M.two_le_k; omega⟩ = some M.startSym) :
    transition M (.inl .rewindInput) a = (.inr M.qStart,fun i => (a i,.stay)) := by
  classical
  simp [transition,rawTransition,h,protect_stay]

private theorem return_marker_step (M : MultitapeTM) (x y : List Bool) :
    (machine M).step (returnFrame M x y 1) = readyFrame M x y := by
  have hr : (returnFrame M x y 1).cells ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩
      ((returnFrame M x y 1).head ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩) = some M.startSym := rfl
  have hd := return_marker_transition M
    (fun i => (returnFrame M x y 1).cells i ((returnFrame M x y 1).head i)) hr
  change transition M (returnFrame M x y 1).state
    (fun i => (returnFrame M x y 1).cells i ((returnFrame M x y 1).head i)) = _ at hd
  apply cfg_ext
  · simp only [MultitapeTM.step,hd]
    rfl
  · simp only [MultitapeTM.step,hd]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,hd]
    funext i
    by_cases hi : i.val = 0
    · simp only [returnFrame,readyFrame,if_pos hi,inputWord,List.length_append,List.length_map,List.length_cons]
      omega
    · simp only [returnFrame,readyFrame,if_neg hi,ite_self]

private theorem return_run (M : MultitapeTM) (x y : List Bool) (p : ℕ)
    (hp : p ≤ (inputWord M x y).length) :
    (machine M).step^[p + 1] (returnFrame M x y (p + 1)) = readyFrame M x y := by
  induction p with
  | zero => simpa using return_marker_step M x y
  | succ p ih => rw [Function.iterate_succ_apply,return_left_step M x y p (by omega),ih (by omega)]

/-- The child input and every work-tape local marker are physically prepared
from the real outer initial configuration, with every write and seek charged. -/
private theorem setup_correct (M : MultitapeTM) (x y : List Bool) :
    (machine M).step^[2 * x.length + 2 * y.length + 6] ((machine M).initCfg x y) =
      readyFrame M x y := by
  let w := inputWord M x y
  have hlen : w.length = x.length + y.length + 1 := by simp [w,inputWord]; omega
  have hstart : (machine M).step^[2] ((machine M).initCfg x y) = copyFrame M x y 0 := by
    rw [show 2 = 1 + 1 by rfl,Function.iterate_add_apply,Function.iterate_one,start_step,mark_step]
  have hcopy : (machine M).step^[w.length + 3] ((machine M).initCfg x y) = returnFrame M x y (w.length + 1) := by
    rw [show w.length + 3 = (w.length + 2) + 1 by omega,
      Function.iterate_succ_apply',Function.iterate_add_apply,hstart,copy_run M x y w.length le_rfl,copy_end_step]
  rw [show 2 * x.length + 2 * y.length + 6 = (w.length + 1) + (w.length + 3) by omega,
    Function.iterate_add_apply,hcopy,return_run M x y w.length le_rfl]

end IntMul.BankedCall


open IntMul IntMul.BankedCall

theorem solution (M : MultitapeTM) (x y : List Bool) :
    (machine M).step^[2 * x.length + 2 * y.length + 6] ((machine M).initCfg x y) =
      readyFrame M x y :=
  IntMul.BankedCall.setup_correct M x y

#print axioms solution
