-- Prove2me | solution 1 for IntMul.InteriorBankedCall.setup_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T21:30:59.326335+00:00
-- url     : https://prove2.me/submissions/876df5c5-76c1-4f43-9417-6fee5923fbc8

import Definitions.Def_IntMul_InteriorBankedCall
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic


namespace IntMul.InteriorBankedCall

private theorem bank_boundary (M : MultitapeTM) (base : ℕ → Option M.Sym) (offset : ℕ) (w : List M.Sym) :
    bankTape M base offset w offset = some M.startSym := by
  simp [bankTape,MultitapeTM.tapeOf]

private theorem bank_payload (M : MultitapeTM) (base : ℕ → Option M.Sym) (offset : ℕ)
    (w : List M.Sym) (p : ℕ) :
    bankTape M base offset w (offset + p + 1) = some (w.getD p M.blank) := by
  rw [bankTape,if_neg (by omega),show offset + p + 1 - offset = p + 1 by omega]
  rfl

private theorem bank_append_one (M : MultitapeTM) (base : ℕ → Option M.Sym) (offset : ℕ)
    (w : List M.Sym) (a : M.Sym) :
    Function.update (bankTape M base offset w) (offset + w.length + 1) (some a) =
      bankTape M base offset (w ++ [a]) := by
  classical
  funext p
  by_cases hp : p < offset
  · rw [Function.update_of_ne (by omega : p ≠ offset + w.length + 1)]
    simp only [bankTape,if_pos hp]
  · by_cases he : p = offset + w.length + 1
    · subst p
      rw [Function.update_self,bank_payload]
      simp
    · rw [Function.update_of_ne he]
      simp only [bankTape,if_neg hp]
      cases hq : p - offset with
      | zero => rfl
      | succ q =>
          change some (w.getD q M.blank) = some ((w ++ [a]).getD q M.blank)
          by_cases hlt : q < w.length
          · rw [List.getD_append _ _ _ _ hlt]
          · have hge : w.length ≤ q := by omega
            rw [List.getD_eq_default _ _ hge,List.getD_append_right _ _ _ _ hge,
              List.getD_eq_default _ _ (by simp; omega)]

private theorem fresh_mark (M : MultitapeTM) (base : ℕ → Option M.Sym) (offset : ℕ) :
    Function.update (freshTape M base offset) offset (some M.startSym) = bankTape M base offset [] := by
  classical
  funext p
  by_cases he : p = offset
  · subst p
    rw [Function.update_self,bank_boundary]
  · rw [Function.update_of_ne he]
    by_cases hp : p < offset
    · simp only [freshTape,bankTape,if_pos hp]
    · simp only [freshTape,bankTape,if_neg hp]
      have hg : 0 < p - offset := by omega
      cases hq : p - offset with
      | zero => omega
      | succ q => rfl

private theorem source_mark (M : MultitapeTM) (base : ℕ → Option M.Sym) (sigma : ℕ) (w : List M.Sym) :
    Function.update (sourceTape M base sigma w) sigma (some M.startSym) = copyTape M base sigma w 0 := by
  classical
  funext p
  by_cases he : p = sigma
  · subst p
    simp [copyTape]
  · rw [Function.update_of_ne he]
    by_cases hp : p < sigma
    · simp only [sourceTape,copyTape,if_pos hp]
    · simp only [sourceTape,copyTape,if_neg hp,if_neg he,if_neg (by omega : ¬p < sigma + 0 + 1)]

private theorem copy_read (M : MultitapeTM) (base : ℕ → Option M.Sym) (sigma : ℕ)
    (w : List M.Sym) (j : ℕ) :
    copyTape M base sigma w j (sigma + j + 1) = some (w.getD j M.blank) := by
  simp only [copyTape,if_neg (by omega : ¬sigma + j + 1 < sigma),
    if_neg (by omega : sigma + j + 1 ≠ sigma),if_neg (by omega : ¬sigma + j + 1 < sigma + j + 1)]
  congr 2
  omega

private theorem copy_erase (M : MultitapeTM) (base : ℕ → Option M.Sym) (sigma : ℕ)
    (w : List M.Sym) (j : ℕ) :
    Function.update (copyTape M base sigma w j) (sigma + j + 1) (some M.blank) =
      copyTape M base sigma w (j + 1) := by
  classical
  funext p
  by_cases he : p = sigma + j + 1
  · subst p
    simp [copyTape,show ¬sigma + j + 1 < sigma by omega,show sigma + j + 1 ≠ sigma by omega]
  · rw [Function.update_of_ne he]
    by_cases hp : p < sigma
    · simp only [copyTape,if_pos hp]
    · by_cases hs : p = sigma
      · simp only [copyTape,if_neg hp,if_pos hs]
      · simp only [copyTape,if_neg hp,if_neg hs]
        by_cases hj : p < sigma + j + 1
        · simp only [if_pos hj,if_pos (by omega : p < sigma + (j + 1) + 1)]
        · simp only [if_neg hj,if_neg (by omega : ¬p < sigma + (j + 1) + 1)]

private theorem copy_finished (M : MultitapeTM) (base : ℕ → Option M.Sym) (sigma : ℕ)
    (w : List M.Sym) : copyTape M base sigma w w.length = bankTape M base sigma [] := by
  funext p
  by_cases hp : p < sigma
  · simp only [copyTape,bankTape,if_pos hp]
  · by_cases he : p = sigma
    · subst p
      simp [copyTape,bankTape,MultitapeTM.tapeOf]
    · simp only [copyTape,bankTape,if_neg hp,if_neg he]
      have hg : 0 < p - sigma := by omega
      cases hq : p - sigma with
      | zero => omega
      | succ q =>
          simp only [MultitapeTM.tapeOf,List.getD_nil]
          by_cases hw : p < sigma + w.length + 1
          · simp only [if_pos hw]
          · rw [if_neg hw,List.getD_eq_default _ _ (by omega)]

end IntMul.InteriorBankedCall



namespace IntMul.InteriorBankedCall

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

private theorem input_index (M : MultitapeTM) (i : Fin (M.k + 2)) (hi : 2 ≤ i.val) :
    BankedSimulation.innerTape M i hi = M.inTape ↔ i.val = 2 := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    simp only [BankedSimulation.innerTape,MultitapeTM.inTape] at hv
    omega
  · intro h
    apply Fin.ext
    simp only [BankedSimulation.innerTape,MultitapeTM.inTape]
    omega

private theorem ready_work_cells (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (i : Fin (M.k + 2)) (hi : 2 ≤ i.val) :
    (readyFrame M base sigma offset x y).cells i =
      bankTape M (base.cells i) (offset (BankedSimulation.innerTape M i hi))
        (if i.val = 2 then BankedCall.inputWord M x y else []) := by
  funext p
  simp only [readyFrame,runningFrame,BankedSimulation.embed,dif_pos hi,callerBase,
    if_neg (by omega : i.val ≠ 1),MultitapeTM.initCfg,input_index M i hi,bankTape]
  by_cases ht : i.val = 2
  · simp only [if_pos ht,BankedCall.inputWord]
  · simp only [if_neg ht]

private theorem start_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Option M.Sym)
    (blank : ∀ i, 1 ≤ i.val → a i = some M.blank) :
    transition M (.inl .start) a = (.inl .copyInput,fun i =>
      (if 1 ≤ i.val then some M.startSym else a i,if i.val = 1 ∨ i.val = 2 then .right else .stay)) := by
  classical
  simp only [transition,rawTransition]
  congr 1
  funext i
  by_cases hi : 1 ≤ i.val
  · simp only [if_pos hi]
    rw [blank i hi]
    by_cases hm : i.val = 1 ∨ i.val = 2
    · simp only [if_pos hm,BankedSimulation.protect,BankedSimulation.decode]
    · simp only [if_neg hm,BankedSimulation.protect,BankedSimulation.decode]
  · have hm : ¬(i.val = 1 ∨ i.val = 2) := by omega
    simp only [if_neg hi,if_neg hm,protect_stay]

/-- Every interior source and bank marker is created by one actual transition.
The input payload and all saved prefixes are retained at this boundary. -/
private theorem start_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) :
    (machine M).step (inputFrame M base sigma offset x y) = copyFrame M base sigma offset x y 0 := by
  have hb : ∀ i, 1 ≤ i.val → (inputFrame M base sigma offset x y).cells i
      ((inputFrame M base sigma offset x y).head i) = some M.blank := by
    intro i hi
    by_cases hw : 2 ≤ i.val
    · simp only [inputFrame,dif_pos hw,freshTape,if_neg (by omega :
        ¬offset (BankedSimulation.innerTape M i hw) < offset (BankedSimulation.innerTape M i hw))]
    · have he : i.val = 1 := by omega
      simp only [inputFrame,dif_neg hw,if_pos he,sourceTape,if_neg (by omega : ¬sigma < sigma),if_true]
  have ht := start_transition M
    (fun i => (inputFrame M base sigma offset x y).cells i ((inputFrame M base sigma offset x y).head i)) hb
  change transition M (inputFrame M base sigma offset x y).state
    (fun i => (inputFrame M base sigma offset x y).cells i ((inputFrame M base sigma offset x y).head i)) = _ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hw : 2 ≤ i.val
    · have hg : 1 ≤ i.val := by omega
      simp only [inputFrame,copyFrame,dif_pos hw,if_pos hg,List.take_zero,ite_self]
      exact fresh_mark M (base.cells i) (offset (BankedSimulation.innerTape M i hw))
    · by_cases hs : i.val = 1
      · have hg : 1 ≤ i.val := by omega
        simp only [inputFrame,copyFrame,dif_neg hw,if_pos hs,if_pos hg]
        exact source_mark M (base.cells i) sigma (BankedCall.inputWord M x y)
      · have hg : ¬1 ≤ i.val := by omega
        simp only [if_neg hg]
        rw [Function.update_eq_self]
        simp only [inputFrame,copyFrame,dif_neg hw,if_neg hs]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hw : 2 ≤ i.val
    · have hs : i.val ≠ 1 := by omega
      simp only [inputFrame,copyFrame,dif_pos hw]
      by_cases ht : i.val = 2
      · simp only [if_pos ht,if_pos (Or.inr ht)]
      · simp only [if_neg ht,if_neg (by tauto : ¬(i.val = 1 ∨ i.val = 2)),Nat.add_zero]
    · by_cases hs : i.val = 1
      · simp only [inputFrame,copyFrame,dif_neg hw,if_pos hs,if_pos (Or.inl hs)]
      · have ht : i.val ≠ 2 := by omega
        simp only [inputFrame,copyFrame,dif_neg hw,if_neg hs,
          if_neg (by tauto : ¬(i.val = 1 ∨ i.val = 2))]

private theorem word_letter (M : MultitapeTM) (x y : List Bool) (a : M.Sym)
    (ha : a ∈ BankedCall.inputWord M x y) : a = M.zero ∨ a = M.one ∨ a = M.sep := by
  simp only [BankedCall.inputWord,List.mem_append,List.mem_cons,List.mem_map] at ha
  rcases ha with ⟨b,_,rfl⟩ | (ha | ⟨b,_,rfl⟩)
  · cases b <;> simp [MultitapeTM.bitSym]
  · exact Or.inr (Or.inr ha)
  · cases b <;> simp [MultitapeTM.bitSym]

private theorem copy_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Option M.Sym)
    (s : M.Sym) (letter : s = M.zero ∨ s = M.one ∨ s = M.sep)
    (source : a ⟨1,by omega⟩ = some s)
    (target : a ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩ = some M.blank) :
    transition M (.inl .copyInput) a = (.inl .copyInput,fun i =>
      (if i.val = 1 then some M.blank else if i.val = 2 then some s else a i,
        if i.val = 1 ∨ i.val = 2 then .right else .stay)) := by
  classical
  have hb : a ⟨1,by omega⟩ = some M.zero ∨ a ⟨1,by omega⟩ = some M.one ∨
      a ⟨1,by omega⟩ = some M.sep := by
    rw [source]
    rcases letter with h | h | h <;> simp only [h,or_true,true_or]
  simp only [transition,rawTransition,if_pos hb]
  congr 1
  funext i
  by_cases hs : i.val = 1
  · have he : i = ⟨1,by omega⟩ := Fin.ext hs
    simp only [if_pos hs,if_pos (Or.inl hs)]
    rw [he,source]
    rfl
  · simp only [if_neg hs]
    by_cases ht : i.val = 2
    · have he : i = ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩ := Fin.ext ht
      simp only [if_pos ht,if_pos (Or.inr ht)]
      rw [he,target,source]
      rfl
    · simp only [if_neg ht,if_neg (by tauto : ¬(i.val = 1 ∨ i.val = 2)),protect_stay]

/-- A single transition simultaneously copies the scanned input symbol to the
child bank and erases it from the mutable source buffer. -/
private theorem copy_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (j : ℕ)
    (hj : j < (BankedCall.inputWord M x y).length) :
    (machine M).step (copyFrame M base sigma offset x y j) = copyFrame M base sigma offset x y (j + 1) := by
  let w := BankedCall.inputWord M x y
  have hjw : j < w.length := hj
  have hs : (copyFrame M base sigma offset x y j).cells ⟨1,by change 1 < M.k + 2; omega⟩
      ((copyFrame M base sigma offset x y j).head ⟨1,by change 1 < M.k + 2; omega⟩) = some w[j] := by
    change copyTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma w j (sigma + j + 1) = _
    rw [copy_read,List.getD_eq_getElem _ _ hjw]
  have hl : (w.take j).length = j := by simp [Nat.min_eq_left hjw.le]
  have hd : (copyFrame M base sigma offset x y j).cells
      ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩
      ((copyFrame M base sigma offset x y j).head
        ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩) = some M.blank := by
    change bankTape M (base.cells ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩)
      (offset M.inTape) (w.take j) (offset M.inTape + j + 1) = _
    rw [bank_payload,List.getD_eq_default _ _ (by omega)]
  have ht := copy_transition M
    (fun i => (copyFrame M base sigma offset x y j).cells i ((copyFrame M base sigma offset x y j).head i))
      w[j] (word_letter M x y w[j] (List.getElem_mem hj)) hs hd
  change transition M (copyFrame M base sigma offset x y j).state
    (fun i => (copyFrame M base sigma offset x y j).cells i ((copyFrame M base sigma offset x y j).head i)) = _ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hs : i.val = 1
    · have hw : ¬2 ≤ i.val := by omega
      simp only [if_pos hs,copyFrame,dif_neg hw]
      exact copy_erase M (base.cells i) sigma w j
    · simp only [if_neg hs]
      by_cases hd : i.val = 2
      · have hw : 2 ≤ i.val := by omega
        simp only [if_pos hd,copyFrame,dif_pos hw]
        change Function.update
          (bankTape M (base.cells i) (offset (BankedSimulation.innerTape M i hw)) (w.take j))
            (offset (BankedSimulation.innerTape M i hw) + (j + 1)) (some w[j]) =
              bankTape M (base.cells i) (offset (BankedSimulation.innerTape M i hw)) (w.take (j + 1))
        rw [List.take_succ_eq_append_getElem hjw]
        simpa only [hl,Nat.add_assoc] using
          bank_append_one M (base.cells i) (offset (BankedSimulation.innerTape M i hw)) (w.take j) w[j]
      · simp only [if_neg hd]
        rw [Function.update_eq_self]
        by_cases hw : 2 ≤ i.val
        · simp only [copyFrame,dif_pos hw,if_neg hd]
        · simp only [copyFrame,dif_neg hw,if_neg hs]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hw : 2 ≤ i.val
    · have hs : i.val ≠ 1 := by omega
      simp only [copyFrame,dif_pos hw]
      by_cases hd : i.val = 2
      · simp only [if_pos hd,if_pos (Or.inr hd)]
        omega
      · simp only [if_neg hd,if_neg (by tauto : ¬(i.val = 1 ∨ i.val = 2))]
    · by_cases hs : i.val = 1
      · simp only [copyFrame,dif_neg hw,if_pos hs,if_pos (Or.inl hs)]
        omega
      · have hd : i.val ≠ 2 := by omega
        simp only [copyFrame,dif_neg hw,if_neg hs,
          if_neg (by tauto : ¬(i.val = 1 ∨ i.val = 2))]

private theorem copy_run (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (j : ℕ)
    (hj : j ≤ (BankedCall.inputWord M x y).length) :
    (machine M).step^[j] (copyFrame M base sigma offset x y 0) = copyFrame M base sigma offset x y j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),copy_step M base sigma offset x y j (by omega)]

private theorem copy_cells_complete (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) :
    (copyFrame M base sigma offset x y (BankedCall.inputWord M x y).length).cells =
      (readyFrame M base sigma offset x y).cells := by
  funext i
  by_cases hw : 2 ≤ i.val
  · rw [ready_work_cells M base sigma offset x y i hw]
    simp only [copyFrame,dif_pos hw,List.take_length]
  · by_cases hs : i.val = 1
    · simp only [copyFrame,dif_neg hw,if_pos hs,readyFrame,runningFrame,BankedSimulation.embed,
        dif_neg hw,callerBase,if_pos hs]
      exact copy_finished M (base.cells i) sigma (BankedCall.inputWord M x y)
    · simp only [copyFrame,dif_neg hw,if_neg hs,readyFrame,runningFrame,BankedSimulation.embed,
        dif_neg hw,callerBase,if_neg hs]

private theorem copy_end_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Option M.Sym)
    (source : a ⟨1,by omega⟩ = some M.blank)
    (target : a ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩ = some M.blank) :
    transition M (.inl .copyInput) a = (.inl .rewindInput,fun i =>
      (a i,if i.val = 2 then .left else .stay)) := by
  classical
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at hd
  have hb : ¬(a ⟨1,by omega⟩ = some M.zero ∨ a ⟨1,by omega⟩ = some M.one ∨
      a ⟨1,by omega⟩ = some M.sep) := by
    rw [source]
    simp only [Option.some.injEq,not_or]
    aesop
  simp only [transition,rawTransition,if_neg hb]
  congr 1
  funext i
  by_cases ht : i.val = 2
  · have he : i = ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩ := Fin.ext ht
    simp only [if_pos ht]
    rw [he,target]
    rfl
  · simp only [if_neg ht,protect_stay]

private theorem copy_end_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) :
    (machine M).step (copyFrame M base sigma offset x y (BankedCall.inputWord M x y).length) =
      returnInputFrame M base sigma offset x y (BankedCall.inputWord M x y).length := by
  let w := BankedCall.inputWord M x y
  change (machine M).step (copyFrame M base sigma offset x y w.length) = returnInputFrame M base sigma offset x y w.length
  have hs : (copyFrame M base sigma offset x y w.length).cells ⟨1,by change 1 < M.k + 2; omega⟩
      ((copyFrame M base sigma offset x y w.length).head ⟨1,by change 1 < M.k + 2; omega⟩) = some M.blank := by
    change copyTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma w w.length (sigma + w.length + 1) = _
    rw [copy_read,List.getD_eq_default _ _ le_rfl]
  have hd : (copyFrame M base sigma offset x y w.length).cells
      ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩
      ((copyFrame M base sigma offset x y w.length).head
        ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩) = some M.blank := by
    change bankTape M (base.cells ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩)
      (offset M.inTape) (w.take w.length) (offset M.inTape + w.length + 1) = _
    rw [List.take_length,bank_payload,List.getD_eq_default _ _ le_rfl]
  have ht := copy_end_transition M
    (fun i => (copyFrame M base sigma offset x y w.length).cells i ((copyFrame M base sigma offset x y w.length).head i)) hs hd
  change transition M (copyFrame M base sigma offset x y w.length).state
    (fun i => (copyFrame M base sigma offset x y w.length).cells i ((copyFrame M base sigma offset x y w.length).head i)) = _ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    change (copyFrame M base sigma offset x y w.length).cells i = (readyFrame M base sigma offset x y).cells i
    exact congrFun (copy_cells_complete M base sigma offset x y) i
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hw : 2 ≤ i.val
    · simp only [copyFrame,returnInputFrame,dif_pos hw]
      by_cases hd : i.val = 2
      · simp only [if_pos hd]
        omega
      · simp only [if_neg hd,Nat.add_zero]
    · have hd : i.val ≠ 2 := by omega
      simp only [w,copyFrame,returnInputFrame,dif_neg hw,if_neg hd]

private theorem protect_left (M : MultitapeTM) (a : Option M.Sym) (h : a ≠ none) :
    BankedSimulation.protect M a (BankedSimulation.decode M a) .left = (a,.left) := by
  cases a with
  | none => exact False.elim (h rfl)
  | some s => rfl

private theorem word_not_start (M : MultitapeTM) (x y : List Bool) (j : ℕ)
    (hj : j < (BankedCall.inputWord M x y).length) : (BankedCall.inputWord M x y)[j] ≠ M.startSym := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at hd
  have hl := word_letter M x y (BankedCall.inputWord M x y)[j] (List.getElem_mem hj)
  aesop

private theorem return_left_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Option M.Sym)
    (h : a ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩ ≠ some M.startSym)
    (hn : a ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩ ≠ none) :
    transition M (.inl .rewindInput) a = (.inl .rewindInput,fun i =>
      (a i,if i.val = 2 then .left else .stay)) := by
  classical
  simp only [transition,rawTransition,if_neg h]
  congr 1
  funext i
  by_cases hi : i.val = 2
  · simp only [if_pos hi]
    have he : i = ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩ := Fin.ext hi
    rw [he]
    exact protect_left M _ hn
  · simp only [if_neg hi,protect_stay]

private theorem return_left_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (j : ℕ)
    (hj : j < (BankedCall.inputWord M x y).length) :
    (machine M).step (returnInputFrame M base sigma offset x y (j + 1)) =
      returnInputFrame M base sigma offset x y j := by
  let w := BankedCall.inputWord M x y
  have hr : (returnInputFrame M base sigma offset x y (j + 1)).cells
      ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩
      ((returnInputFrame M base sigma offset x y (j + 1)).head
        ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩) = some w[j] := by
    change (readyFrame M base sigma offset x y).cells
      ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩ (offset M.inTape + j + 1) = _
    rw [ready_work_cells M base sigma offset x y _ (by change 2 ≤ (2 : ℕ); omega)]
    change bankTape M (base.cells ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩)
      (offset M.inTape) w (offset M.inTape + j + 1) = _
    rw [bank_payload,List.getD_eq_getElem _ _ hj]
  have hm : (returnInputFrame M base sigma offset x y (j + 1)).cells
      ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩
      ((returnInputFrame M base sigma offset x y (j + 1)).head
        ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩) ≠ some M.startSym := by
    rw [hr]
    exact fun he => word_not_start M x y j hj (Option.some.inj he)
  have hn : (returnInputFrame M base sigma offset x y (j + 1)).cells
      ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩
      ((returnInputFrame M base sigma offset x y (j + 1)).head
        ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩) ≠ none := by
    rw [hr]
    exact Option.some_ne_none _
  have ht := return_left_transition M
    (fun i => (returnInputFrame M base sigma offset x y (j + 1)).cells i
      ((returnInputFrame M base sigma offset x y (j + 1)).head i)) hm hn
  change transition M (returnInputFrame M base sigma offset x y (j + 1)).state
    (fun i => (returnInputFrame M base sigma offset x y (j + 1)).cells i
      ((returnInputFrame M base sigma offset x y (j + 1)).head i)) = _ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hw : 2 ≤ i.val
    · simp only [returnInputFrame,dif_pos hw]
      by_cases hd : i.val = 2
      · simp only [if_pos hd]
        omega
      · simp only [if_neg hd]
    · have hd : i.val ≠ 2 := by omega
      simp only [returnInputFrame,dif_neg hw,if_neg hd]

private theorem return_marker_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Option M.Sym)
    (h : a ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩ = some M.startSym) :
    transition M (.inl .rewindInput) a = (.inr M.qStart,fun i => (a i,.stay)) := by
  classical
  simp [transition,rawTransition,h,protect_stay]

private theorem return_marker_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) :
    (machine M).step (returnInputFrame M base sigma offset x y 0) = readyFrame M base sigma offset x y := by
  have hr : (returnInputFrame M base sigma offset x y 0).cells
      ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩
      ((returnInputFrame M base sigma offset x y 0).head
        ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩) = some M.startSym := by
    change (readyFrame M base sigma offset x y).cells
      ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩ (offset M.inTape) = _
    rw [ready_work_cells M base sigma offset x y _ (by change 2 ≤ (2 : ℕ); omega)]
    exact bank_boundary _ _ _ _
  have ht := return_marker_transition M
    (fun i => (returnInputFrame M base sigma offset x y 0).cells i ((returnInputFrame M base sigma offset x y 0).head i)) hr
  change transition M (returnInputFrame M base sigma offset x y 0).state
    (fun i => (returnInputFrame M base sigma offset x y 0).cells i ((returnInputFrame M base sigma offset x y 0).head i)) = _ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hw : 2 ≤ i.val
    · simp only [returnInputFrame,readyFrame,runningFrame,BankedSimulation.embed,dif_pos hw,
        MultitapeTM.initCfg,ite_self,Nat.add_zero]
    · simp only [returnInputFrame,readyFrame,runningFrame,BankedSimulation.embed,dif_neg hw,callerBase]

private theorem return_run (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (p : ℕ)
    (hp : p ≤ (BankedCall.inputWord M x y).length) :
    (machine M).step^[p + 1] (returnInputFrame M base sigma offset x y p) = readyFrame M base sigma offset x y := by
  induction p with
  | zero => simpa using return_marker_step M base sigma offset x y
  | succ p ih => rw [Function.iterate_succ_apply,return_left_step M base sigma offset x y p (by omega),ih (by omega)]

/-- The local buffer and work markers are created physically; the full input
is copied while erased, then its child head is returned to the local marker.
The table is independent of sigma and all bank offsets. -/
private theorem setup_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) :
    (machine M).step^[2 * (BankedCall.inputWord M x y).length + 3]
      (inputFrame M base sigma offset x y) = readyFrame M base sigma offset x y := by
  let L := (BankedCall.inputWord M x y).length
  have hc : (machine M).step^[L + 2] (inputFrame M base sigma offset x y) = returnInputFrame M base sigma offset x y L := by
    rw [show L + 2 = (L + 1) + 1 by omega,Function.iterate_succ_apply',Function.iterate_add_apply,
      Function.iterate_one,start_step,copy_run M base sigma offset x y L le_rfl,copy_end_step]
  rw [show 2 * (BankedCall.inputWord M x y).length + 3 = (L + 1) + (L + 2) by unfold L; omega,
    Function.iterate_add_apply,hc,return_run M base sigma offset x y L le_rfl]

end IntMul.InteriorBankedCall


open IntMul IntMul.InteriorBankedCall

theorem solution (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) :
    (machine M).step^[2 * (BankedCall.inputWord M x y).length + 3]
      (inputFrame M base sigma offset x y) = readyFrame M base sigma offset x y :=
  IntMul.InteriorBankedCall.setup_correct M base sigma offset x y

#print axioms solution
