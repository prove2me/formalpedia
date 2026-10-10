-- Prove2me | solution 1 for IntMul.TrackedBankPreparation.setup_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T22:47:00.067746+00:00
-- url     : https://prove2.me/submissions/a5609a01-c6fc-4c83-bb72-7fde61babcab

import Definitions.Def_IntMul_TrackedBankPreparation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic


namespace IntMul.TrackedBankPreparation

open IntMul.TrackedBankedSimulation (Sym)

private theorem bank_boundary (M : MultitapeTM) (base : ℕ → Sym M) (offset : ℕ) (w : List M.Sym) :
    bankTape M base offset w offset = some (M.startSym,true) := by
  simp [bankTape,MultitapeTM.tapeOf]

private theorem bank_payload (M : MultitapeTM) (base : ℕ → Sym M) (offset : ℕ)
    (w : List M.Sym) (p : ℕ) :
    bankTape M base offset w (offset + p + 1) = some (w.getD p M.blank,decide (p < w.length)) := by
  simp only [bankTape,if_neg (by omega : ¬offset + p + 1 < offset),
    show offset + p + 1 - offset = p + 1 by omega,MultitapeTM.tapeOf]
  simp only [show p + 1 ≤ w.length ↔ p < w.length by omega]

private theorem bank_append (M : MultitapeTM) (base : ℕ → Sym M) (offset : ℕ)
    (w : List M.Sym) (a : M.Sym) :
    Function.update (bankTape M base offset w) (offset + w.length + 1) (some (a,true)) =
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
      by_cases hs : p = offset
      · subst p
        rw [bank_boundary,bank_boundary]
      · have hn : p = offset + (p - offset - 1) + 1 := by omega
        rw [hn,bank_payload,bank_payload]
        have hq : p - offset - 1 ≠ w.length := by omega
        simp only [List.length_append,List.length_singleton]
        by_cases hl : p - offset - 1 < w.length
        · rw [List.getD_append _ _ _ _ hl]
          simp only [hl,show p - offset - 1 < w.length + 1 by omega,decide_true]
        · have hb : w.length ≤ p - offset - 1 := by omega
          rw [List.getD_eq_default _ _ hb,List.getD_append_right _ _ _ _ hb,
            List.getD_eq_default _ _ (by simp; omega)]
          simp only [hl,show ¬p - offset - 1 < w.length + 1 by omega,decide_false]

private theorem fresh_mark (M : MultitapeTM) (base : ℕ → Sym M) (offset : ℕ) :
    Function.update (freshTape M base offset) offset (some (M.startSym,true)) = bankTape M base offset [] := by
  classical
  funext p
  by_cases he : p = offset
  · subst p
    rw [Function.update_self,bank_boundary]
  · rw [Function.update_of_ne he]
    by_cases hp : p < offset
    · simp only [freshTape,bankTape,if_pos hp]
    · simp only [freshTape,bankTape,if_neg hp]
      have hz : p - offset ≠ 0 := by omega
      cases hq : p - offset with
      | zero => omega
      | succ q => simp [MultitapeTM.tapeOf]

private theorem source_mark (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List M.Sym) :
    Function.update (sourceTape M base sigma w) sigma (some (M.startSym,true)) = copyTape M base sigma w 0 := by
  classical
  funext p
  by_cases he : p = sigma
  · subst p
    simp [copyTape]
  · rw [Function.update_of_ne he]
    by_cases hp : p < sigma
    · simp only [sourceTape,copyTape,if_pos hp]
    · simp only [sourceTape,copyTape,if_neg hp,if_neg he,
        if_neg (by omega : ¬p < sigma + 0 + 1)]

private theorem copy_read (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ)
    (w : List M.Sym) (j : ℕ) :
    copyTape M base sigma w j (sigma + j + 1) = some (w.getD j M.blank,decide (j < w.length)) := by
  simp only [copyTape,if_neg (by omega : ¬sigma + j + 1 < sigma),
    if_neg (by omega : sigma + j + 1 ≠ sigma),if_neg (by omega : ¬sigma + j + 1 < sigma + j + 1),
    show sigma + j + 1 - sigma - 1 = j by omega]

private theorem copy_erase (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ)
    (w : List M.Sym) (j : ℕ) :
    Function.update (copyTape M base sigma w j) (sigma + j + 1) (some (M.blank,false)) =
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
        have hc : p < sigma + (j + 1) + 1 ↔ p < sigma + j + 1 := by omega
        simp only [hc]

private theorem copy_finished (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ)
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
            simp
          · have hl : w.length ≤ p - sigma - 1 := by omega
            have hqge : w.length ≤ q := by omega
            simp only [Nat.add_sub_cancel] at *
            rw [if_neg hw,List.getD_eq_default _ _ hqge]
            simp [show ¬q < w.length by omega]

end IntMul.TrackedBankPreparation



namespace IntMul.TrackedBankPreparation

open IntMul.TrackedBankedSimulation (Sym)

private theorem copy_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem copy_protect_right (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .right = (a,.right) := by
  cases a <;> rfl

private theorem copy_protect_stay (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .stay = (a,.stay) := by
  cases a <;> rfl

private theorem copy_input_index (M : MultitapeTM) (i : Fin (M.k + 2)) (hi : 2 ≤ i.val) :
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
        (if i.val = 2 then inputWord M x y else []) := by
  funext p
  simp only [readyFrame,TrackedBankedSimulation.embed,dif_pos hi,callerBase,
    if_neg (by omega : i.val ≠ 1),MultitapeTM.initCfg,copy_input_index M i hi,initialExtent,copy_input_index M i hi,bankTape]
  by_cases ht : i.val = 2
  · simp only [if_pos ht,inputWord]
  · simp only [if_neg ht,List.length_nil]

private theorem copy_start_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Sym M)
    (blank : ∀ i, 1 ≤ i.val → a i = some (M.blank,false)) :
    transition M (.mark) a = (.copy,fun i =>
      (if 1 ≤ i.val then some (M.startSym,true) else a i,if i.val = 1 ∨ i.val = 2 then .right else .stay)) := by
  classical
  simp only [transition,rawTransition]
  congr 1
  funext i
  by_cases hi : 1 ≤ i.val
  · simp only [if_pos hi]
    rw [blank i hi]
    by_cases hm : i.val = 1 ∨ i.val = 2
    · simp only [if_pos hm,TrackedBankCleanup.protect,TrackedBankedSimulation.decode]
    · simp only [if_neg hm,TrackedBankCleanup.protect,TrackedBankedSimulation.decode]
  · have hm : ¬(i.val = 1 ∨ i.val = 2) := by omega
    simp only [if_neg hi,if_neg hm,copy_protect_stay]

/-- Every interior source and bank marker is created by one actual transition.
The input payload and all saved prefixes are retained at this boundary. -/
private theorem start_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) :
    (machine M).step (initialFrame M base sigma offset x y) = copyFrame M base sigma offset x y 0 := by
  have hb : ∀ i, 1 ≤ i.val → (initialFrame M base sigma offset x y).cells i
      ((initialFrame M base sigma offset x y).head i) = some (M.blank,false) := by
    intro i hi
    by_cases hw : 2 ≤ i.val
    · simp only [initialFrame,dif_pos hw,freshTape,if_neg (by omega :
        ¬offset (BankedSimulation.innerTape M i hw) < offset (BankedSimulation.innerTape M i hw))]
    · have he : i.val = 1 := by omega
      simp only [initialFrame,dif_neg hw,if_pos he,sourceTape,if_neg (by omega : ¬sigma < sigma),if_true]
  have ht := copy_start_transition M
    (fun i => (initialFrame M base sigma offset x y).cells i ((initialFrame M base sigma offset x y).head i)) hb
  change transition M (initialFrame M base sigma offset x y).state
    (fun i => (initialFrame M base sigma offset x y).cells i ((initialFrame M base sigma offset x y).head i)) = _ at ht
  apply copy_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hw : 2 ≤ i.val
    · have hg : 1 ≤ i.val := by omega
      simp only [initialFrame,copyFrame,dif_pos hw,if_pos hg,List.take_zero,ite_self]
      exact fresh_mark M (base.cells i) (offset (BankedSimulation.innerTape M i hw))
    · by_cases hs : i.val = 1
      · have hg : 1 ≤ i.val := by omega
        simp only [initialFrame,copyFrame,dif_neg hw,if_pos hs,if_pos hg]
        exact source_mark M (base.cells i) sigma (inputWord M x y)
      · have hg : ¬1 ≤ i.val := by omega
        simp only [if_neg hg]
        rw [Function.update_eq_self]
        simp only [initialFrame,copyFrame,dif_neg hw,if_neg hs]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hw : 2 ≤ i.val
    · have hs : i.val ≠ 1 := by omega
      simp only [initialFrame,copyFrame,dif_pos hw]
      by_cases ht : i.val = 2
      · simp only [if_pos ht,if_pos (Or.inr ht)]
      · simp only [if_neg ht,if_neg (by tauto : ¬(i.val = 1 ∨ i.val = 2)),Nat.add_zero]
    · by_cases hs : i.val = 1
      · simp only [initialFrame,copyFrame,dif_neg hw,if_pos hs,if_pos (Or.inl hs)]
      · have ht : i.val ≠ 2 := by omega
        simp only [initialFrame,copyFrame,dif_neg hw,if_neg hs,
          if_neg (by tauto : ¬(i.val = 1 ∨ i.val = 2))]

private theorem copy_word_letter (M : MultitapeTM) (x y : List Bool) (a : M.Sym)
    (ha : a ∈ inputWord M x y) : a = M.zero ∨ a = M.one ∨ a = M.sep := by
  simp only [inputWord,List.mem_append,List.mem_cons,List.mem_map] at ha
  rcases ha with ⟨b,_,rfl⟩ | (ha | ⟨b,_,rfl⟩)
  · cases b <;> simp [MultitapeTM.bitSym]
  · exact Or.inr (Or.inr ha)
  · cases b <;> simp [MultitapeTM.bitSym]

private theorem copy_copy_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Sym M)
    (s : M.Sym) (letter : s = M.zero ∨ s = M.one ∨ s = M.sep)
    (source : a ⟨1,by omega⟩ = some (s,true))
    (target : a ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩ = some (M.blank,false)) :
    transition M (.copy) a = (.copy,fun i =>
      (if i.val = 1 then some (M.blank,false) else if i.val = 2 then some (s,true) else a i,
        if i.val = 1 ∨ i.val = 2 then .right else .stay)) := by
  classical
  have hb : TrackedBankedSimulation.decode M (a ⟨1,by omega⟩) = M.zero ∨
      TrackedBankedSimulation.decode M (a ⟨1,by omega⟩) = M.one ∨
      TrackedBankedSimulation.decode M (a ⟨1,by omega⟩) = M.sep := by
    rw [source]
    simp only [TrackedBankedSimulation.decode]
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
    · simp only [if_neg ht,if_neg (by tauto : ¬(i.val = 1 ∨ i.val = 2)),copy_protect_stay]

/-- A single transition simultaneously copies the scanned input symbol to the
child bank and erases it from the mutable source buffer. -/
private theorem copy_copy_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (j : ℕ)
    (hj : j < (inputWord M x y).length) :
    (machine M).step (copyFrame M base sigma offset x y j) = copyFrame M base sigma offset x y (j + 1) := by
  let w := inputWord M x y
  have hjw : j < w.length := hj
  have hs : (copyFrame M base sigma offset x y j).cells ⟨1,by change 1 < M.k + 2; omega⟩
      ((copyFrame M base sigma offset x y j).head ⟨1,by change 1 < M.k + 2; omega⟩) = some (w[j],true) := by
    change copyTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma w j (sigma + j + 1) = _
    rw [copy_read,List.getD_eq_getElem _ _ hjw]
    simp only [hjw,decide_true]
  have hl : (w.take j).length = j := by simp [Nat.min_eq_left hjw.le]
  have hd : (copyFrame M base sigma offset x y j).cells
      ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩
      ((copyFrame M base sigma offset x y j).head
        ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩) = some (M.blank,false) := by
    change bankTape M (base.cells ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩)
      (offset M.inTape) (w.take j) (offset M.inTape + j + 1) = _
    rw [bank_payload,List.getD_eq_default _ _ (by omega)]
    simp [hl]
  have ht := copy_copy_transition M
    (fun i => (copyFrame M base sigma offset x y j).cells i ((copyFrame M base sigma offset x y j).head i))
      w[j] (copy_word_letter M x y w[j] (List.getElem_mem hj)) hs hd
  change transition M (copyFrame M base sigma offset x y j).state
    (fun i => (copyFrame M base sigma offset x y j).cells i ((copyFrame M base sigma offset x y j).head i)) = _ at ht
  apply copy_cfg_ext
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
            (offset (BankedSimulation.innerTape M i hw) + (j + 1)) (some (w[j],true)) =
              bankTape M (base.cells i) (offset (BankedSimulation.innerTape M i hw)) (w.take (j + 1))
        rw [List.take_succ_eq_append_getElem hjw]
        simpa only [hl,Nat.add_assoc] using
          bank_append M (base.cells i) (offset (BankedSimulation.innerTape M i hw)) (w.take j) w[j]
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
    (hj : j ≤ (inputWord M x y).length) :
    (machine M).step^[j] (copyFrame M base sigma offset x y 0) = copyFrame M base sigma offset x y j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),copy_copy_step M base sigma offset x y j (by omega)]

private theorem copy_cells_complete (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) :
    (copyFrame M base sigma offset x y (inputWord M x y).length).cells =
      (readyFrame M base sigma offset x y).cells := by
  funext i
  by_cases hw : 2 ≤ i.val
  · rw [ready_work_cells M base sigma offset x y i hw]
    simp only [copyFrame,dif_pos hw,List.take_length]
  · by_cases hs : i.val = 1
    · simp only [copyFrame,dif_neg hw,if_pos hs,readyFrame,TrackedBankedSimulation.embed,
        dif_neg hw,callerBase,if_pos hs]
      exact copy_finished M (base.cells i) sigma (inputWord M x y)
    · simp only [copyFrame,dif_neg hw,if_neg hs,readyFrame,TrackedBankedSimulation.embed,
        dif_neg hw,callerBase,if_neg hs]


end IntMul.TrackedBankPreparation



namespace IntMul.TrackedBankPreparation

open IntMul.TrackedBankedSimulation (Sym)

private theorem rewind_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem rewind_protect_right (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .right = (a,.right) := by
  cases a <;> rfl

private theorem rewind_protect_stay (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .stay = (a,.stay) := by
  cases a <;> rfl

private theorem rewind_rewind_word_letter (M : MultitapeTM) (x y : List Bool) (a : M.Sym)
    (ha : a ∈ inputWord M x y) : a = M.zero ∨ a = M.one ∨ a = M.sep := by
  simp only [inputWord,List.mem_append,List.mem_cons,List.mem_map] at ha
  rcases ha with ⟨b,_,rfl⟩ | (ha | ⟨b,_,rfl⟩)
  · cases b <;> simp [MultitapeTM.bitSym]
  · exact Or.inr (Or.inr ha)
  · cases b <;> simp [MultitapeTM.bitSym]

private theorem rewind_copy_end_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Sym M)
    (source : a ⟨1,by omega⟩ = some (M.blank,false))
    (target : a ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩ = some (M.blank,false)) :
    transition M (.copy) a = (.rewind,fun i =>
      (a i,if i.val = 2 then .left else .stay)) := by
  classical
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at hd
  have hb : ¬(TrackedBankedSimulation.decode M (a ⟨1,by omega⟩) = M.zero ∨
      TrackedBankedSimulation.decode M (a ⟨1,by omega⟩) = M.one ∨
      TrackedBankedSimulation.decode M (a ⟨1,by omega⟩) = M.sep) := by
    rw [source]
    simp only [TrackedBankedSimulation.decode]
    aesop
  simp only [transition,rawTransition,if_neg hb]
  congr 1
  funext i
  by_cases ht : i.val = 2
  · have he : i = ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩ := Fin.ext ht
    simp only [if_pos ht]
    rw [he,target]
    rfl
  · simp only [if_neg ht,rewind_protect_stay]

private theorem rewind_copy_end_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) :
    (machine M).step (copyFrame M base sigma offset x y (inputWord M x y).length) =
      rewindFrame M base sigma offset x y (inputWord M x y).length := by
  let w := inputWord M x y
  change (machine M).step (copyFrame M base sigma offset x y w.length) = rewindFrame M base sigma offset x y w.length
  have hs : (copyFrame M base sigma offset x y w.length).cells ⟨1,by change 1 < M.k + 2; omega⟩
      ((copyFrame M base sigma offset x y w.length).head ⟨1,by change 1 < M.k + 2; omega⟩) = some (M.blank,false) := by
    change copyTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma w w.length (sigma + w.length + 1) = _
    rw [copy_read,List.getD_eq_default _ _ le_rfl]
    simp
  have hd : (copyFrame M base sigma offset x y w.length).cells
      ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩
      ((copyFrame M base sigma offset x y w.length).head
        ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩) = some (M.blank,false) := by
    change bankTape M (base.cells ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩)
      (offset M.inTape) (w.take w.length) (offset M.inTape + w.length + 1) = _
    rw [List.take_length,bank_payload,List.getD_eq_default _ _ le_rfl]
    simp
  have ht := rewind_copy_end_transition M
    (fun i => (copyFrame M base sigma offset x y w.length).cells i ((copyFrame M base sigma offset x y w.length).head i)) hs hd
  change transition M (copyFrame M base sigma offset x y w.length).state
    (fun i => (copyFrame M base sigma offset x y w.length).cells i ((copyFrame M base sigma offset x y w.length).head i)) = _ at ht
  apply rewind_cfg_ext
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
    · simp only [copyFrame,rewindFrame,dif_pos hw]
      by_cases hd : i.val = 2
      · simp only [if_pos hd]
        omega
      · simp only [if_neg hd,Nat.add_zero]
    · have hd : i.val ≠ 2 := by omega
      simp only [w,copyFrame,rewindFrame,dif_neg hw,if_neg hd]

private theorem rewind_protect_left (M : MultitapeTM) (a : Sym M) (h : a ≠ none) :
    TrackedBankCleanup.protect M a a .left = (a,.left) := by
  cases a with
  | none => exact False.elim (h rfl)
  | some s => rfl

private theorem rewind_word_not_start (M : MultitapeTM) (x y : List Bool) (j : ℕ)
    (hj : j < (inputWord M x y).length) : (inputWord M x y)[j] ≠ M.startSym := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at hd
  have hl := rewind_rewind_word_letter M x y (inputWord M x y)[j] (List.getElem_mem hj)
  aesop

private theorem rewind_return_left_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Sym M)
    (h : a ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩ ≠ some (M.startSym,true))
    (hn : a ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩ ≠ none) :
    transition M (.rewind) a = (.rewind,fun i =>
      (a i,if i.val = 2 then .left else .stay)) := by
  classical
  simp only [transition,rawTransition,if_neg h]
  congr 1
  funext i
  by_cases hi : i.val = 2
  · simp only [if_pos hi]
    have he : i = ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩ := Fin.ext hi
    rw [he]
    exact rewind_protect_left M _ hn
  · simp only [if_neg hi,rewind_protect_stay]

private theorem rewind_return_left_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (j : ℕ)
    (hj : j < (inputWord M x y).length) :
    (machine M).step (rewindFrame M base sigma offset x y (j + 1)) =
      rewindFrame M base sigma offset x y j := by
  let w := inputWord M x y
  have hr : (rewindFrame M base sigma offset x y (j + 1)).cells
      ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩
      ((rewindFrame M base sigma offset x y (j + 1)).head
        ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩) = some (w[j],true) := by
    change (readyFrame M base sigma offset x y).cells
      ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩ (offset M.inTape + j + 1) = _
    rw [ready_work_cells M base sigma offset x y _ (by change 2 ≤ (2 : ℕ); omega)]
    change bankTape M (base.cells ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩)
      (offset M.inTape) w (offset M.inTape + j + 1) = _
    rw [bank_payload,List.getD_eq_getElem _ _ hj]
    simp only [w,hj,decide_true]
  have hm : (rewindFrame M base sigma offset x y (j + 1)).cells
      ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩
      ((rewindFrame M base sigma offset x y (j + 1)).head
        ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩) ≠ some (M.startSym,true) := by
    rw [hr]
    exact fun he => rewind_word_not_start M x y j hj (congrArg Prod.fst (Option.some.inj he))
  have hn : (rewindFrame M base sigma offset x y (j + 1)).cells
      ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩
      ((rewindFrame M base sigma offset x y (j + 1)).head
        ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩) ≠ none := by
    rw [hr]
    exact Option.some_ne_none _
  have ht := rewind_return_left_transition M
    (fun i => (rewindFrame M base sigma offset x y (j + 1)).cells i
      ((rewindFrame M base sigma offset x y (j + 1)).head i)) hm hn
  change transition M (rewindFrame M base sigma offset x y (j + 1)).state
    (fun i => (rewindFrame M base sigma offset x y (j + 1)).cells i
      ((rewindFrame M base sigma offset x y (j + 1)).head i)) = _ at ht
  apply rewind_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hw : 2 ≤ i.val
    · simp only [rewindFrame,dif_pos hw]
      by_cases hd : i.val = 2
      · simp only [if_pos hd]
        omega
      · simp only [if_neg hd]
    · have hd : i.val ≠ 2 := by omega
      simp only [rewindFrame,dif_neg hw,if_neg hd]

private theorem rewind_return_marker_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Sym M)
    (h : a ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩ = some (M.startSym,true)) :
    transition M (.rewind) a = (.halt,fun i => (a i,.stay)) := by
  classical
  simp [transition,rawTransition,h,rewind_protect_stay]

private theorem rewind_return_marker_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) :
    (machine M).step (rewindFrame M base sigma offset x y 0) = readyFrame M base sigma offset x y := by
  have hr : (rewindFrame M base sigma offset x y 0).cells
      ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩
      ((rewindFrame M base sigma offset x y 0).head
        ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩) = some (M.startSym,true) := by
    change (readyFrame M base sigma offset x y).cells
      ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩ (offset M.inTape) = _
    rw [ready_work_cells M base sigma offset x y _ (by change 2 ≤ (2 : ℕ); omega)]
    exact bank_boundary _ _ _ _
  have ht := rewind_return_marker_transition M
    (fun i => (rewindFrame M base sigma offset x y 0).cells i ((rewindFrame M base sigma offset x y 0).head i)) hr
  change transition M (rewindFrame M base sigma offset x y 0).state
    (fun i => (rewindFrame M base sigma offset x y 0).cells i ((rewindFrame M base sigma offset x y 0).head i)) = _ at ht
  apply rewind_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hw : 2 ≤ i.val
    · simp only [rewindFrame,readyFrame,TrackedBankedSimulation.embed,dif_pos hw,
        MultitapeTM.initCfg,ite_self,Nat.add_zero]
    · simp only [rewindFrame,readyFrame,TrackedBankedSimulation.embed,dif_neg hw,callerBase]

private theorem rewind_return_run (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (p : ℕ)
    (hp : p ≤ (inputWord M x y).length) :
    (machine M).step^[p + 1] (rewindFrame M base sigma offset x y p) = readyFrame M base sigma offset x y := by
  induction p with
  | zero => simpa using rewind_return_marker_step M base sigma offset x y
  | succ p ih => rw [Function.iterate_succ_apply,rewind_return_left_step M base sigma offset x y p (by omega),ih (by omega)]

/-- The local buffer and work markers are created physically; the full input
is copied while erased, then its child head is returned to the local marker.
The table is independent of sigma and all bank offsets. -/
private theorem setup_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) :
    (machine M).step^[2 * (inputWord M x y).length + 3]
      (initialFrame M base sigma offset x y) = readyFrame M base sigma offset x y := by
  let L := (inputWord M x y).length
  have hc : (machine M).step^[L + 2] (initialFrame M base sigma offset x y) = rewindFrame M base sigma offset x y L := by
    rw [show L + 2 = (L + 1) + 1 by omega,Function.iterate_succ_apply',Function.iterate_add_apply,
      Function.iterate_one,start_step,copy_run M base sigma offset x y L le_rfl,rewind_copy_end_step]
  rw [show 2 * (inputWord M x y).length + 3 = (L + 1) + (L + 2) by unfold L; omega,
    Function.iterate_add_apply,hc,rewind_return_run M base sigma offset x y L le_rfl]

end IntMul.TrackedBankPreparation



namespace IntMul.TrackedBankPreparation

open IntMul.TrackedBankedSimulation (extents nextExtent)

private theorem invariant_word_letter (M : MultitapeTM) (x y : List Bool) (a : M.Sym)
    (ha : a ∈ inputWord M x y) : a = M.zero ∨ a = M.one ∨ a = M.sep := by
  simp only [inputWord,List.mem_append,List.mem_cons,List.mem_map] at ha
  rcases ha with ⟨b,_,rfl⟩ | (ha | ⟨b,_,rfl⟩)
  · cases b <;> simp [MultitapeTM.bitSym]
  · exact Or.inr (Or.inr ha)
  · cases b <;> simp [MultitapeTM.bitSym]

private theorem invariant_word_payload_ne_start (M : MultitapeTM) (x y : List Bool) (p : ℕ) :
    (inputWord M x y).getD p M.blank ≠ M.startSym := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at hd
  by_cases hp : p < (inputWord M x y).length
  · rw [List.getD_eq_getElem _ _ hp]
    have hl := invariant_word_letter M x y (inputWord M x y)[p] (List.getElem_mem hp)
    aesop
  · rw [List.getD_eq_default _ _ (by omega)]
    aesop

private theorem initial_unique_markers (M : MultitapeTM) (x y : List Bool) :
    ∀ j p, (M.initCfg x y).cells j p = M.startSym ↔ p = 0 := by
  intro j p
  cases p with
  | zero =>
      simp only [MultitapeTM.initCfg]
      split <;> simp [MultitapeTM.tapeOf]
  | succ p =>
      simp only [MultitapeTM.initCfg]
      by_cases hj : j = M.inTape
      · simp only [if_pos hj]
        change (inputWord M x y).getD p M.blank = M.startSym ↔ p + 1 = 0
        have h := invariant_word_payload_ne_start M x y p
        simp only [h,Nat.succ_ne_zero]
      · simp only [if_neg hj,MultitapeTM.tapeOf,List.getD_nil]
        have hd := M.syms_distinct
        simp only [List.nodup_cons,List.mem_cons,not_or] at hd
        aesop

private theorem initial_blank_tails (M : MultitapeTM) (x y : List Bool) :
    ∀ j p, initialExtent M x y j < p → (M.initCfg x y).cells j p = M.blank := by
  intro j p hp
  by_cases hj : j = M.inTape
  · simp only [initialExtent,if_pos hj] at hp
    simp only [MultitapeTM.initCfg,if_pos hj]
    cases p with
    | zero => omega
    | succ p =>
        change (inputWord M x y).getD p M.blank = _
        exact List.getD_eq_default _ _ (by omega)
  · simp only [initialExtent,if_neg hj] at hp
    simp only [MultitapeTM.initCfg,if_neg hj]
    cases p with
    | zero => omega
    | succ p => rfl

private theorem initial_heads_near (M : MultitapeTM) (x y : List Bool) :
    ∀ j, (M.initCfg x y).head j ≤ initialExtent M x y j + 1 := by
  intro j
  simp [MultitapeTM.initCfg]

/-- All tracked extents retain the initial physically prepared prefix. -/
private theorem initial_extent_le_run (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ) (T : ℕ) :
    ∀ j, extent j ≤ extents M c extent T j := by
  classical
  induction T with
  | zero => intro j; rfl
  | succ T ih =>
      intro j
      change extent j ≤ nextExtent M (M.step^[T] c) (extents M c extent T) j
      by_cases hh : (M.step^[T] c).state = M.qHalt
      · simpa only [nextExtent,if_pos hh] using ih j
      · simp only [nextExtent,if_neg hh]
        exact (ih j).trans (Nat.le_max_left _ _)

/-- The buffer head left by actual preparation is automatically within the
final workspace bound needed by the complete prepared return-call theorem. -/
private theorem prepared_buffer_near (M : MultitapeTM) (x y : List Bool) (T : ℕ) :
    (inputWord M x y).length + 1 ≤
      TrackedBankCleanup.span M (extents M (M.initCfg x y) (initialExtent M x y) T) + 1 := by
  have hi := initial_extent_le_run M (M.initCfg x y) (initialExtent M x y) T M.inTape
  simp only [initialExtent,if_true] at hi
  have hs : extents M (M.initCfg x y) (initialExtent M x y) T M.inTape ≤
      TrackedBankCleanup.span M (extents M (M.initCfg x y) (initialExtent M x y) T) :=
    Finset.le_sup (Finset.mem_univ M.inTape)
  omega

end IntMul.TrackedBankPreparation


open IntMul IntMul.TrackedBankPreparation

theorem solution (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) :
    (machine M).step^[2 * (inputWord M x y).length + 3]
      (initialFrame M base sigma offset x y) = readyFrame M base sigma offset x y :=
  IntMul.TrackedBankPreparation.setup_correct M base sigma offset x y

#print axioms solution
