-- Prove2me | solution 1 for IntMul.EndParkRecursiveCall.call_entry_protected_prefix
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T07:21:14.368319+00:00
-- url     : https://prove2.me/submissions/61c4db0a-7e27-4cbf-9248-c7e1d78d6293

import Definitions.Def_IntMul_EndParkRecursiveExecution
import Theorems.Thm_IntMul_TrackedBankedSimulation_simulate_run
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Theorems.Thm_IntMul_TrackedChildInputBridge_input_correct
import Theorems.Thm_IntMul_TrackedChildInputBridge_input_window_safe
import Theorems.Thm_IntMul_TrackedBankReservation_reserve_correct
import Theorems.Thm_IntMul_TrackedBankPreparation_setup_correct
import Mathlib.Data.List.GetD
import Mathlib.Tactic



namespace IntMul.TrackedBankPreparation

open IntMul.TrackedBankedSimulation (Sym)

private theorem owned_intmultrackedbankpreparationwindow_bank_boundary (M : MultitapeTM) (base : ℕ → Sym M) (offset : ℕ) (w : List M.Sym) :
    bankTape M base offset w offset = some (M.startSym,true) := by
  simp [bankTape,MultitapeTM.tapeOf]

private theorem owned_intmultrackedbankpreparationwindow_bank_payload (M : MultitapeTM) (base : ℕ → Sym M) (offset : ℕ)
    (w : List M.Sym) (p : ℕ) :
    bankTape M base offset w (offset + p + 1) = some (w.getD p M.blank,decide (p < w.length)) := by
  simp only [bankTape,if_neg (by omega : ¬offset + p + 1 < offset),
    show offset + p + 1 - offset = p + 1 by omega,MultitapeTM.tapeOf]
  simp only [show p + 1 ≤ w.length ↔ p < w.length by omega]

private theorem owned_intmultrackedbankpreparationwindow_bank_append (M : MultitapeTM) (base : ℕ → Sym M) (offset : ℕ)
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
      rw [Function.update_self,owned_intmultrackedbankpreparationwindow_bank_payload]
      simp
    · rw [Function.update_of_ne he]
      by_cases hs : p = offset
      · subst p
        rw [owned_intmultrackedbankpreparationwindow_bank_boundary,owned_intmultrackedbankpreparationwindow_bank_boundary]
      · have hn : p = offset + (p - offset - 1) + 1 := by omega
        rw [hn,owned_intmultrackedbankpreparationwindow_bank_payload,owned_intmultrackedbankpreparationwindow_bank_payload]
        have hq : p - offset - 1 ≠ w.length := by omega
        simp only [List.length_append,List.length_singleton]
        by_cases hl : p - offset - 1 < w.length
        · rw [List.getD_append _ _ _ _ hl]
          simp only [hl,show p - offset - 1 < w.length + 1 by omega,decide_true]
        · have hb : w.length ≤ p - offset - 1 := by omega
          rw [List.getD_eq_default _ _ hb,List.getD_append_right _ _ _ _ hb,
            List.getD_eq_default _ _ (by simp; omega)]
          simp only [hl,show ¬p - offset - 1 < w.length + 1 by omega,decide_false]

private theorem owned_intmultrackedbankpreparationwindow_fresh_mark (M : MultitapeTM) (base : ℕ → Sym M) (offset : ℕ) :
    Function.update (freshTape M base offset) offset (some (M.startSym,true)) = bankTape M base offset [] := by
  classical
  funext p
  by_cases he : p = offset
  · subst p
    rw [Function.update_self,owned_intmultrackedbankpreparationwindow_bank_boundary]
  · rw [Function.update_of_ne he]
    by_cases hp : p < offset
    · simp only [freshTape,bankTape,if_pos hp]
    · simp only [freshTape,bankTape,if_neg hp]
      have hz : p - offset ≠ 0 := by omega
      cases hq : p - offset with
      | zero => omega
      | succ q => simp [MultitapeTM.tapeOf]

private theorem owned_intmultrackedbankpreparationwindow_source_mark (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List M.Sym) :
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

private theorem owned_intmultrackedbankpreparationwindow_copy_read (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ)
    (w : List M.Sym) (j : ℕ) :
    copyTape M base sigma w j (sigma + j + 1) = some (w.getD j M.blank,decide (j < w.length)) := by
  simp only [copyTape,if_neg (by omega : ¬sigma + j + 1 < sigma),
    if_neg (by omega : sigma + j + 1 ≠ sigma),if_neg (by omega : ¬sigma + j + 1 < sigma + j + 1),
    show sigma + j + 1 - sigma - 1 = j by omega]

private theorem owned_intmultrackedbankpreparationwindow_copy_erase (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ)
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

private theorem owned_intmultrackedbankpreparationwindow_copy_finished (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ)
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

private theorem owned_intmultrackedbankpreparationwindow_prep_copy_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem owned_intmultrackedbankpreparationwindow_prep_copy_protect_right (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .right = (a,.right) := by
  cases a <;> rfl

private theorem owned_intmultrackedbankpreparationwindow_prep_copy_protect_stay (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .stay = (a,.stay) := by
  cases a <;> rfl

private theorem owned_intmultrackedbankpreparationwindow_prep_copy_input_index (M : MultitapeTM) (i : Fin (M.k + 2)) (hi : 2 ≤ i.val) :
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

private theorem owned_intmultrackedbankpreparationwindow_ready_work_cells (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (i : Fin (M.k + 2)) (hi : 2 ≤ i.val) :
    (readyFrame M base sigma offset x y).cells i =
      bankTape M (base.cells i) (offset (BankedSimulation.innerTape M i hi))
        (if i.val = 2 then inputWord M x y else []) := by
  funext p
  simp only [readyFrame,TrackedBankedSimulation.embed,dif_pos hi,callerBase,
    if_neg (by omega : i.val ≠ 1),MultitapeTM.initCfg,owned_intmultrackedbankpreparationwindow_prep_copy_input_index M i hi,initialExtent,owned_intmultrackedbankpreparationwindow_prep_copy_input_index M i hi,bankTape]
  by_cases ht : i.val = 2
  · simp only [if_pos ht,inputWord]
  · simp only [if_neg ht,List.length_nil]

private theorem owned_intmultrackedbankpreparationwindow_prep_copy_start_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Sym M)
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
    simp only [if_neg hi,if_neg hm,owned_intmultrackedbankpreparationwindow_prep_copy_protect_stay]

/-- Every interior source and bank marker is created by one actual transition.
The input payload and all saved prefixes are retained at this boundary. -/
private theorem owned_intmultrackedbankpreparationwindow_start_step (M : MultitapeTM) (base : (machine M).Cfg)
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
  have ht := owned_intmultrackedbankpreparationwindow_prep_copy_start_transition M
    (fun i => (initialFrame M base sigma offset x y).cells i ((initialFrame M base sigma offset x y).head i)) hb
  change transition M (initialFrame M base sigma offset x y).state
    (fun i => (initialFrame M base sigma offset x y).cells i ((initialFrame M base sigma offset x y).head i)) = _ at ht
  apply owned_intmultrackedbankpreparationwindow_prep_copy_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hw : 2 ≤ i.val
    · have hg : 1 ≤ i.val := by omega
      simp only [initialFrame,copyFrame,dif_pos hw,if_pos hg,List.take_zero,ite_self]
      exact owned_intmultrackedbankpreparationwindow_fresh_mark M (base.cells i) (offset (BankedSimulation.innerTape M i hw))
    · by_cases hs : i.val = 1
      · have hg : 1 ≤ i.val := by omega
        simp only [initialFrame,copyFrame,dif_neg hw,if_pos hs,if_pos hg]
        exact owned_intmultrackedbankpreparationwindow_source_mark M (base.cells i) sigma (inputWord M x y)
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

private theorem owned_intmultrackedbankpreparationwindow_prep_copy_word_letter (M : MultitapeTM) (x y : List Bool) (a : M.Sym)
    (ha : a ∈ inputWord M x y) : a = M.zero ∨ a = M.one ∨ a = M.sep := by
  simp only [inputWord,List.mem_append,List.mem_cons,List.mem_map] at ha
  rcases ha with ⟨b,_,rfl⟩ | (ha | ⟨b,_,rfl⟩)
  · cases b <;> simp [MultitapeTM.bitSym]
  · exact Or.inr (Or.inr ha)
  · cases b <;> simp [MultitapeTM.bitSym]

private theorem owned_intmultrackedbankpreparationwindow_prep_copy_copy_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Sym M)
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
    · simp only [if_neg ht,if_neg (by tauto : ¬(i.val = 1 ∨ i.val = 2)),owned_intmultrackedbankpreparationwindow_prep_copy_protect_stay]

/-- A single transition simultaneously copies the scanned input symbol to the
child bank and erases it from the mutable source buffer. -/
private theorem owned_intmultrackedbankpreparationwindow_prep_copy_copy_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (j : ℕ)
    (hj : j < (inputWord M x y).length) :
    (machine M).step (copyFrame M base sigma offset x y j) = copyFrame M base sigma offset x y (j + 1) := by
  let w := inputWord M x y
  have hjw : j < w.length := hj
  have hs : (copyFrame M base sigma offset x y j).cells ⟨1,by change 1 < M.k + 2; omega⟩
      ((copyFrame M base sigma offset x y j).head ⟨1,by change 1 < M.k + 2; omega⟩) = some (w[j],true) := by
    change copyTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma w j (sigma + j + 1) = _
    rw [owned_intmultrackedbankpreparationwindow_copy_read,List.getD_eq_getElem _ _ hjw]
    simp only [hjw,decide_true]
  have hl : (w.take j).length = j := by simp [Nat.min_eq_left hjw.le]
  have hd : (copyFrame M base sigma offset x y j).cells
      ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩
      ((copyFrame M base sigma offset x y j).head
        ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩) = some (M.blank,false) := by
    change bankTape M (base.cells ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩)
      (offset M.inTape) (w.take j) (offset M.inTape + j + 1) = _
    rw [owned_intmultrackedbankpreparationwindow_bank_payload,List.getD_eq_default _ _ (by omega)]
    simp [hl]
  have ht := owned_intmultrackedbankpreparationwindow_prep_copy_copy_transition M
    (fun i => (copyFrame M base sigma offset x y j).cells i ((copyFrame M base sigma offset x y j).head i))
      w[j] (owned_intmultrackedbankpreparationwindow_prep_copy_word_letter M x y w[j] (List.getElem_mem hj)) hs hd
  change transition M (copyFrame M base sigma offset x y j).state
    (fun i => (copyFrame M base sigma offset x y j).cells i ((copyFrame M base sigma offset x y j).head i)) = _ at ht
  apply owned_intmultrackedbankpreparationwindow_prep_copy_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hs : i.val = 1
    · have hw : ¬2 ≤ i.val := by omega
      simp only [if_pos hs,copyFrame,dif_neg hw]
      exact owned_intmultrackedbankpreparationwindow_copy_erase M (base.cells i) sigma w j
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
          owned_intmultrackedbankpreparationwindow_bank_append M (base.cells i) (offset (BankedSimulation.innerTape M i hw)) (w.take j) w[j]
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

private theorem owned_intmultrackedbankpreparationwindow_copy_run (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (j : ℕ)
    (hj : j ≤ (inputWord M x y).length) :
    (machine M).step^[j] (copyFrame M base sigma offset x y 0) = copyFrame M base sigma offset x y j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),owned_intmultrackedbankpreparationwindow_prep_copy_copy_step M base sigma offset x y j (by omega)]

private theorem owned_intmultrackedbankpreparationwindow_copy_cells_complete (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) :
    (copyFrame M base sigma offset x y (inputWord M x y).length).cells =
      (readyFrame M base sigma offset x y).cells := by
  funext i
  by_cases hw : 2 ≤ i.val
  · rw [owned_intmultrackedbankpreparationwindow_ready_work_cells M base sigma offset x y i hw]
    simp only [copyFrame,dif_pos hw,List.take_length]
  · by_cases hs : i.val = 1
    · simp only [copyFrame,dif_neg hw,if_pos hs,readyFrame,TrackedBankedSimulation.embed,
        dif_neg hw,callerBase,if_pos hs]
      exact owned_intmultrackedbankpreparationwindow_copy_finished M (base.cells i) sigma (inputWord M x y)
    · simp only [copyFrame,dif_neg hw,if_neg hs,readyFrame,TrackedBankedSimulation.embed,
        dif_neg hw,callerBase,if_neg hs]


end IntMul.TrackedBankPreparation



namespace IntMul.TrackedBankPreparation

open IntMul.TrackedBankedSimulation (Sym)

private theorem owned_intmultrackedbankpreparationwindow_prep_complete_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem owned_intmultrackedbankpreparationwindow_prep_complete_protect_right (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .right = (a,.right) := by
  cases a <;> rfl

private theorem owned_intmultrackedbankpreparationwindow_prep_complete_protect_stay (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .stay = (a,.stay) := by
  cases a <;> rfl

private theorem owned_intmultrackedbankpreparationwindow_prep_complete_rewind_word_letter (M : MultitapeTM) (x y : List Bool) (a : M.Sym)
    (ha : a ∈ inputWord M x y) : a = M.zero ∨ a = M.one ∨ a = M.sep := by
  simp only [inputWord,List.mem_append,List.mem_cons,List.mem_map] at ha
  rcases ha with ⟨b,_,rfl⟩ | (ha | ⟨b,_,rfl⟩)
  · cases b <;> simp [MultitapeTM.bitSym]
  · exact Or.inr (Or.inr ha)
  · cases b <;> simp [MultitapeTM.bitSym]

private theorem owned_intmultrackedbankpreparationwindow_prep_complete_copy_end_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Sym M)
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
  · simp only [if_neg ht,owned_intmultrackedbankpreparationwindow_prep_complete_protect_stay]

private theorem owned_intmultrackedbankpreparationwindow_prep_complete_copy_end_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) :
    (machine M).step (copyFrame M base sigma offset x y (inputWord M x y).length) =
      rewindFrame M base sigma offset x y (inputWord M x y).length := by
  let w := inputWord M x y
  change (machine M).step (copyFrame M base sigma offset x y w.length) = rewindFrame M base sigma offset x y w.length
  have hs : (copyFrame M base sigma offset x y w.length).cells ⟨1,by change 1 < M.k + 2; omega⟩
      ((copyFrame M base sigma offset x y w.length).head ⟨1,by change 1 < M.k + 2; omega⟩) = some (M.blank,false) := by
    change copyTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma w w.length (sigma + w.length + 1) = _
    rw [owned_intmultrackedbankpreparationwindow_copy_read,List.getD_eq_default _ _ le_rfl]
    simp
  have hd : (copyFrame M base sigma offset x y w.length).cells
      ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩
      ((copyFrame M base sigma offset x y w.length).head
        ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩) = some (M.blank,false) := by
    change bankTape M (base.cells ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩)
      (offset M.inTape) (w.take w.length) (offset M.inTape + w.length + 1) = _
    rw [List.take_length,owned_intmultrackedbankpreparationwindow_bank_payload,List.getD_eq_default _ _ le_rfl]
    simp
  have ht := owned_intmultrackedbankpreparationwindow_prep_complete_copy_end_transition M
    (fun i => (copyFrame M base sigma offset x y w.length).cells i ((copyFrame M base sigma offset x y w.length).head i)) hs hd
  change transition M (copyFrame M base sigma offset x y w.length).state
    (fun i => (copyFrame M base sigma offset x y w.length).cells i ((copyFrame M base sigma offset x y w.length).head i)) = _ at ht
  apply owned_intmultrackedbankpreparationwindow_prep_complete_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    change (copyFrame M base sigma offset x y w.length).cells i = (readyFrame M base sigma offset x y).cells i
    exact congrFun (owned_intmultrackedbankpreparationwindow_copy_cells_complete M base sigma offset x y) i
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

private theorem owned_intmultrackedbankpreparationwindow_prep_complete_protect_left (M : MultitapeTM) (a : Sym M) (h : a ≠ none) :
    TrackedBankCleanup.protect M a a .left = (a,.left) := by
  cases a with
  | none => exact False.elim (h rfl)
  | some s => rfl

private theorem owned_intmultrackedbankpreparationwindow_prep_complete_word_not_start (M : MultitapeTM) (x y : List Bool) (j : ℕ)
    (hj : j < (inputWord M x y).length) : (inputWord M x y)[j] ≠ M.startSym := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at hd
  have hl := owned_intmultrackedbankpreparationwindow_prep_complete_rewind_word_letter M x y (inputWord M x y)[j] (List.getElem_mem hj)
  aesop

private theorem owned_intmultrackedbankpreparationwindow_prep_complete_return_left_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Sym M)
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
    exact owned_intmultrackedbankpreparationwindow_prep_complete_protect_left M _ hn
  · simp only [if_neg hi,owned_intmultrackedbankpreparationwindow_prep_complete_protect_stay]

private theorem owned_intmultrackedbankpreparationwindow_prep_complete_return_left_step (M : MultitapeTM) (base : (machine M).Cfg)
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
    rw [owned_intmultrackedbankpreparationwindow_ready_work_cells M base sigma offset x y _ (by change 2 ≤ (2 : ℕ); omega)]
    change bankTape M (base.cells ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩)
      (offset M.inTape) w (offset M.inTape + j + 1) = _
    rw [owned_intmultrackedbankpreparationwindow_bank_payload,List.getD_eq_getElem _ _ hj]
    simp only [w,hj,decide_true]
  have hm : (rewindFrame M base sigma offset x y (j + 1)).cells
      ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩
      ((rewindFrame M base sigma offset x y (j + 1)).head
        ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩) ≠ some (M.startSym,true) := by
    rw [hr]
    exact fun he => owned_intmultrackedbankpreparationwindow_prep_complete_word_not_start M x y j hj (congrArg Prod.fst (Option.some.inj he))
  have hn : (rewindFrame M base sigma offset x y (j + 1)).cells
      ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩
      ((rewindFrame M base sigma offset x y (j + 1)).head
        ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩) ≠ none := by
    rw [hr]
    exact Option.some_ne_none _
  have ht := owned_intmultrackedbankpreparationwindow_prep_complete_return_left_transition M
    (fun i => (rewindFrame M base sigma offset x y (j + 1)).cells i
      ((rewindFrame M base sigma offset x y (j + 1)).head i)) hm hn
  change transition M (rewindFrame M base sigma offset x y (j + 1)).state
    (fun i => (rewindFrame M base sigma offset x y (j + 1)).cells i
      ((rewindFrame M base sigma offset x y (j + 1)).head i)) = _ at ht
  apply owned_intmultrackedbankpreparationwindow_prep_complete_cfg_ext
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

private theorem owned_intmultrackedbankpreparationwindow_prep_complete_return_marker_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Sym M)
    (h : a ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩ = some (M.startSym,true)) :
    transition M (.rewind) a = (.halt,fun i => (a i,.stay)) := by
  classical
  simp [transition,rawTransition,h,owned_intmultrackedbankpreparationwindow_prep_complete_protect_stay]

private theorem owned_intmultrackedbankpreparationwindow_prep_complete_return_marker_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) :
    (machine M).step (rewindFrame M base sigma offset x y 0) = readyFrame M base sigma offset x y := by
  have hr : (rewindFrame M base sigma offset x y 0).cells
      ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩
      ((rewindFrame M base sigma offset x y 0).head
        ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩) = some (M.startSym,true) := by
    change (readyFrame M base sigma offset x y).cells
      ⟨2,by change 2 < M.k + 2; have := M.two_le_k; omega⟩ (offset M.inTape) = _
    rw [owned_intmultrackedbankpreparationwindow_ready_work_cells M base sigma offset x y _ (by change 2 ≤ (2 : ℕ); omega)]
    exact owned_intmultrackedbankpreparationwindow_bank_boundary _ _ _ _
  have ht := owned_intmultrackedbankpreparationwindow_prep_complete_return_marker_transition M
    (fun i => (rewindFrame M base sigma offset x y 0).cells i ((rewindFrame M base sigma offset x y 0).head i)) hr
  change transition M (rewindFrame M base sigma offset x y 0).state
    (fun i => (rewindFrame M base sigma offset x y 0).cells i ((rewindFrame M base sigma offset x y 0).head i)) = _ at ht
  apply owned_intmultrackedbankpreparationwindow_prep_complete_cfg_ext
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

private theorem owned_intmultrackedbankpreparationwindow_prep_complete_return_run (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (p : ℕ)
    (hp : p ≤ (inputWord M x y).length) :
    (machine M).step^[p + 1] (rewindFrame M base sigma offset x y p) = readyFrame M base sigma offset x y := by
  induction p with
  | zero => simpa using owned_intmultrackedbankpreparationwindow_prep_complete_return_marker_step M base sigma offset x y
  | succ p ih => rw [Function.iterate_succ_apply,owned_intmultrackedbankpreparationwindow_prep_complete_return_left_step M base sigma offset x y p (by omega),ih (by omega)]

/-- The local buffer and work markers are created physically; the full input
is copied while erased, then its child head is returned to the local marker.
The table is independent of sigma and all bank offsets. -/
private theorem owned_intmultrackedbankpreparationwindow_setup_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) :
    (machine M).step^[2 * (inputWord M x y).length + 3]
      (initialFrame M base sigma offset x y) = readyFrame M base sigma offset x y := by
  let L := (inputWord M x y).length
  have hc : (machine M).step^[L + 2] (initialFrame M base sigma offset x y) = rewindFrame M base sigma offset x y L := by
    rw [show L + 2 = (L + 1) + 1 by omega,Function.iterate_succ_apply',Function.iterate_add_apply,
      Function.iterate_one,owned_intmultrackedbankpreparationwindow_start_step,owned_intmultrackedbankpreparationwindow_copy_run M base sigma offset x y L le_rfl,owned_intmultrackedbankpreparationwindow_prep_complete_copy_end_step]
  rw [show 2 * (inputWord M x y).length + 3 = (L + 1) + (L + 2) by unfold L; omega,
    Function.iterate_add_apply,hc,owned_intmultrackedbankpreparationwindow_prep_complete_return_run M base sigma offset x y L le_rfl]

end IntMul.TrackedBankPreparation


namespace IntMul.TrackedBankPreparation

private def owned_intmultrackedbankpreparationwindow_windowSafe (M : MultitapeTM) (sigma : ℕ) (offset : Fin M.k → ℕ)
    (d : (machine M).Cfg) : Prop :=
  sigma ≤ d.head ⟨1,by change 1 < M.k+2; omega⟩ ∧ ∀ j, offset j ≤ d.head (BankedSimulation.workTape M j)

private theorem owned_intmultrackedbankpreparationwindow_work_inner_window (M : MultitapeTM) (j : Fin M.k)
    (h : 2 ≤ (BankedSimulation.workTape M j).val) :
    BankedSimulation.innerTape M (BankedSimulation.workTape M j) h=j := by
  apply Fin.ext
  simp only [BankedSimulation.innerTape,BankedSimulation.workTape]
  omega

private theorem owned_intmultrackedbankpreparationwindow_initial_safe (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) :
    owned_intmultrackedbankpreparationwindow_windowSafe M sigma offset (initialFrame M base sigma offset x y) := by
  constructor
  · simp only [initialFrame,dif_neg (by change ¬2 ≤ (1:ℕ); omega),if_true]
    exact le_rfl
  · intro j
    simp [initialFrame,BankedSimulation.workTape,BankedSimulation.innerTape]

private theorem owned_intmultrackedbankpreparationwindow_copy_safe (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (r : ℕ) :
    owned_intmultrackedbankpreparationwindow_windowSafe M sigma offset (copyFrame M base sigma offset x y r) := by
  constructor
  · simp only [copyFrame,dif_neg (by change ¬2 ≤ (1:ℕ); omega),if_true]
    omega
  · intro j
    simp [copyFrame,BankedSimulation.workTape,BankedSimulation.innerTape]

private theorem owned_intmultrackedbankpreparationwindow_rewind_safe (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (r : ℕ) :
    owned_intmultrackedbankpreparationwindow_windowSafe M sigma offset (rewindFrame M base sigma offset x y r) := by
  constructor
  · simp only [rewindFrame,dif_neg (by change ¬2 ≤ (1:ℕ); omega),if_true]
    omega
  · intro j
    simp [rewindFrame,BankedSimulation.workTape,BankedSimulation.innerTape]

private theorem owned_intmultrackedbankpreparationwindow_ready_safe (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) :
    owned_intmultrackedbankpreparationwindow_windowSafe M sigma offset (readyFrame M base sigma offset x y) := by
  constructor
  · simp only [readyFrame,TrackedBankedSimulation.embed,
      dif_neg (by change ¬2 ≤ (1:ℕ); omega),callerBase,if_true]
    omega
  · intro j
    simp [readyFrame,TrackedBankedSimulation.embed,BankedSimulation.workTape,BankedSimulation.innerTape,MultitapeTM.initCfg]

private theorem owned_intmultrackedbankpreparationwindow_rewind_prefix (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (L r : ℕ)
    (hL : L ≤ (inputWord M x y).length) (hr : r ≤ L) :
    (machine M).step^[r] (rewindFrame M base sigma offset x y L)=
      rewindFrame M base sigma offset x y (L-r) := by
  induction r with
  | zero => simp only [Function.iterate_zero,Function.id_def,Nat.sub_zero]
  | succ r ih =>
    rw [Function.iterate_succ_apply',ih (by omega)]
    rw [show L-r=(L-r-1)+1 by omega,
      owned_intmultrackedbankpreparationwindow_prep_complete_return_left_step M base sigma offset x y (L-r-1) (by omega)]
    congr 1

private theorem owned_intmultrackedbankpreparationwindow_halted_step_window (N : MultitapeTM) (d : N.Cfg) (halt : d.state=N.qHalt) :
    N.step d=d := by
  apply owned_intmultrackedbankpreparationwindow_prep_complete_cfg_ext
  · simp [MultitapeTM.step,halt,N.halt_fixed]
  · funext i
    simp only [MultitapeTM.step,halt,N.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,N.halt_fixed]

private theorem owned_intmultrackedbankpreparationwindow_halted_iterate_window (N : MultitapeTM) (d : N.Cfg)
    (halt : d.state=N.qHalt) (t : ℕ) : N.step^[t] d=d := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,owned_intmultrackedbankpreparationwindow_halted_step_window N d halt]

/-- Child-bank preparation protects all local bank and source-buffer floors
at every physical time, including every rewind and later halted step. -/
private theorem setup_window_safe (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) :
    ∀ t, sigma ≤ ((machine M).step^[t] (initialFrame M base sigma offset x y)).head ⟨1,by change 1 < M.k+2; omega⟩ ∧
      ∀ j, offset j ≤ ((machine M).step^[t] (initialFrame M base sigma offset x y)).head
        (BankedSimulation.workTape M j) := by
  let L := (inputWord M x y).length
  have hrewind : (machine M).step^[L+2] (initialFrame M base sigma offset x y)=
      rewindFrame M base sigma offset x y L := by
    rw [show L+2=(L+1)+1 by omega,Function.iterate_succ_apply',Function.iterate_add_apply,
      Function.iterate_one,owned_intmultrackedbankpreparationwindow_start_step,owned_intmultrackedbankpreparationwindow_copy_run M base sigma offset x y L le_rfl,owned_intmultrackedbankpreparationwindow_prep_complete_copy_end_step]
  intro t
  change owned_intmultrackedbankpreparationwindow_windowSafe M sigma offset ((machine M).step^[t] (initialFrame M base sigma offset x y))
  by_cases hzero : t=0
  · subst t
    exact owned_intmultrackedbankpreparationwindow_initial_safe M base sigma offset x y
  · by_cases copying : t ≤ L+1
    · rw [show t=(t-1)+1 by omega,Function.iterate_add_apply,Function.iterate_one,owned_intmultrackedbankpreparationwindow_start_step,
        owned_intmultrackedbankpreparationwindow_copy_run M base sigma offset x y _ (by omega)]
      exact owned_intmultrackedbankpreparationwindow_copy_safe M base sigma offset x y _
    · by_cases rewinding : t ≤ 2*L+2
      · rw [show t=(t-(L+2))+(L+2) by omega,Function.iterate_add_apply,hrewind,
          owned_intmultrackedbankpreparationwindow_rewind_prefix M base sigma offset x y L _ le_rfl (by omega)]
        exact owned_intmultrackedbankpreparationwindow_rewind_safe M base sigma offset x y _
      · rw [show t=(t-(2*L+3))+(2*L+3) by omega,Function.iterate_add_apply,
          owned_intmultrackedbankpreparationwindow_setup_correct M base sigma offset x y,
          owned_intmultrackedbankpreparationwindow_halted_iterate_window (machine M) (readyFrame M base sigma offset x y) rfl]
        exact owned_intmultrackedbankpreparationwindow_ready_safe M base sigma offset x y

end IntMul.TrackedBankPreparation



namespace IntMul.TrackedBankReservation

private theorem owned_intmultrackedbankreservationwindow_step_cells_fixed (M : MultitapeTM) (c : (machine M).Cfg) :
    ((machine M).step c).cells=c.cells := by
  classical
  funext i
  cases h : c.state <;> simp only [MultitapeTM.step,h,transition]
  · split_ifs <;> exact Function.update_eq_self _ _
  · exact Function.update_eq_self _ _

private theorem owned_intmultrackedbankreservationwindow_step_heads_right (M : MultitapeTM) (c : (machine M).Cfg) (i : Fin (M.k+2)) :
    c.head i ≤ ((machine M).step c).head i := by
  classical
  cases h : c.state with
  | halt => simp [MultitapeTM.step,h,transition]
  | seek =>
    by_cases fresh : ∀ j : Fin M.k, visited M (c.cells (BankedSimulation.workTape M j)
      (c.head (BankedSimulation.workTape M j)))=false
    · simp [MultitapeTM.step,h,transition,fresh]
    · by_cases moving : 2 ≤ i.val ∧ visited M (c.cells i (c.head i))=true
      · simp [MultitapeTM.step,h,transition,fresh,moving]
      · simp [MultitapeTM.step,h,transition,fresh,moving]

private theorem owned_intmultrackedbankreservationwindow_step_low_head (M : MultitapeTM) (c : (machine M).Cfg) (i : Fin (M.k+2))
    (low : i.val < 2) : ((machine M).step c).head i=c.head i := by
  classical
  cases h : c.state with
  | halt => simp [MultitapeTM.step,h,transition]
  | seek =>
    by_cases fresh : ∀ j : Fin M.k, visited M (c.cells (BankedSimulation.workTape M j)
      (c.head (BankedSimulation.workTape M j)))=false
    · simp [MultitapeTM.step,h,transition,fresh]
    · have moving : ¬(2 ≤ i.val ∧ visited M (c.cells i (c.head i))=true) := by intro h; omega
      simp [MultitapeTM.step,h,transition,fresh,moving]

/-- Fresh-bank reservation retains every tape cell, moves each head only
right, and fixes the two caller heads at every physical time. -/
private theorem reserve_trajectory (M : MultitapeTM) (c : (machine M).Cfg) (t : ℕ) :
    ((machine M).step^[t] c).cells=c.cells ∧
      (∀ i, c.head i ≤ ((machine M).step^[t] c).head i) ∧
      (∀ i, i.val < 2 → ((machine M).step^[t] c).head i=c.head i) := by
  induction t with
  | zero => exact ⟨rfl,fun _ => le_rfl,fun _ _ => rfl⟩
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨?_,?_,?_⟩
    · rw [owned_intmultrackedbankreservationwindow_step_cells_fixed,ih.1]
    · intro i
      exact le_trans (ih.2.1 i) (owned_intmultrackedbankreservationwindow_step_heads_right M _ i)
    · intro i hi
      rw [owned_intmultrackedbankreservationwindow_step_low_head M _ i hi,ih.2.2 i hi]

end IntMul.TrackedBankReservation



namespace IntMul.FiniteContinuationStack

open IntMul.TrackedBankedSimulation (Sym)

private theorem owned_intmulfinitecontinuationstacktape_zero_ne_one (M : MultitapeTM) : M.zero ≠ M.one := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,and_true] at hd
  tauto

private theorem decode_onehot (M : MultitapeTM) (n : ℕ) (q : Fin n) (j : ℕ) :
    TrackedBankedSimulation.decode M (some (M.bitSym (decide (j = q.val)),true)) = M.one ↔ j = q.val := by
  by_cases hj : j = q.val
  · simp [hj,MultitapeTM.bitSym,TrackedBankedSimulation.decode]
  · simp [hj,MultitapeTM.bitSym,TrackedBankedSimulation.decode,owned_intmulfinitecontinuationstacktape_zero_ne_one M]

private theorem record_bit (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n)
    (j : ℕ) (r : ℕ) (hr : r < j) :
    recordTape M n base rho q j (rho + r + 1) = some (M.bitSym (decide (r = q.val)),true) := by
  simp [recordTape,show ¬rho + r + 1 < rho by omega,
    show rho + r + 1 ≠ rho by omega,show rho + r + 1 < rho + j + 1 by omega,
    show rho + r + 1 - rho - 1 = r by omega]

private theorem record_marker (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n) (j : ℕ) :
    recordTape M n base rho q j rho = some (M.sep,true) := by simp [recordTape]

private theorem fresh_at (M : MultitapeTM) (base : ℕ → Sym M) (rho p : ℕ) (hp : rho ≤ p) :
    freshTape M base rho p = some (M.blank,false) := by simp [freshTape,show ¬p < rho by omega]

private theorem marker_write (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n) :
    Function.update (freshTape M base rho) rho (some (M.sep,true)) = recordTape M n base rho q 0 := by
  funext p
  by_cases he : p = rho
  · subst p
    simp [recordTape]
  · rw [Function.update_of_ne he]
    by_cases hp : p < rho
    · simp [freshTape,recordTape,hp]
    · simp [freshTape,recordTape,hp,he,show ¬p < rho + 0 + 1 by omega]

private theorem bit_write (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n) (j : ℕ) :
    Function.update (recordTape M n base rho q j) (rho + j + 1)
      (some (M.bitSym (decide (j = q.val)),true)) = recordTape M n base rho q (j + 1) := by
  funext p
  by_cases he : p = rho + j + 1
  · subst p
    simp [recordTape,show ¬rho + j + 1 < rho by omega,show rho + j + 1 ≠ rho by omega,show rho + j + 1 - rho - 1 = j by omega]
  · rw [Function.update_of_ne he]
    by_cases hp : p < rho
    · simp [recordTape,hp]
    · by_cases hm : p = rho
      · simp [recordTape,hp,hm]
      · by_cases hj : p < rho + j + 1
        · simp [recordTape,hp,hm,hj,show p < rho + (j + 1) + 1 by omega]
        · simp [recordTape,hp,hm,hj,show ¬p < rho + (j + 1) + 1 by omega]

private theorem bit_erase (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n)
    (j : ℕ) (hj : j < n) :
    Function.update (recordTape M n base rho q (n - j)) (rho + (n - j)) (some (M.blank,false)) =
      recordTape M n base rho q (n - (j + 1)) := by
  funext p
  by_cases he : p = rho + (n - j)
  · subst p
    simp [recordTape,show ¬rho + (n - j) < rho by omega,show rho + (n - j) ≠ rho by omega,
      show ¬rho + (n - j) < rho + (n - (j + 1)) + 1 by omega,show n - j ≠ 0 by omega]
  · rw [Function.update_of_ne he]
    by_cases hp : p < rho
    · simp [recordTape,hp]
    · by_cases hm : p = rho
      · simp [recordTape,hp,hm]
      · by_cases hbit : p < rho + (n - (j + 1)) + 1
        · simp [recordTape,hp,hm,hbit,show p < rho + (n - j) + 1 by omega]
        · simp [recordTape,hp,hm,hbit,show ¬p < rho + (n - j) + 1 by omega]

private theorem marker_erase (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n) :
    Function.update (recordTape M n base rho q 0) rho (some (M.blank,false)) = freshTape M base rho := by
  funext p
  by_cases he : p = rho
  · subst p
    simp [freshTape]
  · rw [Function.update_of_ne he]
    by_cases hp : p < rho
    · simp [recordTape,freshTape,hp]
    · simp [recordTape,freshTape,hp,he,show ¬p < rho + 0 + 1 by omega]

/-- A correctly read one-hot bit updates a finite control register only.
No host memory stores the continuation. -/
private theorem recovered_step (n : ℕ) (q : Fin n) (j : ℕ) (hj : j < n) :
    (if n - 1 - j = q.val then some (⟨n - 1 - j,by omega⟩ : Fin n) else recovered n q j) =
      recovered n q (j + 1) := by
  unfold recovered
  by_cases he : n - 1 - j = q.val
  · rw [if_pos he,if_pos (by have := q.isLt; omega : n - q.val ≤ j + 1)]
    congr 1
    exact Fin.ext he
  · rw [if_neg he]
    by_cases hp : n - q.val ≤ j
    · rw [if_pos hp,if_pos (by omega : n - q.val ≤ j + 1)]
    · rw [if_neg hp,if_neg (by have := q.isLt; omega : ¬n - q.val ≤ j + 1)]

private theorem pop_scan (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ)
    (q : Fin n) (j : ℕ) (hj : j < n) :
    (popFrame M n base rho q j).cells (stackTape M) ((popFrame M n base rho q j).head (stackTape M)) =
      some (M.bitSym (decide (n - 1 - j = q.val)),true) := by
  simp only [popFrame,ite_true]
  have he : rho + (n - j) = rho + (n - 1 - j) + 1 := by omega
  rw [he,record_bit M n _ rho q (n - j) (n - 1 - j) (by omega)]

end IntMul.FiniteContinuationStack



namespace IntMul.FiniteContinuationStack

open IntMul.TrackedBankedSimulation (Sym)

private theorem owned_intmulfinitecontinuationstacksteps_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem owned_intmulfinitecontinuationstacksteps_raw_other (M : MultitapeTM) (n : ℕ) (q : State n)
    (a : Fin (M.k + 3) → Sym M) (i : Fin (M.k + 3)) (hi : i ≠ stackTape M) :
    (rawTransition M n q a).2 i = (a i,.stay) := by
  classical
  cases q <;> dsimp only [rawTransition] <;> split_ifs <;> simp_all

private theorem owned_intmulfinitecontinuationstacksteps_protect_same_stay (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .stay = (a,.stay) := by cases a <;> rfl

/-- A tagged scan and tagged write make the physical protection wrapper
transparent; every non-stack tape remains exact and its head stays. -/
private theorem owned_intmulfinitecontinuationstacksteps_physical_transition (M : MultitapeTM) (n : ℕ) (q : State n)
    (a : Fin (M.k + 3) → Sym M) (target : State n) (old write : M.Sym × Bool) (d : Move)
    (hs : a (stackTape M) = some old) (hstate : (rawTransition M n q a).1 = target)
    (hstack : (rawTransition M n q a).2 (stackTape M) = (some write,d)) :
    transition M n q a = (target,fun i => if i = stackTape M then (some write,d) else (a i,.stay)) := by
  classical
  apply Prod.ext
  · exact hstate
  · funext i
    change TrackedBankCleanup.protect M (a i) ((rawTransition M n q a).2 i).1
      ((rawTransition M n q a).2 i).2 = _
    by_cases hi : i = stackTape M
    · subst i
      rw [hstack,hs]
      simp only [TrackedBankCleanup.protect,ite_true]
    · rw [owned_intmulfinitecontinuationstacksteps_raw_other M n q a i hi,owned_intmulfinitecontinuationstacksteps_protect_same_stay]
      simp only [if_neg hi]

private theorem push_marker_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step (pushStartFrame M n base rho q) = pushFrame M n base rho q 0 := by
  let a := fun i => (pushStartFrame M n base rho q).cells i ((pushStartFrame M n base rho q).head i)
  have hs : a (stackTape M) = some (M.blank,false) := by
    simp [a,pushStartFrame,freshTape]
  have ht := owned_intmulfinitecontinuationstacksteps_physical_transition M n (.pushStart q) a (pushFrame M n base rho q 0).state
    (M.blank,false) (M.sep,true) .right hs
    (by simp [rawTransition,pushFrame,show 0 < n by have := q.isLt; omega]) (by simp [rawTransition])
  dsimp only [a] at ht
  change transition M n (pushStartFrame M n base rho q).state _ = _ at ht
  apply owned_intmulfinitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,pushStartFrame,pushFrame,ite_true]
      exact marker_write M n _ rho q
    · simp only [if_neg hi,pushStartFrame,pushFrame,if_neg hi]
      exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,pushStartFrame,pushFrame,ite_true,Nat.add_zero]
    · simp only [if_neg hi,pushStartFrame,pushFrame,if_neg hi]

private theorem push_bit_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ)
    (q : Fin n) (j : ℕ) (hj : j < n) :
    (machine M n).step (pushFrame M n base rho q j) = pushFrame M n base rho q (j + 1) := by
  let a := fun i => (pushFrame M n base rho q j).cells i ((pushFrame M n base rho q j).head i)
  have hs : a (stackTape M) = some (M.blank,false) := by
    simp [a,pushFrame,recordTape,show ¬rho + j + 1 < rho by omega,show rho + j + 1 ≠ rho by omega]
  have ht := owned_intmulfinitecontinuationstacksteps_physical_transition M n (pushFrame M n base rho q j).state a
    (pushFrame M n base rho q (j + 1)).state (M.blank,false) (M.bitSym (decide (j = q.val)),true) .right hs
    (by simp only [pushFrame,dif_pos hj,rawTransition])
    (by simp only [pushFrame,dif_pos hj,rawTransition]; split_ifs <;> simp)
  dsimp only [a] at ht
  apply owned_intmulfinitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,pushFrame,ite_true]
      exact bit_write M n _ rho q j
    · simp only [if_neg hi,pushFrame,if_neg hi]
      exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,pushFrame,ite_true]
      omega
    · simp only [if_neg hi,pushFrame,if_neg hi]

/-- One real transition switches from completed push to the pop routine.
A caller compiler can instead intercept pushDone to run its child. -/
private theorem push_dispatch (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step (pushFrame M n base rho q n) = popStartFrame M n base rho q := by
  have ht : transition M n (pushFrame M n base rho q n).state
      (fun i => (pushFrame M n base rho q n).cells i ((pushFrame M n base rho q n).head i)) =
      (.popStart,fun i => ((pushFrame M n base rho q n).cells i ((pushFrame M n base rho q n).head i),.stay)) := by
    simp only [pushFrame,dif_neg (by omega : ¬n < n),transition,rawTransition,owned_intmulfinitecontinuationstacksteps_protect_same_stay]
  apply owned_intmulfinitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    rfl

private theorem pop_start_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step (popStartFrame M n base rho q) = popFrame M n base rho q 0 := by
  let a := fun i => (popStartFrame M n base rho q).cells i ((popStartFrame M n base rho q).head i)
  have hs : a (stackTape M) = some (M.blank,false) := by
    simp [a,popStartFrame,pushFrame,recordTape,show ¬rho + n + 1 < rho by omega,
      show rho + n + 1 ≠ rho by omega]
  have hf : recovered n q 0 = none := by
    simp [recovered,show ¬n - q.val ≤ 0 by have := q.isLt; omega]
  have ht := owned_intmulfinitecontinuationstacksteps_physical_transition M n .popStart a (popFrame M n base rho q 0).state
    (M.blank,false) (M.blank,false) .left hs
    (by simp only [rawTransition,if_pos (by have := q.isLt; omega : 0 < n),popFrame,
      dif_pos (by have := q.isLt; omega : 0 < n),hf])
    (by simp [rawTransition,show 0 < n by have := q.isLt; omega,hs])
  dsimp only [a] at ht
  change transition M n (popStartFrame M n base rho q).state _ = _ at ht
  apply owned_intmulfinitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,popStartFrame,pushFrame,popFrame,ite_true,Nat.sub_zero]
      have hscan : recordTape M n (base.cells (stackTape M)) rho q n (rho + n + 1) = some (M.blank,false) := by
        simpa only [a,popStartFrame,pushFrame,ite_true] using hs
      rw [←hscan,Function.update_eq_self]
    · simp only [if_neg hi,popStartFrame,pushFrame,popFrame,if_neg hi]
      exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,popStartFrame,pushFrame,popFrame,ite_true,Nat.sub_zero]
      omega
    · simp only [if_neg hi,popStartFrame,pushFrame,popFrame,if_neg hi]

private theorem pop_bit_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ)
    (q : Fin n) (j : ℕ) (hj : j < n) :
    (machine M n).step (popFrame M n base rho q j) = popFrame M n base rho q (j + 1) := by
  classical
  let a := fun i => (popFrame M n base rho q j).cells i ((popFrame M n base rho q j).head i)
  have hs : a (stackTape M) = some (M.bitSym (decide (n - 1 - j = q.val)),true) :=
    pop_scan M n base rho q j hj
  have hpred : TrackedBankedSimulation.decode M (a (stackTape M)) = M.one ↔ n - 1 - j = q.val := by
    rw [hs]
    exact decode_onehot M n q (n - 1 - j)
  have hf : (if TrackedBankedSimulation.decode M (a (stackTape M)) = M.one then
      some (⟨n - 1 - j,by omega⟩ : Fin n) else recovered n q j) = recovered n q (j + 1) := by
    simpa only [hpred] using recovered_step n q j hj
  have ht := owned_intmulfinitecontinuationstacksteps_physical_transition M n (popFrame M n base rho q j).state a
    (popFrame M n base rho q (j + 1)).state
    (M.bitSym (decide (n - 1 - j = q.val)),true) (M.blank,false) .left hs
    (by simp only [popFrame,dif_pos hj,rawTransition]; rw [hf])
    (by simp only [popFrame,dif_pos hj,rawTransition]; split_ifs <;> simp)
  dsimp only [a] at ht
  apply owned_intmulfinitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,popFrame,ite_true]
      exact bit_erase M n _ rho q j hj
    · simp only [if_neg hi,popFrame,if_neg hi]
      exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,popFrame,ite_true]
      omega
    · simp only [if_neg hi,popFrame,if_neg hi]

/-- The last physical pop transition erases the separator and enters the
finite resume state containing the recovered label, retaining older records. -/
private theorem pop_marker_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step (popFrame M n base rho q n) = finalFrame M n base rho q := by
  let a := fun i => (popFrame M n base rho q n).cells i ((popFrame M n base rho q n).head i)
  have hs : a (stackTape M) = some (M.sep,true) := by
    simp [a,popFrame,recordTape]
  have hf : recovered n q n = some q := by simp [recovered]
  have ht := owned_intmulfinitecontinuationstacksteps_physical_transition M n (popFrame M n base rho q n).state a (.resume q)
    (M.sep,true) (M.blank,false) .stay hs
    (by simp only [popFrame,dif_neg (by omega : ¬n < n),hf,rawTransition,if_pos hs])
    (by simp [popFrame,hf,rawTransition])
  dsimp only [a] at ht
  apply owned_intmulfinitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,popFrame,finalFrame,pushStartFrame,ite_true,Nat.sub_self,Nat.add_zero]
      exact marker_erase M n _ rho q
    · simp only [if_neg hi,popFrame,finalFrame,pushStartFrame,if_neg hi]
      exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,popFrame,finalFrame,pushStartFrame,ite_true,Nat.sub_self,Nat.add_zero]
    · simp only [if_neg hi,popFrame,finalFrame,pushStartFrame,if_neg hi]

end IntMul.FiniteContinuationStack




namespace IntMul.FiniteContinuationStack

/-- Every write is an actual right-moving transition. The finite counter
has the caller's fixed control size; it never depends on recursion depth. -/
private theorem push_run (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ)
    (q : Fin n) (j : ℕ) (hj : j ≤ n) :
    (machine M n).step^[j] (pushFrame M n base rho q 0) = pushFrame M n base rho q j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),push_bit_step M n base rho q j (by omega)]

private theorem push_correct (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step^[n + 1] (pushStartFrame M n base rho q) = pushFrame M n base rho q n := by
  rw [Function.iterate_add_apply,Function.iterate_one,push_marker_step,push_run M n base rho q n le_rfl]

/-- Every read/erase is an actual left-moving transition, updating only a
finite recovered-label register while retaining all older prefix records. -/
private theorem pop_run (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ)
    (q : Fin n) (j : ℕ) (hj : j ≤ n) :
    (machine M n).step^[j] (popFrame M n base rho q 0) = popFrame M n base rho q j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),pop_bit_step M n base rho q j (by omega)]

private theorem pop_correct (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step^[n + 2] (popStartFrame M n base rho q) = finalFrame M n base rho q := by
  have h : (machine M n).step^[n + 1] (popStartFrame M n base rho q) = popFrame M n base rho q n := by
    rw [Function.iterate_add_apply,Function.iterate_one,pop_start_step,pop_run M n base rho q n le_rfl]
  rw [show n + 2 = (n + 1) + 1 by omega,Function.iterate_succ_apply',h,pop_marker_step]

/-- One physical push-to-pop dispatch is included in the exact round trip.
The returned finite control state contains the recovered continuation q.
All tape cells and head positions equal the complete initial frame. -/
private theorem round_trip_correct (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step^[2 * n + 4] (pushStartFrame M n base rho q) = finalFrame M n base rho q ∧
    ((machine M n).step^[2 * n + 4] (pushStartFrame M n base rho q)).state = .resume q ∧
    ((machine M n).step^[2 * n + 4] (pushStartFrame M n base rho q)).cells =
      (pushStartFrame M n base rho q).cells ∧
    ((machine M n).step^[2 * n + 4] (pushStartFrame M n base rho q)).head =
      (pushStartFrame M n base rho q).head := by
  have h : (machine M n).step^[n + 2] (pushStartFrame M n base rho q) = popStartFrame M n base rho q := by
    rw [show n + 2 = (n + 1) + 1 by omega,Function.iterate_succ_apply',push_correct,push_dispatch]
  have hr : (machine M n).step^[2 * n + 4] (pushStartFrame M n base rho q) = finalFrame M n base rho q := by
    rw [show 2 * n + 4 = (n + 2) + (n + 2) by omega,Function.iterate_add_apply,h,pop_correct]
  refine ⟨hr,?_,?_,?_⟩ <;> rw [hr] <;> rfl

end IntMul.FiniteContinuationStack



namespace IntMul.EndParkRecursiveScheduler

private theorem owned_intmulendparkrecursiveschedulerpadding_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem extension_old_cells (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) (j : Fin N.k) :
    (FixedTapeExtension.embed N base c).cells (FixedTapeExtension.oldTape N j)=c.cells j := by
  simp only [FixedTapeExtension.embed,FixedTapeExtension.oldTape,dif_pos j.isLt]
  have h : FixedTapeExtension.innerTape N ⟨j.val,by have := j.isLt; omega⟩ j.isLt=j := by apply Fin.ext; rfl
  rw [h]

private theorem extension_old_heads (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) (j : Fin N.k) :
    (FixedTapeExtension.embed N base c).head (FixedTapeExtension.oldTape N j)=c.head j := by
  simp only [FixedTapeExtension.embed,FixedTapeExtension.oldTape,dif_pos j.isLt]
  have h : FixedTapeExtension.innerTape N ⟨j.val,by have := j.isLt; omega⟩ j.isLt=j := by apply Fin.ext; rfl
  rw [h]

private theorem extension_extra_cells (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) :
    (FixedTapeExtension.embed N base c).cells (FixedTapeExtension.extraTape N)=base.cells (FixedTapeExtension.extraTape N) := by
  simp [FixedTapeExtension.embed,FixedTapeExtension.extraTape]

private theorem extension_extra_heads (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) :
    (FixedTapeExtension.embed N base c).head (FixedTapeExtension.extraTape N)=base.head (FixedTapeExtension.extraTape N) := by
  simp [FixedTapeExtension.embed,FixedTapeExtension.extraTape]

private theorem extension_cells_ready (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg)
    (old : ∀ j, base.cells (FixedTapeExtension.oldTape N j)=c.cells j) :
    (FixedTapeExtension.embed N base c).cells=base.cells := by
  funext i
  by_cases hi : i.val < N.k
  · simp only [FixedTapeExtension.embed,dif_pos hi]
    have h := old (FixedTapeExtension.innerTape N i hi)
    have he : FixedTapeExtension.oldTape N (FixedTapeExtension.innerTape N i hi)=i := by apply Fin.ext; rfl
    rw [he] at h
    exact h.symm
  · simp only [FixedTapeExtension.embed,dif_neg hi]

private theorem extension_heads_ready (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg)
    (old : ∀ j, base.head (FixedTapeExtension.oldTape N j)=c.head j) :
    (FixedTapeExtension.embed N base c).head=base.head := by
  funext i
  by_cases hi : i.val < N.k
  · simp only [FixedTapeExtension.embed,dif_pos hi]
    have h := old (FixedTapeExtension.innerTape N i hi)
    have he : FixedTapeExtension.oldTape N (FixedTapeExtension.innerTape N i hi)=i := by apply Fin.ext; rfl
    rw [he] at h
    exact h.symm
  · simp only [FixedTapeExtension.embed,dif_neg hi]

private theorem padded_init (N : MultitapeTM) (x y : List Bool) :
    (FixedTapeExtension.machine N).initCfg x y =
      FixedTapeExtension.embed N ((FixedTapeExtension.machine N).initCfg x y) (N.initCfg x y) := by
  apply owned_intmulendparkrecursiveschedulerpadding_cfg_ext
  · rfl
  · apply (extension_cells_ready N _ _ ?_).symm
    intro j
    have hzero : FixedTapeExtension.oldTape N j=(FixedTapeExtension.machine N).inTape ↔ j=N.inTape := by
      constructor
      · intro h; apply Fin.ext
        have hv := congrArg (fun i : Fin (N.k+1) => i.val) h
        exact hv
      · intro h; subst j; rfl
    simp only [MultitapeTM.initCfg,hzero]
    split <;> rfl
  · apply (extension_heads_ready N _ _ ?_).symm
    intro j
    rfl

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveScheduler

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem work_inner (M : MultitapeTM) (i : Fin (M.k+2)) (h : 2≤ i.val) :
    workTape M (innerTape M i h)=i := by
  apply Fin.ext
  simp only [workTape,innerTape]
  omega

private theorem work_injective (M : MultitapeTM) : Function.Injective (workTape M) := by
  intro i j h
  apply Fin.ext
  have h := congrArg Fin.val h
  simp only [workTape] at h
  omega

private theorem work_ne_buffer (M : MultitapeTM) (j : Fin M.k) :
    workTape M j≠TrackedChildInputBridge.bufferTape M := by
  intro h
  have h := congrArg Fin.val h
  simp only [workTape,TrackedChildInputBridge.bufferTape] at h
  omega

private theorem embed_work (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) (p : ℕ) :
    (TrackedBankedSimulation.embed M base offset extent c).cells (workTape M j) (offset j+p)=
      some (c.cells j p,decide (p≤ extent j)) := by
  simp only [TrackedBankedSimulation.embed,workTape]
  rw [dif_pos (by omega)]
  have hi : innerTape M ⟨j.val+2,by omega⟩ (by change 2≤ j.val+2; omega)=j := by
    apply Fin.ext
    simp [innerTape]
  simp only [hi,if_neg (by omega : ¬offset j+p< offset j),show offset j+p-offset j=p by omega]

private theorem embed_work_head (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) :
    (TrackedBankedSimulation.embed M base offset extent c).head (workTape M j)=offset j+c.head j := by
  simp only [TrackedBankedSimulation.embed,workTape]
  rw [dif_pos (by omega)]
  have hi : innerTape M ⟨j.val+2,by omega⟩ (by change 2≤ j.val+2; omega)=j := by
    apply Fin.ext
    simp [innerTape]
  rw [hi]

private theorem embed_cells_ready (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (canonical : ∀ j p, base.cells (workTape M j) (offset j+p)=some (c.cells j p,decide (p≤ extent j))) :
    (TrackedBankedSimulation.embed M base offset extent c).cells=base.cells := by
  funext i p
  dsimp only [TrackedBankedSimulation.embed]
  by_cases hi : 2≤ i.val
  · rw [dif_pos hi]
    let j := innerTape M i hi
    by_cases hp : p< offset j
    · dsimp only [j] at hp
      simp only [if_pos hp]
    · have hle : offset j≤ p := Nat.le_of_not_gt hp
      dsimp only [j] at hp
      rw [if_neg hp]
      have h := canonical j (p-offset j)
      have hw : workTape M j=i := work_inner M i hi
      rw [hw,show offset j+(p-offset j)=p by omega] at h
      exact h.symm
  · simp only [dif_neg hi]

private theorem embed_heads_ready (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (heads : ∀ j, base.head (workTape M j)=offset j+c.head j) :
    (TrackedBankedSimulation.embed M base offset extent c).head=base.head := by
  funext i
  dsimp only [TrackedBankedSimulation.embed]
  by_cases hi : 2≤ i.val
  · rw [dif_pos hi]
    have h := heads (innerTape M i hi)
    rw [work_inner M i hi] at h
    exact h.symm
  · simp only [dif_neg hi]


end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveScheduler

private theorem owned_intmulendparkrecursiveschedulerprograms_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem owned_intmulendparkrecursiveschedulerprograms_fixed_iterate (N : MultitapeTM) (c : N.Cfg) (fixed : N.step c=c) (T : ℕ) :
    N.step^[T] c=c := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,fixed]

private theorem owned_intmulendparkrecursiveschedulerprograms_halted_step (N : MultitapeTM) (c : N.Cfg) (halt : c.state=N.qHalt) : N.step c=c := by
  apply owned_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp [MultitapeTM.step,halt,N.halt_fixed]
  · funext i
    simp only [MultitapeTM.step,halt,N.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,N.halt_fixed]

/-- First entry to any family of quiescent service exits preserves the exact
complete supplied terminal configuration, including all tape heads. -/
private theorem owned_intmulendparkrecursiveschedulerprograms_first_exit (N : MultitapeTM) (P : N.K → Prop)
    (fixed : ∀ d : N.Cfg, P d.state → N.step d=d) (c : N.Cfg) (T : ℕ)
    (exit : P (N.step^[T] c).state) :
    ∃ t, t≤ T ∧ N.step^[t] c=N.step^[T] c ∧ ∀ s, s< t → ¬P (N.step^[s] c).state := by
  classical
  have hex : ∃ t, P (N.step^[t] c).state := ⟨T,exit⟩
  let t := Nat.find hex
  have ht : t≤ T := Nat.find_min' hex exit
  have hp : P (N.step^[t] c).state := Nat.find_spec hex
  refine ⟨t,ht,?_,?_⟩
  · rw [show T=(T-t)+t by omega,Function.iterate_add_apply,owned_intmulendparkrecursiveschedulerprograms_fixed_iterate N _ (fixed _ hp)]
  · intro s hs
    exact Nat.find_min hex hs

private theorem boot_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (live : c.state≠(bootMachine M).qHalt) :
    (machine M n request resume).step (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step c) := by
  have ht : transition M n request resume (.boot c.state) (fun i => c.cells i (c.head i))=
      (let r := (bootMachine M).δ c.state (fun i => c.cells i (c.head i)); (.boot r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply owned_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftBoot,ht]
  · simp only [MultitapeTM.step,liftBoot,ht]
  · simp only [MultitapeTM.step,liftBoot,ht]

private theorem boot_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((bootMachine M).step^[s] c).state≠(bootMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      boot_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem boot_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (T : ℕ)
    (exit : ((bootMachine M).step^[T] c).state=(bootMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := owned_intmulendparkrecursiveschedulerprograms_first_exit (bootMachine M)
    (fun q => q=(bootMachine M).qHalt) (by intro d hd; exact owned_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [boot_iterate M n request resume c s hlive,he]

private theorem preparation_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (live : c.state≠(preparationMachine M).qHalt) :
    (machine M n request resume).step (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step c) := by
  have ht : transition M n request resume (.preparation c.state) (fun i => c.cells i (c.head i))=
      (let r := (preparationMachine M).δ c.state (fun i => c.cells i (c.head i)); (.preparation r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply owned_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftPreparation,ht]
  · simp only [MultitapeTM.step,liftPreparation,ht]
  · simp only [MultitapeTM.step,liftPreparation,ht]

private theorem preparation_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((preparationMachine M).step^[s] c).state≠(preparationMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      preparation_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem preparation_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (T : ℕ)
    (exit : ((preparationMachine M).step^[T] c).state=(preparationMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := owned_intmulendparkrecursiveschedulerprograms_first_exit (preparationMachine M)
    (fun q => q=(preparationMachine M).qHalt) (by intro d hd; exact owned_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [preparation_iterate M n request resume c s hlive,he]

private theorem body_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (live : c.state≠(bodyMachine M).qHalt)
    (no_request : request c.state=none) :
    (machine M n request resume).step (liftBody M n request resume c)=
      liftBody M n request resume ((bodyMachine M).step c) := by
  have ht : transition M n request resume (.body c.state) (fun i => c.cells i (c.head i))=
      (let r := (bodyMachine M).δ c.state (fun i => c.cells i (c.head i)); (.body r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live,no_request]
  apply owned_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftBody,ht]
  · simp only [MultitapeTM.step,liftBody,ht]
  · simp only [MultitapeTM.step,liftBody,ht]

private theorem body_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((bodyMachine M).step^[s] c).state≠(bodyMachine M).qHalt)
    (no_request : ∀ s, s < T → request (((bodyMachine M).step^[s] c).state)=none) :
    (machine M n request resume).step^[T] (liftBody M n request resume c)=
      liftBody M n request resume ((bodyMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)) (by intro s hs; exact no_request s (by omega)),
      body_step M n request resume _ (live T (by omega)) (no_request T (by omega)),Function.iterate_succ_apply']

private theorem body_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (T : ℕ)
    (exit : ((bodyMachine M).step^[T] c).state=(bodyMachine M).qHalt)
    (no_request : ∀ s, s < T → request (((bodyMachine M).step^[s] c).state)=none) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftBody M n request resume c)=
      liftBody M n request resume ((bodyMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := owned_intmulendparkrecursiveschedulerprograms_first_exit (bodyMachine M)
    (fun q => q=(bodyMachine M).qHalt) (by intro d hd; exact owned_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [body_iterate M n request resume c s hlive (by intro r hr; exact no_request r (by omega)),he]

private theorem input_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (live : c.state≠(inputMachine M).qHalt) :
    (machine M n request resume).step (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step c) := by
  have ht : transition M n request resume (.input label c.state) (fun i => c.cells i (c.head i))=
      (let r := (inputMachine M).δ c.state (fun i => c.cells i (c.head i)); (.input label r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply owned_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftInput,ht]
  · simp only [MultitapeTM.step,liftInput,ht]
  · simp only [MultitapeTM.step,liftInput,ht]

private theorem input_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((inputMachine M).step^[s] c).state≠(inputMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      input_step M n request resume label _ (live T (by omega)),Function.iterate_succ_apply']

private theorem input_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (T : ℕ)
    (exit : ((inputMachine M).step^[T] c).state=(inputMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := owned_intmulendparkrecursiveschedulerprograms_first_exit (inputMachine M)
    (fun q => q=(inputMachine M).qHalt) (by intro d hd; exact owned_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [input_iterate M n request resume label c s hlive,he]

private theorem reservation_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (live : c.state≠(reservationMachine M).qHalt) :
    (machine M n request resume).step (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step c) := by
  have ht : transition M n request resume (.reservation c.state) (fun i => c.cells i (c.head i))=
      (let r := (reservationMachine M).δ c.state (fun i => c.cells i (c.head i)); (.reservation r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply owned_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftReservation,ht]
  · simp only [MultitapeTM.step,liftReservation,ht]
  · simp only [MultitapeTM.step,liftReservation,ht]

private theorem reservation_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((reservationMachine M).step^[s] c).state≠(reservationMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      reservation_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem reservation_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (T : ℕ)
    (exit : ((reservationMachine M).step^[T] c).state=(reservationMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := owned_intmulendparkrecursiveschedulerprograms_first_exit (reservationMachine M)
    (fun q => q=(reservationMachine M).qHalt) (by intro d hd; exact owned_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [reservation_iterate M n request resume c s hlive,he]

private theorem return_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (live : c.state≠(returnMachine M).qHalt) :
    (machine M n request resume).step (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step c) := by
  have ht : transition M n request resume (.returning c.state) (fun i => c.cells i (c.head i))=
      (let r := (returnMachine M).δ c.state (fun i => c.cells i (c.head i)); (.returning r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply owned_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftReturn,ht]
  · simp only [MultitapeTM.step,liftReturn,ht]
  · simp only [MultitapeTM.step,liftReturn,ht]

private theorem return_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((returnMachine M).step^[s] c).state≠(returnMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      return_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem return_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (T : ℕ)
    (exit : ((returnMachine M).step^[T] c).state=(returnMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := owned_intmulendparkrecursiveschedulerprograms_first_exit (returnMachine M)
    (fun q => q=(returnMachine M).qHalt) (by intro d hd; exact owned_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [return_iterate M n request resume c s hlive,he]

private theorem cleanup_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (live : c.state≠(cleanupMachine M).qHalt) :
    (machine M n request resume).step (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step c) := by
  have ht : transition M n request resume (.cleanup c.state) (fun i => c.cells i (c.head i))=
      (let r := (cleanupMachine M).δ c.state (fun i => c.cells i (c.head i)); (.cleanup r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply owned_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftCleanup,ht]
  · simp only [MultitapeTM.step,liftCleanup,ht]
  · simp only [MultitapeTM.step,liftCleanup,ht]

private theorem cleanup_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((cleanupMachine M).step^[s] c).state≠(cleanupMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      cleanup_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem cleanup_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (T : ℕ)
    (exit : ((cleanupMachine M).step^[T] c).state=(cleanupMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := owned_intmulendparkrecursiveschedulerprograms_first_exit (cleanupMachine M)
    (fun q => q=(cleanupMachine M).qHalt) (by intro d hd; exact owned_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [cleanup_iterate M n request resume c s hlive,he]

private theorem output_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (live : c.state≠(outputMachine M).qHalt) :
    (machine M n request resume).step (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step c) := by
  have ht : transition M n request resume (.output label c.state) (fun i => c.cells i (c.head i))=
      (let r := (outputMachine M).δ c.state (fun i => c.cells i (c.head i)); (.output label r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply owned_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftOutput,ht]
  · simp only [MultitapeTM.step,liftOutput,ht]
  · simp only [MultitapeTM.step,liftOutput,ht]

private theorem output_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((outputMachine M).step^[s] c).state≠(outputMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      output_step M n request resume label _ (live T (by omega)),Function.iterate_succ_apply']

private theorem output_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (T : ℕ)
    (exit : ((outputMachine M).step^[T] c).state=(outputMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := owned_intmulendparkrecursiveschedulerprograms_first_exit (outputMachine M)
    (fun q => q=(outputMachine M).qHalt) (by intro d hd; exact owned_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [output_iterate M n request resume label c s hlive,he]

private theorem finish_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (live : c.state≠(finishMachine M).qHalt) :
    (machine M n request resume).step (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step c) := by
  have ht : transition M n request resume (.finish c.state) (fun i => c.cells i (c.head i))=
      (let r := (finishMachine M).δ c.state (fun i => c.cells i (c.head i)); (.finish r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply owned_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftFinish,ht]
  · simp only [MultitapeTM.step,liftFinish,ht]
  · simp only [MultitapeTM.step,liftFinish,ht]

private theorem finish_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((finishMachine M).step^[s] c).state≠(finishMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      finish_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem finish_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (T : ℕ)
    (exit : ((finishMachine M).step^[T] c).state=(finishMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := owned_intmulendparkrecursiveschedulerprograms_first_exit (finishMachine M)
    (fun q => q=(finishMachine M).qHalt) (by intro d hd; exact owned_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [finish_iterate M n request resume c s hlive,he]

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveScheduler

open IntMul.TrackedBankedSimulation (extents)

private noncomputable def bodyView (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) : (bodyMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankedSimulation.machine M)
    (stackBase M n request resume base rho)
    (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma v) offset extent c)

private theorem body_service_run (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (c : M.Cfg) (v : List Bool) (T : ℕ)
    (marker : ∀ j, c.cells j 0=M.startSym) (near : ∀ j, c.head j ≤ extent j+1) :
    (bodyMachine M).step^[T] (bodyView M n request resume base rho sigma offset extent c v)=
      bodyView M n request resume base rho sigma offset (extents M c extent T) (M.step^[T] c) v := by
  have hr := (FixedTapeExtension.simulate_run (TrackedBankedSimulation.machine M)
    (stackBase M n request resume base rho)
    (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma v) offset extent c) T).1
  rw [(TrackedBankedSimulation.simulate_run M (parentBase M n request resume base sigma v)
    offset extent positive c T marker near).1] at hr
  exact hr

/-- The actual flat scheduler executes an ordinary body segment and reaches
its complete tracked terminal frame without consuming a request state. -/
private theorem body_segment_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (c : M.Cfg) (v : List Bool) (T : ℕ)
    (marker : ∀ j, c.cells j 0=M.startSym) (near : ∀ j, c.head j ≤ extent j+1)
    (halt : (M.step^[T] c).state=M.qHalt)
    (no_request : ∀ s, s < T → request (M.step^[s] c).state=none) :
    ∃ t, t ≤ T ∧ (machine M n request resume).step^[t]
      (bodyFrame M n request resume base rho sigma offset extent c v)=
      bodyFrame M n request resume base rho sigma offset (extents M c extent T) (M.step^[T] c) v := by
  have hr := body_service_run M n request resume base rho sigma offset extent positive c v T marker near
  have hh : ((bodyMachine M).step^[T] (bodyView M n request resume base rho sigma offset extent c v)).state=
      (bodyMachine M).qHalt := by
    rw [hr]
    exact halt
  obtain ⟨t,ht,htrun⟩ := body_to_halt M n request resume
    (bodyView M n request resume base rho sigma offset extent c v) T hh (by
      intro s hs
      rw [body_service_run M n request resume base rho sigma offset extent positive c v s marker near]
      exact no_request s hs)
  rw [hr] at htrun
  exact ⟨t,ht,htrun⟩

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveScheduler

private theorem owned_intmulendparkrecursiveschedulerdispatch_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem owned_intmulendparkrecursiveschedulerdispatch_right_actions (M : MultitapeTM) (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M)
    (tape : Fin (M.k+3)) : moveActions M a tape .right=
      fun i => (a i,if i=tape then .right else .stay) := by
  classical
  funext i
  simp only [moveActions]
  split_ifs <;> cases a i <;> rfl

private theorem owned_intmulendparkrecursiveschedulerdispatch_left_actions (M : MultitapeTM) (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M)
    (tape : Fin (M.k+3)) (present : a tape≠none) : moveActions M a tape .left=
      fun i => (a i,if i=tape then .left else .stay) := by
  classical
  funext i
  simp only [moveActions]
  by_cases hi : i=tape
  · subst i
    simp only [eq_self,if_true]
    cases h : a tape with
    | none => exact False.elim (present h)
    | some s => rfl
  · simp only [if_neg hi]
    cases a i <;> rfl

private theorem stay_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (q : State M n)
    (ht : transition M n request resume c.state (fun i => c.cells i (c.head i))=
      (q,fun i => (c.cells i (c.head i),.stay))) :
    (machine M n request resume).step c=relabel M n request resume q c := by
  apply owned_intmulendparkrecursiveschedulerdispatch_cfg_ext
  · simp only [MultitapeTM.step,ht,relabel]
  · simp only [MultitapeTM.step,ht,relabel]
    funext i
    rw [Function.update_eq_self]
  · simp only [MultitapeTM.step,ht,relabel]

private theorem right_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (q : State M n) (tape : Fin (M.k+3))
    (ht : transition M n request resume c.state (fun i => c.cells i (c.head i))=
      (q,moveActions M (fun i => c.cells i (c.head i)) tape .right)) :
    (machine M n request resume).step c=headFrame M n request resume q c tape (c.head tape+1) := by
  classical
  rw [owned_intmulendparkrecursiveschedulerdispatch_right_actions] at ht
  apply owned_intmulendparkrecursiveschedulerdispatch_cfg_ext
  · simp only [MultitapeTM.step,ht,headFrame]
  · simp only [MultitapeTM.step,ht,headFrame]
    funext i
    rw [Function.update_eq_self]
  · simp only [MultitapeTM.step,ht,headFrame]
    funext i
    by_cases hi : i=tape
    · subst i
      simp
    · simp [hi]

private theorem left_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (q : State M n) (tape : Fin (M.k+3))
    (present : c.cells tape (c.head tape)≠none)
    (ht : transition M n request resume c.state (fun i => c.cells i (c.head i))=
      (q,moveActions M (fun i => c.cells i (c.head i)) tape .left)) :
    (machine M n request resume).step c=headFrame M n request resume q c tape (c.head tape-1) := by
  classical
  rw [owned_intmulendparkrecursiveschedulerdispatch_left_actions M _ tape present] at ht
  apply owned_intmulendparkrecursiveschedulerdispatch_cfg_ext
  · simp only [MultitapeTM.step,ht,headFrame]
  · simp only [MultitapeTM.step,ht,headFrame]
    funext i
    rw [Function.update_eq_self]
  · simp only [MultitapeTM.step,ht,headFrame]
    funext i
    by_cases hi : i=tape
    · subst i
      simp
    · simp [hi]

private theorem boot_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (exit : c.state=(bootMachine M).qHalt) :
    (machine M n request resume).step (liftBoot M n request resume c)=headFrame M n request resume (.preparation .mark) (liftBoot M n request resume c) (stackTape M) (c.head (stackTape M)+1) := by
  apply right_step
  change transition M n request resume (.boot c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem preparation_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (exit : c.state=(preparationMachine M).qHalt) :
    (machine M n request resume).step (liftPreparation M n request resume c)=relabel M n request resume (.resetBuffer) (liftPreparation M n request resume c) := by
  apply stay_step
  change transition M n request resume (.preparation c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem input_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (exit : c.state=(inputMachine M).qHalt) :
    (machine M n request resume).step (liftInput M n request resume label c)=relabel M n request resume (.push (.pushStart label)) (liftInput M n request resume label c) := by
  apply stay_step
  change transition M n request resume (.input label c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem reservation_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (exit : c.state=(reservationMachine M).qHalt) :
    (machine M n request resume).step (liftReservation M n request resume c)=relabel M n request resume (.preparation .mark) (liftReservation M n request resume c) := by
  apply stay_step
  change transition M n request resume (.reservation c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem return_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (exit : c.state=(returnMachine M).qHalt) :
    (machine M n request resume).step (liftReturn M n request resume c)=relabel M n request resume (.cleanup .rewind) (liftReturn M n request resume c) := by
  apply stay_step
  change transition M n request resume (.returning c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem cleanup_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (exit : c.state=(cleanupMachine M).qHalt)
    (present : c.cells (stackTape M) (c.head (stackTape M))≠none) :
    (machine M n request resume).step (liftCleanup M n request resume c)=headFrame M n request resume (.inspectStack) (liftCleanup M n request resume c) (stackTape M) (c.head (stackTape M)-1) := by
  apply left_step M n request resume _ _ _ present
  change transition M n request resume (.cleanup c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem output_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (exit : c.state=(outputMachine M).qHalt) :
    (machine M n request resume).step (liftOutput M n request resume label c)=relabel M n request resume (.body (resume label)) (liftOutput M n request resume label c) := by
  apply stay_step
  change transition M n request resume (.output label c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem finish_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (exit : c.state=(finishMachine M).qHalt) :
    (machine M n request resume).step (liftFinish M n request resume c)=relabel M n request resume (.halt) (liftFinish M n request resume c) := by
  apply stay_step
  change transition M n request resume (.finish c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem body_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (exit : c.state=(bodyMachine M).qHalt) :
    (machine M n request resume).step (liftBody M n request resume c)=relabel M n request resume ( .returning (returnMachine M).qStart) (liftBody M n request resume c) := by
  apply stay_step
  change transition M n request resume (.body c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem body_request_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (label : Fin n) (live : c.state≠M.qHalt)
    (call : request c.state=some label) :
    (machine M n request resume).step (liftBody M n request resume c)=
      relabel M n request resume (.input label .before) (liftBody M n request resume c) := by
  apply stay_step
  change transition M n request resume (.body c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live,call]
  all_goals try rfl

private theorem push_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (exit : c.state=.pushDone) :
    (machine M n request resume).step (liftPush M n request resume c)=
      relabel M n request resume (.reservation .seek) (liftPush M n request resume c) := by
  apply stay_step
  change transition M n request resume (.push c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem pop_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (label : Fin n) (exit : c.state=.resume label) :
    (machine M n request resume).step (liftPop M n request resume c)=
      relabel M n request resume (.output label .before) (liftPop M n request resume c) := by
  apply stay_step
  change transition M n request resume (.pop c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,exit]
  all_goals try rfl

private theorem inspect_root_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.inspectStack)
    (root : c.cells (stackTape M) (c.head (stackTape M))=none) :
    (machine M n request resume).step c=relabel M n request resume (.finish .rewind) c := by
  apply stay_step
  change transition M n request resume c.state _=_
  simp only [transition,phase,FlatRecursiveScheduler.transition,FlatRecursiveScheduler.stackTape,reduceCtorEq,if_false,if_pos root]
  all_goals try rfl

private theorem inspect_parent_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.inspectStack)
    (parent : c.cells (stackTape M) (c.head (stackTape M))≠none) :
    (machine M n request resume).step c=
      headFrame M n request resume (.restore .rewind) c (stackTape M) (c.head (stackTape M)+1) := by
  apply right_step
  change transition M n request resume c.state _=_
  simp only [transition,phase,FlatRecursiveScheduler.transition,FlatRecursiveScheduler.stackTape,reduceCtorEq,if_false,if_neg parent]
  all_goals try rfl

private theorem reset_marker_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.resetBuffer)
    (marker : c.cells (bufferTape M) (c.head (bufferTape M))=some (M.startSym,true)) :
    (machine M n request resume).step c=
      headFrame M n request resume (.body M.qStart) c (bufferTape M) (c.head (bufferTape M)+1) := by
  have hm : c.cells (FlatRecursiveScheduler.bufferTape M) (c.head (FlatRecursiveScheduler.bufferTape M))=some (M.startSym,true) := marker
  apply right_step
  change transition M n request resume c.state _=_
  simp only [transition,phase,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos hm]
  rfl

private theorem reset_live_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.resetBuffer)
    (marker : c.cells (bufferTape M) (c.head (bufferTape M))≠some (M.startSym,true))
    (present : c.cells (bufferTape M) (c.head (bufferTape M))≠none) :
    (machine M n request resume).step c=
      headFrame M n request resume .resetBuffer c (bufferTape M) (c.head (bufferTape M)-1) := by
  have hm : c.cells (FlatRecursiveScheduler.bufferTape M) (c.head (FlatRecursiveScheduler.bufferTape M))≠some (M.startSym,true) := marker
  apply left_step M n request resume _ _ _ present
  change transition M n request resume c.state _=_
  simp only [transition,phase,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg hm]
  rfl

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveScheduler

private theorem owned_intmulendparkrecursiveschedulerreset_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def resetFrame (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a r : ℕ) : (machine M n request resume).Cfg where
  state := .resetBuffer
  cells := c.cells
  head := Function.update c.head (bufferTape M) (sigma+(a-r))

private theorem owned_intmulendparkrecursiveschedulerreset_empty_return_scan (M : MultitapeTM) (base : ℕ → TrackedBankedSimulation.Sym M)
    (sigma p : ℕ) : TrackedOutputReturn.bufferTape M base sigma [] (sigma+p)=
      if p=0 then some (M.startSym,true) else some (M.blank,false) := by
  cases p with
  | zero => simp [TrackedOutputReturn.bufferTape]
  | succ p => simp [TrackedOutputReturn.bufferTape,show ¬sigma+(p+1) < sigma by omega,
      show sigma+(p+1)≠sigma by omega]

private theorem reset_scan (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a r : ℕ)
    (empty : c.cells (bufferTape M)=TrackedOutputReturn.bufferTape M (c.cells (bufferTape M)) sigma []) :
    (resetFrame M n request resume c sigma a r).cells (bufferTape M)
      ((resetFrame M n request resume c sigma a r).head (bufferTape M))=
        if a ≤ r then some (M.startSym,true) else some (M.blank,false) := by
  simp only [resetFrame,Function.update_self]
  rw [empty,owned_intmulendparkrecursiveschedulerreset_empty_return_scan]
  split_ifs <;> first | rfl | omega

private theorem reset_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a r : ℕ)
    (empty : c.cells (bufferTape M)=TrackedOutputReturn.bufferTape M (c.cells (bufferTape M)) sigma [])
    (hr : r < a) :
    (machine M n request resume).step (resetFrame M n request resume c sigma a r)=
      resetFrame M n request resume c sigma a (r+1) := by
  have hscan := reset_scan M n request resume c sigma a r empty
  rw [if_neg (by omega : ¬a ≤ r)] at hscan
  have hm : (resetFrame M n request resume c sigma a r).cells (bufferTape M)
      ((resetFrame M n request resume c sigma a r).head (bufferTape M))≠some (M.startSym,true) := by
    rw [hscan]
    intro h
    have h := congrArg Prod.snd (Option.some.inj h)
    cases h
  rw [reset_live_step M n request resume _ rfl hm (by rw [hscan]; exact Option.some_ne_none _)]
  apply owned_intmulendparkrecursiveschedulerreset_cfg_ext
  · rfl
  · rfl
  · simp only [headFrame,resetFrame,Function.update_self,Function.update_idem]
    congr 1
    omega

private theorem reset_run (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a r : ℕ)
    (empty : c.cells (bufferTape M)=TrackedOutputReturn.bufferTape M (c.cells (bufferTape M)) sigma [])
    (hr : r ≤ a) :
    (machine M n request resume).step^[r] (resetFrame M n request resume c sigma a 0)=
      resetFrame M n request resume c sigma a r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply',ih (by omega),reset_step M n request resume c sigma a r empty (by omega)]

private theorem reset_complete (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a : ℕ)
    (phase : c.state=.resetBuffer) (head : c.head (bufferTape M)=sigma+a)
    (empty : c.cells (bufferTape M)=TrackedOutputReturn.bufferTape M (c.cells (bufferTape M)) sigma []) :
    (machine M n request resume).step^[a+1] c=
      headFrame M n request resume (.body M.qStart) c (bufferTape M) (sigma+1) := by
  have hstart : c=resetFrame M n request resume c sigma a 0 := by
    apply owned_intmulendparkrecursiveschedulerreset_cfg_ext
    · exact phase
    · rfl
    · simp only [resetFrame,Nat.sub_zero,←head]
      exact (Function.update_eq_self _ _).symm
  rw [hstart,Function.iterate_succ_apply',reset_run M n request resume _ sigma a a empty le_rfl]
  have hm := reset_scan M n request resume c sigma a a empty
  rw [if_pos le_rfl] at hm
  rw [reset_marker_dispatch M n request resume _ rfl hm]
  apply owned_intmulendparkrecursiveschedulerreset_cfg_ext
  · rfl
  · rfl
  · simp only [headFrame,resetFrame,Nat.sub_self,Nat.add_zero,Function.update_self,Function.update_idem]

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveCall

open IntMul.EndParkRecursiveScheduler
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem owned_intmulendparkrecursivecallinputframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def inputParent (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) : (TrackedChildInputBridge.machine M).Cfg where
  state := (TrackedChildInputBridge.machine M).qStart
  cells := fun i => base.cells (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) i)
  head := fun i => base.head (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) i)

private noncomputable def inputPadBase (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) : (inputMachine M).Cfg where
  state := (inputMachine M).qStart
  cells := (bodyView M n request resume base rho sigma offset extent c v).cells
  head := (bodyView M n request resume base rho sigma offset extent c v).head

private noncomputable def inputStart (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) : (inputMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedChildInputBridge.machine M)
    (inputPadBase M n request resume base rho sigma offset extent c v)
    (TrackedChildInputBridge.initialFrame M (inputParent M n request resume base) sigma offset extent c v)

private noncomputable def inputFinal (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) : (inputMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedChildInputBridge.machine M)
    (inputPadBase M n request resume base rho sigma offset extent c v)
    (TrackedChildInputBridge.finalFrame M (inputParent M n request resume base) sigma offset extent c v x y)

private theorem owned_intmulendparkrecursivecallinputframes_word_before_heads (M : MultitapeTM) (base : (TrackedChildInputBridge.machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) :
    (TrackedChildInputBridge.beforeFrame M base sigma offset extent c v 0).head=
      TrackedChildInputBridge.initialHeads M base sigma offset extent c v := by
  funext i
  simp only [TrackedChildInputBridge.beforeFrame,Nat.sub_zero]
  by_cases hb : i=TrackedChildInputBridge.bufferTape M
  · subst i
    simp only [if_true,TrackedChildInputBridge.initialHeads,TrackedBankedSimulation.embed,
      TrackedChildInputBridge.bufferTape,dif_neg (by omega : ¬2 ≤ (1 : ℕ)),
      TrackedChildInputBridge.parentBase,if_true]
    omega
  · simp only [if_neg hb]
    by_cases hp : i=TrackedChildInputBridge.packetTape M
    · subst i
      simp only [if_true]
      exact (embed_work_head M (TrackedChildInputBridge.parentBase M base sigma v)
        offset extent c M.outTape).symm
    · simp only [if_neg hp]

private theorem owned_intmulendparkrecursivecallinputframes_word_parent_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (sigma : ℕ) (v : List Bool) :
    TrackedChildInputBridge.parentBase M
      (inputParent M n request resume base) sigma v=
      parentBase M n request resume base sigma v := by
  apply owned_intmulendparkrecursivecallinputframes_cfg_ext
  · rfl
  · funext i
    simp only [TrackedChildInputBridge.parentBase,inputParent,parentBase]
    by_cases hb : i.val=1
    · have he : i=TrackedChildInputBridge.bufferTape M := Fin.ext hb
      simp only [if_pos he,if_pos hb]
    · have he : i≠TrackedChildInputBridge.bufferTape M := by intro h; exact hb (congrArg Fin.val h)
      simp only [if_neg he,if_neg hb]
  · funext i
    simp only [TrackedChildInputBridge.parentBase,inputParent,parentBase]
    by_cases hb : i.val=1
    · have he : i=TrackedChildInputBridge.bufferTape M := Fin.ext hb
      simp only [if_pos he,if_pos hb]
    · have he : i≠TrackedChildInputBridge.bufferTape M := by intro h; exact hb (congrArg Fin.val h)
      simp only [if_neg he,if_neg hb]

private theorem body_input_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) :
    relabel M n request resume (.input label .before)
      (bodyFrame M n request resume base rho sigma offset extent c v)=
    liftInput M n request resume label (inputStart M n request resume base rho sigma offset extent c v) := by
  have hc : (TrackedChildInputBridge.initialFrame M (inputParent M n request resume base)
      sigma offset extent c v).cells=
      (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma v) offset extent c).cells := by
    simp only [TrackedChildInputBridge.initialFrame,
      TrackedChildInputBridge.initialFrame,TrackedChildInputBridge.beforeFrame,
      TrackedChildInputBridge.initialCells,owned_intmulendparkrecursivecallinputframes_word_parent_ready]
  have hh : (TrackedChildInputBridge.initialFrame M (inputParent M n request resume base)
      sigma offset extent c v).head=
      (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma v) offset extent c).head := by
    simp only [TrackedChildInputBridge.initialFrame,
      TrackedChildInputBridge.initialFrame,owned_intmulendparkrecursivecallinputframes_word_before_heads,
      TrackedChildInputBridge.initialHeads,owned_intmulendparkrecursivecallinputframes_word_parent_ready]
  apply owned_intmulendparkrecursivecallinputframes_cfg_ext
  · rfl
  · funext i
    simp only [relabel,bodyFrame,liftBody,liftInput,inputStart,inputPadBase,bodyView,
      FixedTapeExtension.embed,hc]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape]
    · simp only [dif_neg hi]
  · funext i
    simp only [relabel,bodyFrame,liftBody,liftInput,inputStart,inputPadBase,bodyView,
      FixedTapeExtension.embed,hh]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape]
    · simp only [dif_neg hi]

end IntMul.EndParkRecursiveCall



namespace IntMul.EndParkRecursiveCall

open IntMul.EndParkRecursiveScheduler
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem owned_intmulendparkrecursivecallstackframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def pushParent (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (FiniteContinuationStack.machine M n).Cfg where
  state := .popStart
  cells := (inputFinal M n request resume base rho sigma offset extent c v x y).cells
  head := (inputFinal M n request resume base rho sigma offset extent c v x y).head

private theorem input_stack_cells (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (inputFinal M n request resume base rho sigma offset extent c v x y).cells (stackTape M)=
      FiniteContinuationStack.freshTape M (base.cells (stackTape M)) rho := by
  have he : stackTape M=FixedTapeExtension.extraTape (TrackedChildInputBridge.machine M) := by
    apply Fin.ext; rfl
  simp only [inputFinal,he,extension_extra_cells,inputPadBase,bodyView,extension_extra_cells]
  rw [show FixedTapeExtension.extraTape (TrackedChildInputBridge.machine M)=
    FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M) by rfl]
  simp only [extension_extra_cells,extension_extra_heads]
  rw [show FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M)=stackTape M by rfl]
  simp only [stackBase,eq_self,if_true]

private theorem input_stack_head (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (inputFinal M n request resume base rho sigma offset extent c v x y).head (stackTape M)=rho := by
  have he : stackTape M=FixedTapeExtension.extraTape (TrackedChildInputBridge.machine M) := by
    apply Fin.ext; rfl
  simp only [inputFinal,he,extension_extra_heads,inputPadBase,bodyView,extension_extra_heads]
  rw [show FixedTapeExtension.extraTape (TrackedChildInputBridge.machine M)=
    FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M) by rfl]
  simp only [extension_extra_cells,extension_extra_heads]
  rw [show FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M)=stackTape M by rfl]
  simp only [stackBase,eq_self,if_true]

private theorem input_push_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    relabel M n request resume (.push (.pushStart label))
      (liftInput M n request resume label (inputFinal M n request resume base rho sigma offset extent c v x y))=
    liftPush M n request resume (FiniteContinuationStack.pushStartFrame M n
      (pushParent M n request resume base rho sigma offset extent c v x y) rho label) := by
  apply owned_intmulendparkrecursivecallstackframes_cfg_ext
  · rfl
  · funext i p
    simp only [relabel,liftInput,liftPush,FiniteContinuationStack.pushStartFrame,pushParent]
    by_cases hi : i=stackTape M
    · subst i
      simp only [if_true,input_stack_cells,FiniteContinuationStack.freshTape]
      by_cases hp : p < rho <;> simp only [hp,if_true,if_false]
    · simp only [if_neg hi]
  · funext i
    simp only [relabel,liftInput,liftPush,FiniteContinuationStack.pushStartFrame,pushParent]
    by_cases hi : i=stackTape M
    · subst i
      simp only [if_true,input_stack_head]
    · simp only [if_neg hi]

end IntMul.EndParkRecursiveCall



namespace IntMul.EndParkRecursiveCall

open IntMul.EndParkRecursiveScheduler
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem owned_intmulendparkrecursivecallreservationframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def pushed (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (FiniteContinuationStack.machine M n).Cfg :=
  FiniteContinuationStack.pushFrame M n
    (pushParent M n request resume base rho sigma offset extent c v x y) rho label n

private noncomputable def reserveParent (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (TrackedBankReservation.machine M).Cfg where
  state := .seek
  cells := fun i => (pushed M n request resume label base rho sigma offset extent c v x y).cells
    (FixedTapeExtension.oldTape (TrackedBankReservation.machine M) i)
  head := fun i => (pushed M n request resume label base rho sigma offset extent c v x y).head
    (FixedTapeExtension.oldTape (TrackedBankReservation.machine M) i)

private noncomputable def reservePadBase (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (reservationMachine M).Cfg where
  state := .seek
  cells := (pushed M n request resume label base rho sigma offset extent c v x y).cells
  head := (pushed M n request resume label base rho sigma offset extent c v x y).head

private noncomputable def reserveStart (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (reservationMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankReservation.machine M)
    (reservePadBase M n request resume label base rho sigma offset extent c v x y)
    (TrackedBankReservation.initialFrame M
      (reserveParent M n request resume label base rho sigma offset extent c v x y)
      offset extent (parentAfterInput M c))

private noncomputable def reserveFinal (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (reservationMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankReservation.machine M)
    (reservePadBase M n request resume label base rho sigma offset extent c v x y)
    (TrackedBankReservation.finalFrame M
      (reserveParent M n request resume label base rho sigma offset extent c v x y)
      offset extent (parentAfterInput M c))

private theorem stack_ne_old (M : MultitapeTM) (i : Fin (M.k+2)) :
    FixedTapeExtension.oldTape (TrackedBankReservation.machine M) i≠stackTape M := by
  intro h
  have h := congrArg Fin.val h
  simp only [FixedTapeExtension.oldTape,stackTape,FiniteContinuationStack.stackTape] at h
  have := i.isLt
  omega

private theorem reserve_parent_cells (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) (j : Fin M.k) (p : ℕ) :
    (reserveParent M n request resume label base rho sigma offset extent c v x y).cells
      (workTape M j) (offset j+p)=some ((parentAfterInput M c).cells j p,decide (p≤ extent j)) := by
  simp only [reserveParent,pushed,FiniteContinuationStack.pushFrame,if_neg (stack_ne_old M _),pushParent]
  rw [show FixedTapeExtension.oldTape (TrackedBankReservation.machine M) (workTape M j)=
    FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) (workTape M j) by rfl]
  simp only [inputFinal,extension_old_cells,TrackedChildInputBridge.finalFrame,
    if_neg (work_ne_buffer M j),TrackedChildInputBridge.initialCells,parentAfterInput]
  exact embed_work M _ offset extent c j p

private theorem reserve_parent_heads (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) (j : Fin M.k) :
    (reserveParent M n request resume label base rho sigma offset extent c v x y).head
      (workTape M j)=offset j+(parentAfterInput M c).head j := by
  simp only [reserveParent,pushed,FiniteContinuationStack.pushFrame,if_neg (stack_ne_old M _),pushParent]
  rw [show FixedTapeExtension.oldTape (TrackedBankReservation.machine M) (workTape M j)=
    FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) (workTape M j) by rfl]
  simp only [inputFinal,extension_old_heads,TrackedChildInputBridge.finalFrame,
    if_neg (work_ne_buffer M j),parentAfterInput]
  by_cases hj : j=M.outTape
  · subst j
    simp only [TrackedChildInputBridge.packetTape,eq_self,if_true,Nat.add_zero]
  · have hn : workTape M j≠TrackedChildInputBridge.packetTape M := by
      intro h; exact hj (work_injective M h)
    rw [if_neg hn]
    simp only [if_neg hj,TrackedChildInputBridge.initialHeads]
    exact embed_work_head M _ offset extent c j

private theorem push_reserve_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    relabel M n request resume (.reservation .seek)
      (liftPush M n request resume (pushed M n request resume label base rho sigma offset extent c v x y))=
    liftReservation M n request resume (reserveStart M n request resume label base rho sigma offset extent c v x y) := by
  have hc : (TrackedBankReservation.initialFrame M
      (reserveParent M n request resume label base rho sigma offset extent c v x y)
      offset extent (parentAfterInput M c)).cells=
      (reserveParent M n request resume label base rho sigma offset extent c v x y).cells := by
    exact embed_cells_ready M _ offset extent _ (reserve_parent_cells M n request resume label base rho sigma offset extent c v x y)
  have hh : (TrackedBankReservation.initialFrame M
      (reserveParent M n request resume label base rho sigma offset extent c v x y)
      offset extent (parentAfterInput M c)).head=
      (reserveParent M n request resume label base rho sigma offset extent c v x y).head := by
    simp only [TrackedBankReservation.initialFrame,TrackedBankReservation.seekFrame,Nat.zero_min,Nat.add_zero]
    exact embed_heads_ready M
      (TrackedBankReservation.parentBase M (reserveParent M n request resume label base rho sigma offset extent c v x y))
      offset extent (parentAfterInput M c) (reserve_parent_heads M n request resume label base rho sigma offset extent c v x y)
  apply owned_intmulendparkrecursivecallreservationframes_cfg_ext
  · rfl
  · funext i
    simp only [relabel,liftPush,liftReservation,reserveStart,FixedTapeExtension.embed]
    rw [hc]
    simp only [reserveParent,reservePadBase]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
    · simp only [dif_neg hi]
  · funext i
    simp only [relabel,liftPush,liftReservation,reserveStart,FixedTapeExtension.embed]
    rw [hh]
    simp only [reserveParent,reservePadBase]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
    · simp only [dif_neg hi]

end IntMul.EndParkRecursiveCall



namespace IntMul.EndParkRecursiveCall

open IntMul.EndParkRecursiveScheduler
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)
open IntMul.TrackedBankReservation (newOffsets)

private theorem owned_intmulendparkrecursivecallpreparationframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def preparationParent (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (TrackedBankPreparation.machine M).Cfg where
  state := .mark
  cells := (reserveParent M n request resume label base rho sigma offset extent c v x y).cells
  head := (TrackedBankReservation.finalFrame M
    (reserveParent M n request resume label base rho sigma offset extent c v x y)
    offset extent (parentAfterInput M c)).head

private noncomputable def preparationPadBase (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (preparationMachine M).Cfg where
  state := .mark
  cells := (reserveFinal M n request resume label base rho sigma offset extent c v x y).cells
  head := (reserveFinal M n request resume label base rho sigma offset extent c v x y).head

private noncomputable def preparationStart (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (preparationMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankPreparation.machine M)
    (preparationPadBase M n request resume label base rho sigma offset extent c v x y)
    (TrackedBankPreparation.initialFrame M
      (preparationParent M n request resume label base rho sigma offset extent c v x y)
      sigma (newOffsets M offset extent) x y)

private noncomputable def preparationFinal (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (preparationMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankPreparation.machine M)
    (preparationPadBase M n request resume label base rho sigma offset extent c v x y)
    (TrackedBankPreparation.readyFrame M
      (preparationParent M n request resume label base rho sigma offset extent c v x y)
      sigma (newOffsets M offset extent) x y)

private theorem preparation_fresh (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) (j : Fin M.k) :
    TrackedBankPreparation.freshTape M
      ((preparationParent M n request resume label base rho sigma offset extent c v x y).cells (workTape M j))
      (newOffsets M offset extent j)=
    (preparationParent M n request resume label base rho sigma offset extent c v x y).cells (workTape M j) := by
  funext p
  by_cases hp : p < newOffsets M offset extent j
  · simp only [TrackedBankPreparation.freshTape,if_pos hp]
  · simp only [TrackedBankPreparation.freshTape,if_neg hp]
    have ho : offset j≤ p := by unfold newOffsets at hp; omega
    have he : extent j < p-offset j := by unfold newOffsets at hp; omega
    have h := reserve_parent_cells M n request resume label base rho sigma offset extent c v x y j (p-offset j)
    rw [show offset j+(p-offset j)=p by omega] at h
    simp only [parentAfterInput] at h
    rw [show (preparationParent M n request resume label base rho sigma offset extent c v x y).cells
      (workTape M j) p=some (c.cells j (p-offset j),decide (p-offset j≤ extent j)) from h]
    rw [tail j (p-offset j) he]
    simp only [decide_eq_false_iff_not.mpr (by omega : ¬p-offset j≤ extent j)]

private theorem preparation_source (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (preparationParent M n request resume label base rho sigma offset extent c v x y).cells
      ⟨1,by change 1 < M.k+2; omega⟩=
      TrackedBankPreparation.sourceTape M
        ((preparationParent M n request resume label base rho sigma offset extent c v x y).cells
          ⟨1,by change 1 < M.k+2; omega⟩) sigma (TrackedBankPreparation.inputWord M x y) := by
  have he : FixedTapeExtension.oldTape (TrackedBankReservation.machine M) ⟨1,by change 1 < M.k+2; omega⟩≠FiniteContinuationStack.stackTape M :=
    stack_ne_old M _
  simp only [preparationParent,reserveParent,pushed,FiniteContinuationStack.pushFrame,if_neg he,pushParent]
  rw [show FixedTapeExtension.oldTape (TrackedBankReservation.machine M) ⟨1,by change 1 < M.k+2; omega⟩=
    FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) ⟨1,by change 1 < M.k+2; omega⟩ by rfl]
  simp only [inputFinal,extension_old_cells,TrackedChildInputBridge.finalFrame,
    show (⟨1,by change 1 < M.k+2; omega⟩ : Fin (M.k+2))=TrackedChildInputBridge.bufferTape M by rfl,if_true]
  funext p
  by_cases hp : p < sigma <;> simp only [TrackedBankPreparation.sourceTape,hp,if_true,if_false]

private theorem preparation_source_head (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (preparationParent M n request resume label base rho sigma offset extent c v x y).head
      ⟨1,by change 1 < M.k+2; omega⟩=sigma := by
  simp only [preparationParent,TrackedBankReservation.finalFrame,dif_neg (by omega : ¬2≤ (1:ℕ)),
    reserveParent,pushed,FiniteContinuationStack.pushFrame,if_neg (stack_ne_old M _),pushParent]
  rw [show FixedTapeExtension.oldTape (TrackedBankReservation.machine M) ⟨1,by change 1 < M.k+2; omega⟩=
    FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) ⟨1,by change 1 < M.k+2; omega⟩ by rfl]
  simp only [inputFinal,extension_old_heads,TrackedChildInputBridge.finalFrame,
    show (⟨1,by change 1 < M.k+2; omega⟩ : Fin (M.k+2))=TrackedChildInputBridge.bufferTape M by rfl,if_true]

private theorem reserve_preparation_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    relabel M n request resume (.preparation .mark)
      (liftReservation M n request resume (reserveFinal M n request resume label base rho sigma offset extent c v x y))=
    liftPreparation M n request resume (preparationStart M n request resume label base rho sigma offset extent c v x y) := by
  have hc : (TrackedBankReservation.finalFrame M
      (reserveParent M n request resume label base rho sigma offset extent c v x y)
      offset extent (parentAfterInput M c)).cells=
      (reserveParent M n request resume label base rho sigma offset extent c v x y).cells := by
    exact embed_cells_ready M _ offset extent _ (reserve_parent_cells M n request resume label base rho sigma offset extent c v x y)
  have hpc : (TrackedBankPreparation.initialFrame M
      (preparationParent M n request resume label base rho sigma offset extent c v x y)
      sigma (newOffsets M offset extent) x y).cells=
      (preparationParent M n request resume label base rho sigma offset extent c v x y).cells := by
    funext i
    simp only [TrackedBankPreparation.initialFrame]
    by_cases hw : 2≤ i.val
    · simp only [dif_pos hw]
      have h := preparation_fresh M n request resume label base rho sigma offset extent c v x y tail (innerTape M i hw)
      rw [work_inner M i hw] at h
      exact h
    · simp only [dif_neg hw]
      by_cases hb : i.val=1
      · simp only [if_pos hb]
        have hi : i=⟨1,by change 1 < M.k+2; omega⟩ := Fin.ext hb
        rw [hi]
        exact (preparation_source M n request resume label base rho sigma offset extent c v x y).symm
      · simp only [if_neg hb]
  have hph : (TrackedBankPreparation.initialFrame M
      (preparationParent M n request resume label base rho sigma offset extent c v x y)
      sigma (newOffsets M offset extent) x y).head=
      (preparationParent M n request resume label base rho sigma offset extent c v x y).head := by
    funext i
    simp only [TrackedBankPreparation.initialFrame]
    by_cases hw : 2≤ i.val
    · simp only [dif_pos hw,preparationParent,TrackedBankReservation.finalFrame]
    · simp only [dif_neg hw]
      by_cases hb : i.val=1
      · simp only [if_pos hb]
        have hi : i=⟨1,by change 1 < M.k+2; omega⟩ := Fin.ext hb
        rw [hi]
        exact (preparation_source_head M n request resume label base rho sigma offset extent c v x y).symm
      · simp only [if_neg hb]
  apply owned_intmulendparkrecursivecallpreparationframes_cfg_ext
  · rfl
  · funext i
    simp only [relabel,liftReservation,liftPreparation,preparationStart,FixedTapeExtension.embed]
    rw [hpc]
    simp only [reserveFinal,preparationPadBase,preparationParent,FixedTapeExtension.embed]
    rw [hc]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape]
    · simp only [dif_neg hi]
  · funext i
    simp only [relabel,liftReservation,liftPreparation,preparationStart,FixedTapeExtension.embed]
    rw [hph]
    simp only [reserveFinal,preparationPadBase,preparationParent,FixedTapeExtension.embed]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape]
    · simp only [dif_neg hi]

end IntMul.EndParkRecursiveCall



namespace IntMul.EndParkRecursiveCall

open IntMul.EndParkRecursiveScheduler
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)
open IntMul.TrackedBankReservation (newOffsets)

private theorem owned_intmulendparkrecursivecallchildframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem owned_intmulendparkrecursivecallchildframes_bank_empty_buffer (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) :
    TrackedBankPreparation.bankTape M base sigma []=TrackedOutputReturn.bufferTape M base sigma [] := by
  funext p
  by_cases hp : p < sigma
  · simp only [TrackedBankPreparation.bankTape,TrackedOutputReturn.bufferTape,if_pos hp]
  · by_cases he : p=sigma
    · subst p
      simp [TrackedBankPreparation.bankTape,TrackedOutputReturn.bufferTape,MultitapeTM.tapeOf]
    · simp only [TrackedBankPreparation.bankTape,TrackedOutputReturn.bufferTape,if_neg hp,if_neg he]
      cases hq : p-sigma with
      | zero => omega
      | succ q =>
        simp only [MultitapeTM.tapeOf,List.map_nil,List.getD_nil,List.length_nil]
        simp

private theorem owned_intmulendparkrecursivecallchildframes_return_idem (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List Bool) :
    TrackedOutputReturn.bufferTape M (TrackedOutputReturn.bufferTape M base sigma w) sigma w=
      TrackedOutputReturn.bufferTape M base sigma w := by
  funext p
  by_cases hp : p < sigma <;> simp only [TrackedOutputReturn.bufferTape,hp,if_true,if_false]

private theorem preparation_buffer (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (preparationFinal M n request resume label base rho sigma offset extent c v x y).cells (bufferTape M)=
      TrackedOutputReturn.bufferTape M
        ((preparationFinal M n request resume label base rho sigma offset extent c v x y).cells (bufferTape M)) sigma [] ∧
    (preparationFinal M n request resume label base rho sigma offset extent c v x y).head (bufferTape M)=
      sigma+(TrackedBankPreparation.inputWord M x y).length+1 := by
  have hc : (preparationFinal M n request resume label base rho sigma offset extent c v x y).cells (bufferTape M)=
      TrackedBankPreparation.bankTape M
        ((preparationParent M n request resume label base rho sigma offset extent c v x y).cells ⟨1,by change 1 < M.k+2; omega⟩) sigma [] := by
    change (FixedTapeExtension.embed (TrackedBankPreparation.machine M) _
      (TrackedBankPreparation.readyFrame M _ sigma (newOffsets M offset extent) x y)).cells
      (FixedTapeExtension.oldTape (TrackedBankPreparation.machine M) ⟨1,by change 1 < M.k+2; omega⟩)=_
    rw [extension_old_cells]
    simp only [TrackedBankPreparation.readyFrame,TrackedBankedSimulation.embed,
      dif_neg (by omega : ¬2 ≤ (1 : ℕ)),TrackedBankPreparation.callerBase,if_true]
  constructor
  · rw [hc,owned_intmulendparkrecursivecallchildframes_bank_empty_buffer]
    exact (owned_intmulendparkrecursivecallchildframes_return_idem M _ sigma []).symm
  · change (FixedTapeExtension.embed (TrackedBankPreparation.machine M) _
      (TrackedBankPreparation.readyFrame M _ sigma (newOffsets M offset extent) x y)).head
      (FixedTapeExtension.oldTape (TrackedBankPreparation.machine M) ⟨1,by change 1 < M.k+2; omega⟩)=_
    rw [extension_old_heads]
    simp only [TrackedBankPreparation.readyFrame,TrackedBankedSimulation.embed,
      dif_neg (by omega : ¬2 ≤ (1 : ℕ)),TrackedBankPreparation.callerBase,if_true]

private theorem preparation_parent_nonbuffer (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool)
    (i : Fin (M.k+2)) (hi : i.val≠1) :
    (preparationParent M n request resume label base rho sigma offset extent c v x y).cells i=
      (childBase M n request resume base rho sigma offset extent c label).cells
        (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) i) := by
  have hb : i≠TrackedChildInputBridge.bufferTape M := by
    intro h; exact hi (congrArg Fin.val h)
  simp only [preparationParent,reserveParent,pushed,FiniteContinuationStack.pushFrame,
    if_neg (stack_ne_old M i),pushParent]
  rw [show FixedTapeExtension.oldTape (TrackedBankReservation.machine M) i=
    FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) i by rfl]
  simp only [inputFinal,extension_old_cells]
  simp only [TrackedChildInputBridge.finalFrame,if_neg hb,TrackedChildInputBridge.initialCells]
  simp only [childBase,if_neg (stack_ne_old M i),FixedTapeExtension.oldTape,if_neg hi,bodyFrame,liftBody]
  have hs : (⟨i.val,by have := i.isLt; omega⟩ : Fin (M.k+3))≠stackTape M := stack_ne_old M i
  simp only [if_neg hs,FixedTapeExtension.embed,dif_pos i.isLt,FixedTapeExtension.innerTape]
  funext p
  simp only [TrackedBankedSimulation.embed]
  by_cases hw : 2 ≤ i.val
  · simp only [dif_pos hw]
    by_cases hp : p < offset (innerTape M i hw)
    · simp only [if_pos hp,TrackedChildInputBridge.parentBase,if_neg hb,inputParent,parentBase,if_neg hi]
    · simp only [if_neg hp]
  · simp only [dif_neg hw,TrackedChildInputBridge.parentBase,if_neg hb,inputParent,parentBase,if_neg hi]

private theorem preparation_parent_buffer_prefix (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) (p : ℕ) (hp : p < sigma) :
    (preparationParent M n request resume label base rho sigma offset extent c v x y).cells
      ⟨1,by change 1 < M.k+2; omega⟩ p=base.cells (bufferTape M) p := by
  simp only [preparationParent,reserveParent,pushed,FiniteContinuationStack.pushFrame,
    if_neg (stack_ne_old M _),pushParent]
  rw [show FixedTapeExtension.oldTape (TrackedBankReservation.machine M) ⟨1,by change 1 < M.k+2; omega⟩=
    FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) ⟨1,by change 1 < M.k+2; omega⟩ by rfl]
  simp only [inputFinal,extension_old_cells,TrackedChildInputBridge.finalFrame,
    show (⟨1,by change 1 < M.k+2; omega⟩ : Fin (M.k+2))=TrackedChildInputBridge.bufferTape M by rfl,
    if_true,TrackedBankPreparation.sourceTape,if_pos hp,inputParent]
  rfl

private theorem preparation_stack_cells (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (preparationFinal M n request resume label base rho sigma offset extent c v x y).cells (stackTape M)=
      FiniteContinuationStack.recordTape M n (base.cells (stackTape M)) rho label n := by
  have he : stackTape M=FixedTapeExtension.extraTape (TrackedBankPreparation.machine M) := by apply Fin.ext; rfl
  simp only [preparationFinal,he,extension_extra_cells,preparationPadBase,reserveFinal]
  rw [show FixedTapeExtension.extraTape (TrackedBankPreparation.machine M)=
    FixedTapeExtension.extraTape (TrackedBankReservation.machine M) by rfl]
  simp only [extension_extra_cells,reservePadBase,pushed,FiniteContinuationStack.pushFrame]
  rw [show FixedTapeExtension.extraTape (TrackedBankReservation.machine M)=stackTape M by rfl]
  simp only [eq_self,if_true,pushParent,input_stack_cells]
  funext p
  by_cases hp : p < rho <;> simp only [FiniteContinuationStack.recordTape,FiniteContinuationStack.freshTape,hp,if_true,if_false]

private theorem preparation_stack_head (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (preparationFinal M n request resume label base rho sigma offset extent c v x y).head (stackTape M)=rho+n+1 := by
  have he : stackTape M=FixedTapeExtension.extraTape (TrackedBankPreparation.machine M) := by apply Fin.ext; rfl
  simp only [preparationFinal,he,extension_extra_heads,preparationPadBase,reserveFinal]
  rw [show FixedTapeExtension.extraTape (TrackedBankPreparation.machine M)=
    FixedTapeExtension.extraTape (TrackedBankReservation.machine M) by rfl]
  simp only [extension_extra_heads,reservePadBase,pushed,FiniteContinuationStack.pushFrame]
  rw [show FixedTapeExtension.extraTape (TrackedBankReservation.machine M)=stackTape M by rfl]
  simp only [eq_self,if_true]


private theorem preparation_parent_root_head (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool)
    (i : Fin (M.k+2)) (hi : i.val=0) :
    (preparationParent M n request resume label base rho sigma offset extent c v x y).head i=
      base.head (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) i) := by
  have hb : i≠TrackedChildInputBridge.bufferTape M := by intro h; have := congrArg Fin.val h; simp [hi,TrackedChildInputBridge.bufferTape] at this
  have hp : i≠TrackedChildInputBridge.packetTape M := by intro h; have := congrArg Fin.val h; simp [hi,TrackedChildInputBridge.packetTape,workTape] at this
  have hw : ¬2 ≤ i.val := by omega
  simp only [preparationParent,TrackedBankReservation.finalFrame,dif_neg hw,reserveParent,pushed,
    FiniteContinuationStack.pushFrame,if_neg (stack_ne_old M _),pushParent]
  rw [show FixedTapeExtension.oldTape (TrackedBankReservation.machine M) i=
    FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) i by rfl]
  simp only [inputFinal,extension_old_heads,TrackedChildInputBridge.finalFrame,if_neg hb,if_neg hp,
    TrackedChildInputBridge.initialHeads,TrackedBankedSimulation.embed,dif_neg hw,
    TrackedChildInputBridge.parentBase,if_neg hb,inputParent]

private theorem preparation_child_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    headFrame M n request resume (.body M.qStart)
      (relabel M n request resume .resetBuffer
        (liftPreparation M n request resume (preparationFinal M n request resume label base rho sigma offset extent c v x y)))
      (bufferTape M) (sigma+1)=
    childFrame M n request resume base rho sigma offset extent c label x y := by
  classical
  apply owned_intmulendparkrecursivecallchildframes_cfg_ext
  · rfl
  · funext i p
    have hik : i.val < M.k+3 := i.isLt
    by_cases hi : i.val < M.k+2
    · simp only [headFrame,relabel,liftPreparation,preparationFinal,childFrame,bodyFrame,liftBody,
        FixedTapeExtension.embed,dif_pos hi]
      simp only [TrackedBankPreparation.readyFrame,TrackedBankedSimulation.embed,
        TrackedBankPreparation.callerBase,parentBase,FixedTapeExtension.innerTape]
      by_cases hw : 2 ≤ i.val
      · simp only [dif_pos hw]
        by_cases hp : p < newOffsets M offset extent (innerTape M ⟨i.val,hi⟩ hw)
        · simp only [if_pos hp,if_neg (by omega : i.val≠1)]
          exact congrFun (preparation_parent_nonbuffer M n request resume label base rho sigma offset extent c v x y
            ⟨i.val,hi⟩ (by change i.val≠1; omega)) p
        · simp only [if_neg hp]
      · simp only [dif_neg hw]
        by_cases hb : i.val=1
        · simp only [if_pos hb]
          rw [owned_intmulendparkrecursivecallchildframes_bank_empty_buffer]
          by_cases hp : p < sigma
          · simp only [TrackedOutputReturn.bufferTape,if_pos hp]
            have hi1 : (⟨i.val,hi⟩ : Fin (M.k+2))=⟨1,by omega⟩ := Fin.ext hb
            rw [hi1,preparation_parent_buffer_prefix M n request resume label base rho sigma offset extent c v x y p hp]
            change base.cells (bufferTape M) p=
              (childBase M n request resume base rho sigma offset extent c label).cells (bufferTape M) p
            simp [childBase,bufferTape,stackTape,FiniteContinuationStack.stackTape,
              TrackedOutputReturn.bufferTape,hp]
          · simp only [TrackedOutputReturn.bufferTape,if_neg hp]
        · simp only [if_neg hb]
          exact congrFun (preparation_parent_nonbuffer M n request resume label base rho sigma offset extent c v x y
            ⟨i.val,hi⟩ hb) p
    · have he : i=stackTape M := by apply Fin.ext; simp only [stackTape,FiniteContinuationStack.stackTape]; omega
      subst i
      change (preparationFinal M n request resume label base rho sigma offset extent c v x y).cells (stackTape M) p=
        (FixedTapeExtension.embed (TrackedBankedSimulation.machine M)
          (stackBase M n request resume (childBase M n request resume base rho sigma offset extent c label) (rho+n+1))
          (TrackedBankedSimulation.embed M _ _ _ _)).cells (stackTape M) p
      rw [preparation_stack_cells]
      rw [show stackTape M=FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M) by rfl,
        extension_extra_cells]
      rw [show FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M)=stackTape M by rfl]
      simp only [stackBase,if_true,childBase,if_true,FiniteContinuationStack.freshTape]
      by_cases hp : p < rho+n+1
      · simp only [if_pos hp]
      · simp only [if_neg hp,FiniteContinuationStack.recordTape,
          if_neg (by omega : ¬p < rho),if_neg (by omega : p≠rho),if_neg hp]
  · funext i
    have hik : i.val < M.k+3 := i.isLt
    by_cases hb : i=bufferTape M
    · subst i
      simp [headFrame,childFrame,bodyFrame,liftBody,FixedTapeExtension.embed,
        TrackedBankedSimulation.embed,parentBase,bufferTape,FixedTapeExtension.innerTape]
    · simp only [headFrame,Function.update_of_ne hb,relabel,liftPreparation]
      by_cases hi : i.val < M.k+2
      · simp only [preparationFinal,childFrame,bodyFrame,liftBody,FixedTapeExtension.embed,dif_pos hi,
          TrackedBankPreparation.readyFrame,TrackedBankedSimulation.embed,FixedTapeExtension.innerTape]
        by_cases hw : 2 ≤ i.val
        · simp [dif_pos hw,MultitapeTM.initCfg]
        · have hn : i.val≠1 := by intro h; exact hb (Fin.ext h)
          have hz : i.val=0 := by omega
          simp only [dif_neg hw,TrackedBankPreparation.callerBase,parentBase,if_neg hn]
          rw [preparation_parent_root_head M n request resume label base rho sigma offset extent c v x y ⟨i.val,hi⟩ hz]
          simp only [childBase,FixedTapeExtension.oldTape]
          have hs : (⟨i.val,by omega⟩ : Fin (M.k+3))≠stackTape M := by intro h; have := congrArg Fin.val h; simp [stackTape,FiniteContinuationStack.stackTape] at this; omega
          simp only [if_neg hs,if_neg hn,dif_pos hi,dif_neg hw]
      · have he : i=stackTape M := by apply Fin.ext; simp only [stackTape,FiniteContinuationStack.stackTape]; omega
        subst i
        rw [preparation_stack_head]
        simp only [childFrame,bodyFrame,liftBody]
        rw [show stackTape M=FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M) by rfl,
          extension_extra_heads]
        rw [show FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M)=stackTape M by rfl]
        simp only [stackBase,if_true]

end IntMul.EndParkRecursiveCall




namespace IntMul.EndParkRecursiveStack

open IntMul.EndParkRecursiveScheduler

private theorem owned_intmulendparkrecursivestack_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem push_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (live : c.state≠.pushDone) :
    (machine M n request resume).step (liftPush M n request resume c)=
      liftPush M n request resume ((FiniteContinuationStack.machine M n).step c) := by
  have ht : transition M n request resume (.push c.state) (fun i => c.cells i (c.head i))=
      (let r := FiniteContinuationStack.transition M n c.state (fun i => c.cells i (c.head i)); (.push r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply owned_intmulendparkrecursivestack_cfg_ext
  · simp only [MultitapeTM.step,liftPush,ht]
  · simp only [MultitapeTM.step,liftPush,ht]
  · simp only [MultitapeTM.step,liftPush,ht]

private theorem push_run (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (FiniteContinuationStack.machine M n).Cfg) (rho : ℕ) (label : Fin n) (j : ℕ) (hj : j ≤ n) :
    (machine M n request resume).step^[j]
      (liftPush M n request resume (FiniteContinuationStack.pushFrame M n base rho label 0))=
      liftPush M n request resume (FiniteContinuationStack.pushFrame M n base rho label j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hlive : (FiniteContinuationStack.pushFrame M n base rho label j).state≠.pushDone := by
      simp only [FiniteContinuationStack.pushFrame,dif_pos (by omega : j < n)]
      simp
    rw [Function.iterate_succ_apply',ih (by omega),push_step M n request resume _ hlive,
      FiniteContinuationStack.push_bit_step M n base rho label j (by omega)]

private theorem push_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (FiniteContinuationStack.machine M n).Cfg) (rho : ℕ) (label : Fin n) :
    (machine M n request resume).step^[n+1]
      (liftPush M n request resume (FiniteContinuationStack.pushStartFrame M n base rho label))=
      liftPush M n request resume (FiniteContinuationStack.pushFrame M n base rho label n) := by
  have hlive : (FiniteContinuationStack.pushStartFrame M n base rho label).state≠.pushDone := by simp [FiniteContinuationStack.pushStartFrame]
  rw [Function.iterate_add_apply,Function.iterate_one,push_step M n request resume _ hlive,
    FiniteContinuationStack.push_marker_step,push_run M n request resume base rho label n le_rfl]

private theorem pop_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (live : ∀ label, c.state≠.resume label) :
    (machine M n request resume).step (liftPop M n request resume c)=
      liftPop M n request resume ((FiniteContinuationStack.machine M n).step c) := by
  have ht : transition M n request resume (.pop c.state) (fun i => c.cells i (c.head i))=
      (let r := FiniteContinuationStack.transition M n c.state (fun i => c.cells i (c.head i)); (.pop r.1,r.2)) := by
    cases hs : c.state <;> first | (simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false]; try rfl) | skip
    rename_i label
    exact False.elim (live label hs)
  apply owned_intmulendparkrecursivestack_cfg_ext
  · simp only [MultitapeTM.step,liftPop,ht]
  · simp only [MultitapeTM.step,liftPop,ht]
  · simp only [MultitapeTM.step,liftPop,ht]

private theorem pop_run (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (FiniteContinuationStack.machine M n).Cfg) (rho : ℕ) (label : Fin n) (j : ℕ) (hj : j ≤ n) :
    (machine M n request resume).step^[j]
      (liftPop M n request resume (FiniteContinuationStack.popFrame M n base rho label 0))=
      liftPop M n request resume (FiniteContinuationStack.popFrame M n base rho label j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hlive : ∀ q, (FiniteContinuationStack.popFrame M n base rho label j).state≠.resume q := by
      intro q
      simp only [FiniteContinuationStack.popFrame,dif_pos (by omega : j < n)]
      simp
    rw [Function.iterate_succ_apply',ih (by omega),pop_step M n request resume _ hlive,
      FiniteContinuationStack.pop_bit_step M n base rho label j (by omega)]

private theorem pop_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (FiniteContinuationStack.machine M n).Cfg) (rho : ℕ) (label : Fin n) :
    (machine M n request resume).step^[n+2]
      (liftPop M n request resume (FiniteContinuationStack.popStartFrame M n base rho label))=
      liftPop M n request resume (FiniteContinuationStack.finalFrame M n base rho label) := by
  have hlive : ∀ q, (FiniteContinuationStack.popStartFrame M n base rho label).state≠.resume q := by
    intro q
    simp [FiniteContinuationStack.popStartFrame]
  have hr : (machine M n request resume).step^[n+1]
      (liftPop M n request resume (FiniteContinuationStack.popStartFrame M n base rho label))=
      liftPop M n request resume (FiniteContinuationStack.popFrame M n base rho label n) := by
    rw [Function.iterate_add_apply,Function.iterate_one,pop_step M n request resume _ hlive,
      FiniteContinuationStack.pop_start_step,pop_run M n request resume base rho label n le_rfl]
  have hm : ∀ q, (FiniteContinuationStack.popFrame M n base rho label n).state≠.resume q := by
    intro q
    simp [FiniteContinuationStack.popFrame]
  rw [show n+2=(n+1)+1 by omega,Function.iterate_succ_apply',hr,pop_step M n request resume _ hm,
    FiniteContinuationStack.pop_marker_step]

end IntMul.EndParkRecursiveStack


namespace IntMul.EndParkRecursiveCall

open IntMul.EndParkRecursiveScheduler
open IntMul.TrackedBankPreparation (inputWord)
open IntMul.TrackedBankCleanup (span)

private def headSafe (N : MultitapeTM) (d : N.Cfg) : Prop :=
  ∀ i, i ≠ N.inTape → 1 ≤ d.head i

private def safePrefix (N : MultitapeTM) (c : N.Cfg) (T : ℕ) : Prop :=
  ∀ s, s ≤ T → headSafe N (N.step^[s] c)

private theorem safe_concat (N : MultitapeTM) (c d : N.Cfg) (A B : ℕ)
    (run : N.step^[A] c=d) (first : safePrefix N c A) (second : safePrefix N d B) :
    safePrefix N c (B+A) := by
  intro s hs i hi
  by_cases before : s ≤ A
  · exact first s before i hi
  · rw [show s=(s-A)+A by omega,Function.iterate_add_apply,run]
    exact second (s-A) (by omega) i hi

private theorem lifted_first_exit (N S : MultitapeTM) (lift : S.Cfg → N.Cfg)
    (c : S.Cfg) (T : ℕ) (exit : (S.step^[T] c).state=S.qHalt)
    (runs : ∀ t, (∀ r, r < t → (S.step^[r] c).state≠S.qHalt) →
      N.step^[t] (lift c)=lift (S.step^[t] c))
    (safe : ∀ t, headSafe N (lift (S.step^[t] c))) :
    ∃ t, t ≤ T ∧ N.step^[t] (lift c)=lift (S.step^[T] c) ∧ safePrefix N (lift c) t := by
  obtain ⟨t,ht,he,live⟩ := EndParkRecursiveScheduler.owned_intmulendparkrecursiveschedulerprograms_first_exit S
    (fun q => q=S.qHalt)
    (by intro d hd; exact EndParkRecursiveScheduler.owned_intmulendparkrecursiveschedulerprograms_halted_step S d hd)
    c T exit
  refine ⟨t,ht,?_,?_⟩
  · rw [runs t live,he]
  · intro s hs
    rw [runs s (by intro r hr; exact live r (by omega))]
    exact safe s

private theorem padded_head_safe (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg)
    (c : N.Cfg) (t : ℕ) (oldSafe : headSafe N (N.step^[t] c))
    (extraSafe : 1 ≤ base.head (FixedTapeExtension.extraTape N)) :
    headSafe (FixedTapeExtension.machine N)
      ((FixedTapeExtension.machine N).step^[t] (FixedTapeExtension.embed N base c)) := by
  rw [(FixedTapeExtension.simulate_run N base c t).1]
  intro i hi
  simp only [FixedTapeExtension.embed]
  by_cases old : i.val < N.k
  · rw [dif_pos old]
    apply oldSafe
    intro he
    have hz : i.val=0 := congrArg Fin.val he
    exact hi (Fin.ext hz)
  · rw [dif_neg old]
    have he : i=FixedTapeExtension.extraTape N := by
      apply Fin.ext
      change i.val=N.k
      have hilim : i.val < N.k+1 := i.isLt
      omega
    rw [he]
    exact extraSafe

private theorem child_bridge_heads (M : MultitapeTM) (base : (TrackedChildInputBridge.machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool)
    (positive : ∀ j, 1 ≤ offset j) (hsigma : 1 ≤ sigma)
    (packet : c.cells M.outTape=M.tapeOf (inputWord M x y)) (t : ℕ) :
    headSafe (TrackedChildInputBridge.machine M)
      ((TrackedChildInputBridge.machine M).step^[t]
        (TrackedChildInputBridge.initialFrame M base sigma offset extent c v)) := by
  intro i hi
  have nonzero : i.val≠0 := by intro hz; exact hi (Fin.ext hz)
  have h := TrackedChildInputBridge.input_window_safe M base sigma offset extent c v x y packet t
  by_cases work : 2 ≤ i.val
  · let j := BankedSimulation.innerTape M i work
    have he : BankedSimulation.workTape M j=i := by
      apply Fin.ext
      dsimp only [j,BankedSimulation.innerTape,BankedSimulation.workTape]
      omega
    rw [←he]
    exact le_trans (positive j) (h.2 j)
  · have he : i=TrackedChildInputBridge.bufferTape M := by
      apply Fin.ext
      change i.val=1
      omega
    rw [he]
    exact le_trans hsigma h.1

private theorem preparation_heads (M : MultitapeTM) (base : (TrackedBankPreparation.machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool)
    (positive : ∀ j, 1 ≤ offset j) (hsigma : 1 ≤ sigma) (t : ℕ) :
    headSafe (TrackedBankPreparation.machine M)
      ((TrackedBankPreparation.machine M).step^[t]
        (TrackedBankPreparation.initialFrame M base sigma offset x y)) := by
  intro i hi
  have nonzero : i.val≠0 := by intro hz; exact hi (Fin.ext hz)
  have h := TrackedBankPreparation.setup_window_safe M base sigma offset x y t
  by_cases work : 2 ≤ i.val
  · let j := BankedSimulation.innerTape M i work
    have he : BankedSimulation.workTape M j=i := by
      apply Fin.ext
      dsimp only [j,BankedSimulation.innerTape,BankedSimulation.workTape]
      omega
    rw [←he]
    exact le_trans (positive j) (h.2 j)
  · have he : i=⟨1,by change 1 < M.k+2; omega⟩ := by
      apply Fin.ext
      change i.val=1
      omega
    rw [he]
    exact le_trans hsigma h.1

end IntMul.EndParkRecursiveCall


namespace IntMul.EndParkRecursiveCall

open IntMul.EndParkRecursiveScheduler

private theorem push_heads_safe (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (FiniteContinuationStack.machine M n).Cfg) (rho : ℕ) (label : Fin n)
    (hrho : 1 ≤ rho) (safe : headSafe (FiniteContinuationStack.machine M n) base) :
    safePrefix (machine M n request resume)
      (liftPush M n request resume (FiniteContinuationStack.pushStartFrame M n base rho label)) (n+1) := by
  intro t ht i hi
  by_cases zero : t=0
  · subst t
    change 1 ≤ (FiniteContinuationStack.pushStartFrame M n base rho label).head i
    simp only [FiniteContinuationStack.pushStartFrame]
    by_cases stack : i=stackTape M
    · rw [if_pos stack]
      exact hrho
    · rw [if_neg stack]
      exact safe i hi
  · rw [show t=(t-1)+1 by omega,Function.iterate_add_apply,Function.iterate_one,
      EndParkRecursiveStack.push_step M n request resume _ (by simp [FiniteContinuationStack.pushStartFrame]),
      FiniteContinuationStack.push_marker_step,
      EndParkRecursiveStack.push_run M n request resume base rho label (t-1) (by omega)]
    change 1 ≤ (FiniteContinuationStack.pushFrame M n base rho label (t-1)).head i
    simp only [FiniteContinuationStack.pushFrame]
    by_cases stack : i=stackTape M
    · rw [if_pos stack]
      omega
    · rw [if_neg stack]
      exact safe i hi

private theorem reset_heads_safe (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a : ℕ)
    (hsigma : 1 ≤ sigma) (safe : headSafe (machine M n request resume) c)
    (phase : c.state=.resetBuffer) (head : c.head (bufferTape M)=sigma+a)
    (empty : c.cells (bufferTape M)=TrackedOutputReturn.bufferTape M (c.cells (bufferTape M)) sigma []) :
    safePrefix (machine M n request resume) c (a+1) := by
  have hstart : c=resetFrame M n request resume c sigma a 0 := by
    apply EndParkRecursiveScheduler.owned_intmulendparkrecursiveschedulerreset_cfg_ext
    · exact phase
    · rfl
    · simp only [resetFrame,Nat.sub_zero,←head]
      exact (Function.update_eq_self _ _).symm
  intro t ht i hi
  by_cases rewinding : t ≤ a
  · rw [hstart,reset_run M n request resume c sigma a t empty rewinding]
    change 1 ≤ (Function.update c.head (bufferTape M) (sigma+(a-t))) i
    by_cases buffer : i=bufferTape M
    · subst i
      rw [Function.update_self]
      omega
    · rw [Function.update_of_ne buffer]
      exact safe i hi
  · have last : t=a+1 := by omega
    rw [last,reset_complete M n request resume c sigma a phase head empty]
    change 1 ≤ (Function.update c.head (bufferTape M) (sigma+1)) i
    by_cases buffer : i=bufferTape M
    · subst i
      rw [Function.update_self]
      omega
    · rw [Function.update_of_ne buffer]
      exact safe i hi

end IntMul.EndParkRecursiveCall


namespace IntMul.EndParkRecursiveCall

open IntMul.EndParkRecursiveScheduler

private theorem safe_one (N : MultitapeTM) (c d : N.Cfg) (run : N.step c=d)
    (first : headSafe N c) (last : headSafe N d) : safePrefix N c 1 := by
  intro t ht
  by_cases zero : t=0
  · subst t
    exact first
  · have one : t=1 := by omega
    rw [one,Function.iterate_one,run]
    exact last

private theorem padded_heads_monotone (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg)
    (c : N.Cfg) (t : ℕ) (right : ∀ i, c.head i ≤ (N.step^[t] c).head i) :
    ∀ i, (FixedTapeExtension.embed N base c).head i ≤
      ((FixedTapeExtension.machine N).step^[t] (FixedTapeExtension.embed N base c)).head i := by
  intro i
  rw [(FixedTapeExtension.simulate_run N base c t).1]
  simp only [FixedTapeExtension.embed]
  by_cases old : i.val < N.k
  · simp only [dif_pos old]
    exact right _
  · simp only [dif_neg old]
    exact le_rfl

end IntMul.EndParkRecursiveCall


-- Full protected call entry follows.

namespace IntMul.EndParkRecursiveCall

open IntMul.EndParkRecursiveScheduler
open IntMul.TrackedBankPreparation (inputWord)
open IntMul.TrackedBankCleanup (span)

/-- One real recursive call entry in the single flat transition table. -/
private theorem call_entry_protected_prefix (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool)
    (positive : ∀ j, 1 ≤ offset j) (hrho : 1 ≤ rho) (hsigma : 1 ≤ sigma)
    (live : c.state≠M.qHalt) (call : request c.state=some label)
    (packet : c.cells M.outTape=M.tapeOf (inputWord M x y))
    (near : ∀ j, c.head j≤ extent j+1)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∃ t, t ≤ max (c.head M.outTape) (v.length+1)+2*max (inputWord M x y).length v.length+
        3*(inputWord M x y).length+
        span M (TrackedBankReservation.distance M extent (parentAfterInput M c).head)+n+16 ∧
      (machine M n request resume).step^[t]
        (bodyFrame M n request resume base rho sigma offset extent c v)=
        childFrame M n request resume base rho sigma offset extent c label x y ∧
      ∀ a, a ≤ t → ∀ i, i ≠ (machine M n request resume).inTape →
        1 ≤ ((machine M n request resume).step^[a]
          (bodyFrame M n request resume base rho sigma offset extent c v)).head i := by
  have hbody : (machine M n request resume).step
      (bodyFrame M n request resume base rho sigma offset extent c v)=
      liftInput M n request resume label (inputStart M n request resume base rho sigma offset extent c v) := by
    change (machine M n request resume).step
      (liftBody M n request resume (bodyView M n request resume base rho sigma offset extent c v))=_
    rw [body_request_dispatch M n request resume _ label live call]
    exact body_input_ready M n request resume label base rho sigma offset extent c v
  let I := max (c.head M.outTape) (v.length+1)+2*max (inputWord M x y).length v.length+4
  have hir : (inputMachine M).step^[I] (inputStart M n request resume base rho sigma offset extent c v)=
      inputFinal M n request resume base rho sigma offset extent c v x y := by
    have h := (FixedTapeExtension.simulate_run (TrackedChildInputBridge.machine M)
      (inputPadBase M n request resume base rho sigma offset extent c v)
      (TrackedChildInputBridge.initialFrame M (inputParent M n request resume base) sigma offset extent c v) I).1
    rw [(TrackedChildInputBridge.input_correct M (inputParent M n request resume base)
      sigma offset extent c v x y packet).1] at h
    exact h
  have hih : ((inputMachine M).step^[I] (inputStart M n request resume base rho sigma offset extent c v)).state=
      (inputMachine M).qHalt := by rw [hir]; rfl
  have hstackLow : ¬(stackTape M).val < M.k+2 := by change ¬M.k+2 < M.k+2; omega
  have hinputPad : 1 ≤ (inputPadBase M n request resume base rho sigma offset extent c v).head
      (FixedTapeExtension.extraTape (TrackedChildInputBridge.machine M)) := by
    change 1 ≤ (inputPadBase M n request resume base rho sigma offset extent c v).head (stackTape M)
    simpa only [inputPadBase,bodyView,FixedTapeExtension.embed,dif_neg hstackLow,stackBase,if_true] using hrho
  obtain ⟨s,hsc,hsr,hssafe⟩ := lifted_first_exit (machine M n request resume) (inputMachine M)
    (liftInput M n request resume label) (inputStart M n request resume base rho sigma offset extent c v) I hih
    (by intro t live; exact input_iterate M n request resume label _ t live)
    (by
      intro t
      exact padded_head_safe (TrackedChildInputBridge.machine M)
        (inputPadBase M n request resume base rho sigma offset extent c v)
        (TrackedChildInputBridge.initialFrame M (inputParent M n request resume base) sigma offset extent c v)
        t (child_bridge_heads M (inputParent M n request resume base) sigma offset extent c v x y
          positive hsigma packet t) hinputPad)
  rw [hir] at hsr
  have hbodySafe : headSafe (machine M n request resume)
      (bodyFrame M n request resume base rho sigma offset extent c v) := by
    have h := hssafe 0 (Nat.zero_le s)
    change headSafe (machine M n request resume)
      (liftInput M n request resume label (inputStart M n request resume base rho sigma offset extent c v)) at h
    rw [←body_input_ready M n request resume label base rho sigma offset extent c v] at h
    exact h
  have hinputFinalSafe : headSafe (machine M n request resume)
      (liftInput M n request resume label (inputFinal M n request resume base rho sigma offset extent c v x y)) := by
    have h := hssafe s le_rfl
    rw [hsr] at h
    exact h
  have hpushSafe := push_heads_safe M n request resume
    (pushParent M n request resume base rho sigma offset extent c v x y) rho label hrho hinputFinalSafe
  have hpushEntry : (machine M n request resume).step
      (liftInput M n request resume label (inputFinal M n request resume base rho sigma offset extent c v x y))=
      liftPush M n request resume (FiniteContinuationStack.pushStartFrame M n
        (pushParent M n request resume base rho sigma offset extent c v x y) rho label) := by
    rw [input_dispatch M n request resume label _ rfl,input_push_ready]
  have hpushStagedSafe := safe_concat (machine M n request resume)
    (liftInput M n request resume label (inputFinal M n request resume base rho sigma offset extent c v x y))
    (liftPush M n request resume (FiniteContinuationStack.pushStartFrame M n
      (pushParent M n request resume base rho sigma offset extent c v x y) rho label)) 1 (n+1)
    (by simpa only [Function.iterate_one] using hpushEntry)
    (safe_one _ _ _ hpushEntry hinputFinalSafe (hpushSafe 0 (Nat.zero_le _))) hpushSafe
  have hdown1 : (machine M n request resume).step^[s+1]
      (bodyFrame M n request resume base rho sigma offset extent c v)=
      liftInput M n request resume label (inputFinal M n request resume base rho sigma offset extent c v x y) := by
    rw [Function.iterate_succ_apply,hbody,hsr]
  have hstack : (machine M n request resume).step^[n+2]
      (liftInput M n request resume label (inputFinal M n request resume base rho sigma offset extent c v x y))=
      liftPush M n request resume (pushed M n request resume label base rho sigma offset extent c v x y) := by
    rw [show n+2=(n+1)+1 by omega,Function.iterate_succ_apply,input_dispatch M n request resume label _ rfl,
      input_push_ready M n request resume label base rho sigma offset extent c v x y]
    exact EndParkRecursiveStack.push_correct M n request resume _ rho label
  have hdown2 : (machine M n request resume).step^[n+3]
      (liftInput M n request resume label (inputFinal M n request resume base rho sigma offset extent c v x y))=
      liftReservation M n request resume (reserveStart M n request resume label base rho sigma offset extent c v x y) := by
    rw [show n+3=(n+2)+1 by omega,Function.iterate_succ_apply',hstack,
      push_dispatch M n request resume _ (by simp [pushed,FiniteContinuationStack.pushFrame])]
    exact push_reserve_ready M n request resume label base rho sigma offset extent c v x y
  have hpushedSafe : headSafe (machine M n request resume)
      (liftPush M n request resume (pushed M n request resume label base rho sigma offset extent c v x y)) := by
    have h := hpushStagedSafe (n+2) (by omega)
    rw [hstack] at h
    exact h
  have hreserveEntry : (machine M n request resume).step
      (liftPush M n request resume (pushed M n request resume label base rho sigma offset extent c v x y))=
      liftReservation M n request resume (reserveStart M n request resume label base rho sigma offset extent c v x y) := by
    rw [push_dispatch M n request resume _ (by simp [pushed,FiniteContinuationStack.pushFrame]),push_reserve_ready]
  have hreserveEntrySafe : headSafe (machine M n request resume)
      (liftReservation M n request resume (reserveStart M n request resume label base rho sigma offset extent c v x y)) := by
    rw [←push_reserve_ready]
    exact hpushedSafe
  have hstackServiceSafe := safe_concat (machine M n request resume)
    (liftInput M n request resume label (inputFinal M n request resume base rho sigma offset extent c v x y))
    (liftPush M n request resume (pushed M n request resume label base rho sigma offset extent c v x y))
    (n+2) 1 hstack (by simpa only [Nat.add_assoc] using hpushStagedSafe)
    (safe_one _ _ _ hreserveEntry hpushedSafe hreserveEntrySafe)
  rw [show 1+(n+2)=n+3 by omega] at hstackServiceSafe
  have hnear : ∀ j, (parentAfterInput M c).head j≤ extent j+1 := by
    intro j
    simp only [parentAfterInput]
    split
    · omega
    · exact near j
  have htail : ∀ j p, extent j < p → (parentAfterInput M c).cells j p=M.blank := tail
  let R := span M (TrackedBankReservation.distance M extent (parentAfterInput M c).head)+1
  have hrr : (reservationMachine M).step^[R]
      (reserveStart M n request resume label base rho sigma offset extent c v x y)=
      reserveFinal M n request resume label base rho sigma offset extent c v x y := by
    have h := (FixedTapeExtension.simulate_run (TrackedBankReservation.machine M)
      (reservePadBase M n request resume label base rho sigma offset extent c v x y)
      (TrackedBankReservation.initialFrame M
        (reserveParent M n request resume label base rho sigma offset extent c v x y)
        offset extent (parentAfterInput M c)) R).1
    rw [(TrackedBankReservation.reserve_correct M
      (reserveParent M n request resume label base rho sigma offset extent c v x y)
      offset extent (parentAfterInput M c) hnear htail).1] at h
    exact h
  have hrh : ((reservationMachine M).step^[R]
      (reserveStart M n request resume label base rho sigma offset extent c v x y)).state=(reservationMachine M).qHalt := by
    rw [hrr]; rfl
  obtain ⟨q,hqc,hqr,hqsafe⟩ := lifted_first_exit (machine M n request resume) (reservationMachine M)
    (liftReservation M n request resume) (reserveStart M n request resume label base rho sigma offset extent c v x y) R hrh
    (by intro t live; exact reservation_iterate M n request resume _ t live)
    (by
      intro t i hi
      apply le_trans (hreserveEntrySafe i hi)
      exact padded_heads_monotone (TrackedBankReservation.machine M)
        (reservePadBase M n request resume label base rho sigma offset extent c v x y)
        (TrackedBankReservation.initialFrame M
          (reserveParent M n request resume label base rho sigma offset extent c v x y)
          offset extent (parentAfterInput M c)) t
        ((TrackedBankReservation.reserve_trajectory M _ t).2.1) i)
  rw [hrr] at hqr
  have hdown3 : (machine M n request resume).step^[q+1]
      (liftReservation M n request resume (reserveStart M n request resume label base rho sigma offset extent c v x y))=
      liftPreparation M n request resume (preparationStart M n request resume label base rho sigma offset extent c v x y) := by
    rw [Function.iterate_succ_apply',hqr,reservation_dispatch M n request resume _ rfl]
    exact reserve_preparation_ready M n request resume label base rho sigma offset extent c v x y tail
  have hreserveFinalSafe : headSafe (machine M n request resume)
      (liftReservation M n request resume (reserveFinal M n request resume label base rho sigma offset extent c v x y)) := by
    have h := hqsafe q le_rfl
    rw [hqr] at h
    exact h
  have hprepPad : 1 ≤ (preparationPadBase M n request resume label base rho sigma offset extent c v x y).head
      (FixedTapeExtension.extraTape (TrackedBankPreparation.machine M)) := by
    change 1 ≤ (reserveFinal M n request resume label base rho sigma offset extent c v x y).head (stackTape M)
    exact hreserveFinalSafe (stackTape M) (by
      intro h
      have hv := congrArg Fin.val h
      simp only [stackTape,FiniteContinuationStack.stackTape,MultitapeTM.inTape] at hv
      omega)
  have hprepAll : ∀ t, headSafe (machine M n request resume)
      (liftPreparation M n request resume ((preparationMachine M).step^[t]
        (preparationStart M n request resume label base rho sigma offset extent c v x y))) := by
    intro t
    exact padded_head_safe (TrackedBankPreparation.machine M)
      (preparationPadBase M n request resume label base rho sigma offset extent c v x y)
      (TrackedBankPreparation.initialFrame M
        (preparationParent M n request resume label base rho sigma offset extent c v x y)
        sigma (TrackedBankReservation.newOffsets M offset extent) x y) t
      (preparation_heads M _ sigma (TrackedBankReservation.newOffsets M offset extent) x y
        (by intro j; unfold TrackedBankReservation.newOffsets; omega) hsigma t) hprepPad
  have hreserveDispatch : (machine M n request resume).step
      (liftReservation M n request resume (reserveFinal M n request resume label base rho sigma offset extent c v x y))=
      liftPreparation M n request resume (preparationStart M n request resume label base rho sigma offset extent c v x y) := by
    rw [reservation_dispatch M n request resume _ rfl]
    exact reserve_preparation_ready M n request resume label base rho sigma offset extent c v x y tail
  have hreserveServiceSafe := safe_concat (machine M n request resume)
    (liftReservation M n request resume (reserveStart M n request resume label base rho sigma offset extent c v x y))
    (liftReservation M n request resume (reserveFinal M n request resume label base rho sigma offset extent c v x y))
    q 1 hqr hqsafe (safe_one _ _ _ hreserveDispatch hreserveFinalSafe (hprepAll 0))
  let P := 2*(inputWord M x y).length+3
  have hpr : (preparationMachine M).step^[P]
      (preparationStart M n request resume label base rho sigma offset extent c v x y)=
      preparationFinal M n request resume label base rho sigma offset extent c v x y := by
    have h := (FixedTapeExtension.simulate_run (TrackedBankPreparation.machine M)
      (preparationPadBase M n request resume label base rho sigma offset extent c v x y)
      (TrackedBankPreparation.initialFrame M
        (preparationParent M n request resume label base rho sigma offset extent c v x y)
        sigma (TrackedBankReservation.newOffsets M offset extent) x y) P).1
    rw [TrackedBankPreparation.setup_correct] at h
    exact h
  have hph : ((preparationMachine M).step^[P]
      (preparationStart M n request resume label base rho sigma offset extent c v x y)).state=(preparationMachine M).qHalt := by
    rw [hpr]; rfl
  obtain ⟨p,hpc,hprun,hpsafe⟩ := lifted_first_exit (machine M n request resume) (preparationMachine M)
    (liftPreparation M n request resume) (preparationStart M n request resume label base rho sigma offset extent c v x y) P hph
    (by intro t live; exact preparation_iterate M n request resume _ t live) hprepAll
  rw [hpr] at hprun
  have hdown4 : (machine M n request resume).step^[p+1]
      (liftPreparation M n request resume (preparationStart M n request resume label base rho sigma offset extent c v x y))=
      relabel M n request resume .resetBuffer
        (liftPreparation M n request resume (preparationFinal M n request resume label base rho sigma offset extent c v x y)) := by
    rw [Function.iterate_succ_apply',hprun,preparation_dispatch M n request resume _ rfl]
  have hprepFinalSafe : headSafe (machine M n request resume)
      (liftPreparation M n request resume (preparationFinal M n request resume label base rho sigma offset extent c v x y)) := by
    have h := hpsafe p le_rfl
    rw [hprun] at h
    exact h
  have hresetStartSafe : headSafe (machine M n request resume)
      (relabel M n request resume .resetBuffer
        (liftPreparation M n request resume (preparationFinal M n request resume label base rho sigma offset extent c v x y))) :=
    hprepFinalSafe
  have hprepDispatch : (machine M n request resume).step
      (liftPreparation M n request resume (preparationFinal M n request resume label base rho sigma offset extent c v x y))=
      relabel M n request resume .resetBuffer
        (liftPreparation M n request resume (preparationFinal M n request resume label base rho sigma offset extent c v x y)) :=
    preparation_dispatch M n request resume _ rfl
  have hprepServiceSafe := safe_concat (machine M n request resume)
    (liftPreparation M n request resume (preparationStart M n request resume label base rho sigma offset extent c v x y))
    (liftPreparation M n request resume (preparationFinal M n request resume label base rho sigma offset extent c v x y))
    p 1 hprun hpsafe (safe_one _ _ _ hprepDispatch hprepFinalSafe hresetStartSafe)
  have hbuf := preparation_buffer M n request resume label base rho sigma offset extent c v x y
  have hdown5 : (machine M n request resume).step^[(inputWord M x y).length+2]
      (relabel M n request resume .resetBuffer
        (liftPreparation M n request resume (preparationFinal M n request resume label base rho sigma offset extent c v x y)))=
      childFrame M n request resume base rho sigma offset extent c label x y := by
    rw [show (inputWord M x y).length+2=((inputWord M x y).length+1)+1 by omega,
      reset_complete M n request resume _ sigma ((inputWord M x y).length+1) rfl hbuf.2 hbuf.1]
    exact preparation_child_ready M n request resume label base rho sigma offset extent c v x y
  have hresetSafe := reset_heads_safe M n request resume
    (relabel M n request resume .resetBuffer
      (liftPreparation M n request resume (preparationFinal M n request resume label base rho sigma offset extent c v x y)))
    sigma ((inputWord M x y).length+1) hsigma hresetStartSafe rfl hbuf.2 hbuf.1
  have hbodyServiceSafe : safePrefix (machine M n request resume)
      (bodyFrame M n request resume base rho sigma offset extent c v) (s+1) := by
    intro t ht
    by_cases zero : t=0
    · subst t
      exact hbodySafe
    · rw [show t=(t-1)+1 by omega,Function.iterate_add_apply,Function.iterate_one,hbody]
      exact hssafe (t-1) (by omega)
  let a := s+1
  let b := n+3
  let d := q+1
  let e := p+1
  let f := (inputWord M x y).length+2
  refine ⟨f+(e+(d+(b+a))),by dsimp only [a,b,d,e,f,I,R,P] at *; omega,?_,?_⟩
  · rw [Function.iterate_add_apply (machine M n request resume).step f (e+(d+(b+a))),
      Function.iterate_add_apply (machine M n request resume).step e (d+(b+a)),
      Function.iterate_add_apply (machine M n request resume).step d (b+a),
      Function.iterate_add_apply (machine M n request resume).step b a,
      hdown1,hdown2,hdown3,hdown4,hdown5]
  · change safePrefix (machine M n request resume)
      (bodyFrame M n request resume base rho sigma offset extent c v) (f+(e+(d+(b+a))))
    have hEF := safe_concat (machine M n request resume)
      (liftPreparation M n request resume (preparationStart M n request resume label base rho sigma offset extent c v x y))
      (relabel M n request resume .resetBuffer
        (liftPreparation M n request resume (preparationFinal M n request resume label base rho sigma offset extent c v x y)))
      e f hdown4 (by simpa only [e,Nat.add_comm] using hprepServiceSafe) hresetSafe
    have hDEF := safe_concat (machine M n request resume)
      (liftReservation M n request resume (reserveStart M n request resume label base rho sigma offset extent c v x y))
      (liftPreparation M n request resume (preparationStart M n request resume label base rho sigma offset extent c v x y))
      d (f+e) hdown3 (by simpa only [d,Nat.add_comm] using hreserveServiceSafe) hEF
    have hBDEF := safe_concat (machine M n request resume)
      (liftInput M n request resume label (inputFinal M n request resume base rho sigma offset extent c v x y))
      (liftReservation M n request resume (reserveStart M n request resume label base rho sigma offset extent c v x y))
      b ((f+e)+d) hdown2 (by simpa only [b] using hstackServiceSafe) hDEF
    simpa only [Nat.add_assoc] using safe_concat (machine M n request resume)
      (bodyFrame M n request resume base rho sigma offset extent c v)
      (liftInput M n request resume label (inputFinal M n request resume base rho sigma offset extent c v x y))
      a (((f+e)+d)+b) hdown1 hbodyServiceSafe hBDEF


end IntMul.EndParkRecursiveCall



open IntMul IntMul.EndParkRecursiveCall IntMul.EndParkRecursiveScheduler
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankPreparation (inputWord)

theorem solution (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool)
    (positive : ∀ j, 1 ≤ offset j) (hrho : 1 ≤ rho) (hsigma : 1 ≤ sigma)
    (live : c.state≠M.qHalt) (call : request c.state=some label)
    (packet : c.cells M.outTape=M.tapeOf (inputWord M x y))
    (near : ∀ j, c.head j≤ extent j+1)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∃ t, t ≤ max (c.head M.outTape) (v.length+1)+2*max (inputWord M x y).length v.length+
        3*(inputWord M x y).length+
        span M (TrackedBankReservation.distance M extent (parentAfterInput M c).head)+n+16 ∧
      (machine M n request resume).step^[t]
        (bodyFrame M n request resume base rho sigma offset extent c v)=
        childFrame M n request resume base rho sigma offset extent c label x y ∧
      ∀ a, a ≤ t → ∀ i, i ≠ (machine M n request resume).inTape →
        1 ≤ ((machine M n request resume).step^[a]
          (bodyFrame M n request resume base rho sigma offset extent c v)).head i :=
  IntMul.EndParkRecursiveCall.call_entry_protected_prefix M n request resume label base rho sigma offset extent c v x y positive hrho hsigma live call packet near tail

#print axioms solution
