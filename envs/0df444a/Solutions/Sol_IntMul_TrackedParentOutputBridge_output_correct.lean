-- Prove2me | solution 1 for IntMul.TrackedParentOutputBridge.output_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T00:48:50.955796+00:00
-- url     : https://prove2.me/submissions/381ec47d-e2e9-48d7-b1b3-40ae8ef9a3d6

import Definitions.Def_IntMul_TrackedParentOutputBridge
import Mathlib.Data.List.GetD
import Mathlib.Tactic


namespace IntMul.TrackedParentOutputBridge

open IntMul.TrackedBankedSimulation (Sym)

private theorem tape_symbols_distinct (M : MultitapeTM) :
    M.blank≠M.startSym ∧ M.zero≠M.startSym ∧ M.one≠M.startSym := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true] at hd
  tauto

private theorem bit_word_letter (M : MultitapeTM) (w : List Bool) (j : ℕ) (hj : j<w.length) :
    (w.map M.bitSym).getD j M.blank=M.zero ∨ (w.map M.bitSym).getD j M.blank=M.one := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp only [List.getElem_map]
  cases w[j] <;> simp [MultitapeTM.bitSym]

private theorem bit_word_not_start (M : MultitapeTM) (w : List Bool) (j : ℕ) :
    (w.map M.bitSym).getD j M.blank≠M.startSym := by
  by_cases hj : j<w.length
  · rcases bit_word_letter M w j hj with h | h
    · rw [h]; exact (tape_symbols_distinct M).2.1
    · rw [h]; exact (tape_symbols_distinct M).2.2
  · rw [List.getD_eq_default _ _ (by simp only [List.length_map]; omega)]
    exact (tape_symbols_distinct M).1

private theorem bit_tape_marker (M : MultitapeTM) (w : List Bool) (p : ℕ) :
    M.tapeOf (w.map M.bitSym) p=M.startSym ↔ p=0 := by
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
    change (w.map M.bitSym).getD p M.blank=M.startSym ↔ p+1=0
    constructor
    · intro h; exact False.elim (bit_word_not_start M w p h)
    · intro h; omega

private theorem buffer_marker (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List Bool) (p : ℕ) :
    TrackedOutputReturn.bufferTape M base sigma w (sigma+p)=some (M.startSym,true) ↔ p=0 := by
  cases p with
  | zero => simp [TrackedOutputReturn.bufferTape]
  | succ p =>
    simp only [TrackedOutputReturn.bufferTape,if_neg (by omega : ¬sigma+(p+1)<sigma),
      if_neg (by omega : sigma+(p+1)≠sigma),show sigma+(p+1)-sigma-1=p by omega]
    constructor
    · intro h
      have h := congrArg Prod.fst (Option.some.inj h)
      exact False.elim (bit_word_not_start M w p h)
    · intro h; omega

private theorem buffer_payload (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List Bool) (p : ℕ) :
    TrackedOutputReturn.bufferTape M base sigma w (sigma+p+1)=
      some ((w.map M.bitSym).getD p M.blank,decide (p<w.length)) := by
  simp only [TrackedOutputReturn.bufferTape,if_neg (by omega : ¬sigma+p+1<sigma),
    if_neg (by omega : sigma+p+1≠sigma),show sigma+p+1-sigma-1=p by omega]

private theorem old_payload (M : MultitapeTM) (base : ℕ → Sym M) (offset extent : ℕ)
    (cells : ℕ → M.Sym) (p : ℕ) :
    oldTape M base offset extent cells (offset+p)=some (cells p,decide (p≤extent)) := by
  simp only [oldTape,if_neg (by omega : ¬offset+p<offset),show offset+p-offset=p by omega]

private theorem copy_write (M : MultitapeTM) (base : ℕ → Sym M) (offset extent : ℕ)
    (cells : ℕ → M.Sym) (w : List Bool) (j : ℕ) :
    Function.update (copiedTape M base offset extent cells w j) (offset+j+1)
      (some ((w.map M.bitSym).getD j M.blank,true)) = copiedTape M base offset extent cells w (j+1) := by
  funext p
  by_cases he : p=offset+j+1
  · subst p
    simp [copiedTape,show ¬offset+j+1<offset by omega,show offset+j+1≠offset by omega,
      show offset+j+1-offset-1=j by omega]
  · rw [Function.update_of_ne he]
    by_cases hp : p<offset
    · simp [copiedTape,hp]
    · by_cases hm : p=offset
      · simp [copiedTape,hm]
      · by_cases hj : p<offset+j+1
        · simp [copiedTape,hp,hm,hj,show p<offset+(j+1)+1 by omega]
        · simp [copiedTape,hp,hm,hj,show ¬p<offset+(j+1)+1 by omega]

private theorem copied_zero (M : MultitapeTM) (base : ℕ → Sym M) (offset extent : ℕ)
    (cells : ℕ → M.Sym) (marker : cells 0=M.startSym) (w : List Bool) :
    copiedTape M base offset extent cells w 0 = oldTape M base offset extent cells := by
  funext p
  by_cases hp : p<offset
  · simp [copiedTape,oldTape,hp]
  · by_cases hm : p=offset
    · subst p
      simp [copiedTape,oldTape,marker]
    · simp only [copiedTape,if_neg hp,if_neg hm,if_neg (by omega : ¬p<offset+0+1)]

private theorem copied_complete (M : MultitapeTM) (base : ℕ → Sym M) (offset extent : ℕ)
    (cells : ℕ → M.Sym) (w : List Bool) :
    copiedTape M base offset extent cells w w.length=clearedTape M base offset extent cells w 0 := by
  funext p
  simp only [copiedTape,clearedTape,Nat.add_zero]
  split_ifs <;> rfl

private theorem tail_read (M : MultitapeTM) (base : ℕ → Sym M) (offset extent : ℕ)
    (cells : ℕ → M.Sym) (w : List Bool) (d : ℕ) :
    clearedTape M base offset extent cells w d (offset+w.length+d+1)=
      some (cells (w.length+d+1),decide (w.length+d+1≤extent)) := by
  simp only [clearedTape,if_neg (by omega : ¬offset+w.length+d+1<offset),
    if_neg (by omega : offset+w.length+d+1≠offset),
    if_neg (by omega : ¬offset+w.length+d+1<offset+w.length+1),
    if_neg (by omega : ¬offset+w.length+d+1<offset+w.length+d+1),oldTape,
    show offset+w.length+d+1-offset=w.length+d+1 by omega]

private theorem tail_erase (M : MultitapeTM) (base : ℕ → Sym M) (offset extent : ℕ)
    (cells : ℕ → M.Sym) (w : List Bool) (d : ℕ) :
    Function.update (clearedTape M base offset extent cells w d) (offset+w.length+d+1)
      (some (M.blank,false)) = clearedTape M base offset extent cells w (d+1) := by
  funext p
  by_cases he : p=offset+w.length+d+1
  · subst p
    simp [clearedTape,show ¬offset+w.length+d+1<offset by omega,
      show offset+w.length+d+1≠offset by omega,show ¬offset+w.length+d+1<offset+w.length+1 by omega]
  · rw [Function.update_of_ne he]
    by_cases hp : p<offset
    · simp [clearedTape,hp]
    · by_cases hm : p=offset
      · simp [clearedTape,hm]
      · by_cases hw : p<offset+w.length+1
        · simp [clearedTape,hp,hm,hw]
        · by_cases hd : p<offset+w.length+d+1
          · simp [clearedTape,hp,hm,hw,hd,show p<offset+w.length+(d+1)+1 by omega]
          · simp [clearedTape,hp,hm,hw,hd,show ¬p<offset+w.length+(d+1)+1 by omega]

private theorem marked_payload (M : MultitapeTM) (base : ℕ → Sym M) (offset : ℕ) (w : List Bool) (p : ℕ) :
    TrackedBankPreparation.bankTape M base offset (w.map M.bitSym) (offset+p+1)=
      some ((w.map M.bitSym).getD p M.blank,decide (p<w.length)) := by
  simp only [TrackedBankPreparation.bankTape,if_neg (by omega : ¬offset+p+1<offset),
    show offset+p+1-offset=p+1 by omega,MultitapeTM.tapeOf,List.length_map,
    show p+1≤w.length ↔ p<w.length by omega]

private theorem cleared_payload (M : MultitapeTM) (base : ℕ → Sym M) (offset extent : ℕ)
    (cells : ℕ → M.Sym) (w : List Bool) (d p : ℕ) :
    clearedTape M base offset extent cells w d (offset+p+1)=
      if p<w.length then some ((w.map M.bitSym).getD p M.blank,true)
      else if p<w.length+d then some (M.blank,false)
      else some (cells (p+1),decide (p+1≤extent)) := by
  simp only [clearedTape,if_neg (by omega : ¬offset+p+1<offset),
    if_neg (by omega : offset+p+1≠offset),show offset+p+1-offset-1=p by omega,
    show offset+p+1<offset+w.length+1 ↔ p<w.length by omega,
    show offset+p+1<offset+w.length+d+1 ↔ p<w.length+d by omega,oldTape,
    show offset+p+1-offset=p+1 by omega,Nat.add_sub_cancel]

private theorem cleared_complete (M : MultitapeTM) (base : ℕ → Sym M) (offset extent : ℕ)
    (cells : ℕ → M.Sym) (tail : ∀ p, extent<p → cells p=M.blank) (w : List Bool) :
    clearedTape M base offset extent cells w (max w.length extent-w.length)=
      TrackedBankPreparation.bankTape M base offset (w.map M.bitSym) := by
  funext p
  by_cases hp : p<offset
  · simp [clearedTape,TrackedBankPreparation.bankTape,hp]
  · by_cases hm : p=offset
    · subst p
      simp [clearedTape,TrackedBankPreparation.bankTape,MultitapeTM.tapeOf]
    · have he : p=offset+(p-offset-1)+1 := by omega
      rw [he,cleared_payload,marked_payload]
      by_cases hw : p-offset-1<w.length
      · simp only [hw,if_true,decide_true]
      · rw [if_neg hw,List.getD_eq_default _ _ (by simp only [List.length_map]; omega)]
        by_cases hd : p-offset-1<w.length+(max w.length extent-w.length)
        · simp only [if_pos hd,hw,decide_false]
        · rw [if_neg hd,tail _ (by omega)]
          have hf : ¬p-offset-1+1≤extent := by omega
          simp only [hw,hf,decide_false]

end IntMul.TrackedParentOutputBridge



namespace IntMul.TrackedParentOutputBridge

open IntMul.TrackedBankedSimulation (Sym)

private theorem buffer_ne_target (M : MultitapeTM) : bufferTape M ≠ targetTape M := by
  intro h
  have h := congrArg Fin.val h
  simp only [bufferTape,targetTape,BankedSimulation.workTape,MultitapeTM.outTape] at h
  omega

private theorem work_ne_buffer (M : MultitapeTM) (j : Fin M.k) :
    BankedSimulation.workTape M j ≠ bufferTape M := by
  intro h
  have h := congrArg Fin.val h
  simp only [bufferTape,BankedSimulation.workTape] at h
  omega

private theorem initial_buffer (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    initialCells M base sigma offset extent c w (bufferTape M) =
      TrackedOutputReturn.bufferTape M (base.cells (bufferTape M)) sigma w := by
  funext p
  simp [initialCells,TrackedBankedSimulation.embed,parentBase,bufferTape]

private theorem initial_work (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (j : Fin M.k) (p : ℕ) :
    initialCells M base sigma offset extent c w (BankedSimulation.workTape M j) (offset j + p) =
      some (c.cells j p,decide (p ≤ extent j)) := by
  simp only [initialCells,TrackedBankedSimulation.embed,BankedSimulation.workTape]
  rw [dif_pos (by omega)]
  have hi : BankedSimulation.innerTape M ⟨j.val+2,by omega⟩ (by change 2 ≤ j.val+2; omega) = j := by
    apply Fin.ext
    simp [BankedSimulation.innerTape]
  simp only [hi,if_neg (by omega : ¬offset j+p < offset j),show offset j+p-offset j=p by omega]
private theorem initial_target (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    initialCells M base sigma offset extent c w (targetTape M) =
      oldTape M (base.cells (targetTape M)) (offset M.outTape) (extent M.outTape) (c.cells M.outTape) := by
  funext p
  simp only [initialCells,TrackedBankedSimulation.embed,targetTape,BankedSimulation.workTape]
  rw [dif_pos (by omega)]
  have hi : BankedSimulation.innerTape M ⟨M.outTape.val+2,by omega⟩
      (by change 2≤M.outTape.val+2; omega)=M.outTape := by
    apply Fin.ext
    simp [BankedSimulation.innerTape]
  simp only [hi,oldTape]
  by_cases hp : p<offset M.outTape
  · simp only [if_pos hp,parentBase]
    split_ifs with h
    · have h := congrArg Fin.val h
      simp only [bufferTape] at h
      omega
    · rfl
  · simp only [if_neg hp]

private theorem initial_target_head (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    initialHeads M base sigma offset extent c w (targetTape M)=offset M.outTape := by
  simp only [initialHeads,eq_self,if_true]

private theorem before_buffer_scan (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (r : ℕ) :
    (beforeFrame M base sigma offset extent c w r).cells (bufferTape M)
      ((beforeFrame M base sigma offset extent c w r).head (bufferTape M)) =
      TrackedOutputReturn.bufferTape M (base.cells (bufferTape M)) sigma w (sigma+(w.length+1-r)) := by
  simp only [beforeFrame,eq_self,if_true,initial_buffer]

private theorem before_target_scan (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (marker : c.cells M.outTape 0=M.startSym) (r : ℕ) :
    (beforeFrame M base sigma offset extent c w r).cells (targetTape M)
      ((beforeFrame M base sigma offset extent c w r).head (targetTape M)) = some (M.startSym,true) := by
  simp only [beforeFrame,if_neg (buffer_ne_target M).symm,initial_target_head,initial_target]
  have h := old_payload M (base.cells (targetTape M)) (offset M.outTape) (extent M.outTape) (c.cells M.outTape) 0
  simpa only [Nat.add_zero,marker,Nat.zero_le,decide_true] using h

private theorem before_buffer_marker (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (r : ℕ) :
    (beforeFrame M base sigma offset extent c w r).cells (bufferTape M)
      ((beforeFrame M base sigma offset extent c w r).head (bufferTape M)) = some (M.startSym,true) ↔ w.length+1≤r := by
  rw [before_buffer_scan,buffer_marker]
  omega

private theorem before_markers (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (marker : c.cells M.outTape 0=M.startSym) (r : ℕ) :
    ((beforeFrame M base sigma offset extent c w r).cells (bufferTape M)
        ((beforeFrame M base sigma offset extent c w r).head (bufferTape M)) = some (M.startSym,true) ∧
      (beforeFrame M base sigma offset extent c w r).cells (targetTape M)
        ((beforeFrame M base sigma offset extent c w r).head (targetTape M)) = some (M.startSym,true)) ↔ w.length+1≤r := by
  rw [before_buffer_marker,before_target_scan M base sigma offset extent c w marker]
  simp only [and_true]

private theorem before_buffer_not_global (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (r : ℕ) :
    (beforeFrame M base sigma offset extent c w r).cells (bufferTape M)
      ((beforeFrame M base sigma offset extent c w r).head (bufferTape M)) ≠ none := by
  rw [before_buffer_scan]
  simp only [TrackedOutputReturn.bufferTape,if_neg (by omega : ¬sigma+(w.length+1-r)<sigma)]
  split_ifs <;> exact Option.some_ne_none _

private theorem copy_buffer_scan (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (j : ℕ) :
    (copyFrame M base sigma offset extent c w j).cells (bufferTape M)
      ((copyFrame M base sigma offset extent c w j).head (bufferTape M)) =
      some ((w.map M.bitSym).getD j M.blank,decide (j<w.length)) := by
  simp only [copyFrame,if_neg (buffer_ne_target M),eq_self,if_true,initial_buffer,buffer_payload]

private theorem copy_target_not_global (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (j : ℕ) :
    (copyFrame M base sigma offset extent c w j).cells (targetTape M)
      ((copyFrame M base sigma offset extent c w j).head (targetTape M)) ≠ none := by
  simp only [copyFrame,eq_self,if_true,if_neg (buffer_ne_target M).symm,copiedTape,
    if_neg (by omega : ¬offset M.outTape+j+1<offset M.outTape),
    if_neg (by omega : offset M.outTape+j+1≠offset M.outTape),
    if_neg (by omega : ¬offset M.outTape+j+1<offset M.outTape+j+1)]
  simp [oldTape,show ¬offset M.outTape+j+1<offset M.outTape by omega]

private theorem clear_target_scan (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (d : ℕ) :
    (clearFrame M base sigma offset extent c w d).cells (targetTape M)
      ((clearFrame M base sigma offset extent c w d).head (targetTape M)) =
      some (c.cells M.outTape (w.length+d+1),decide (w.length+d+1≤extent M.outTape)) := by
  simp only [clearFrame,eq_self,if_true,if_neg (buffer_ne_target M).symm,tail_read]

private theorem rewind_target_scan (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (r : ℕ) :
    (rewindFrame M base sigma offset extent c w r).cells (targetTape M)
      ((rewindFrame M base sigma offset extent c w r).head (targetTape M)) =
      some (M.tapeOf (w.map M.bitSym) (max w.length (extent M.outTape)-r),
        decide (max w.length (extent M.outTape)-r≤w.length)) := by
  simp only [rewindFrame,eq_self,if_true,if_neg (buffer_ne_target M).symm,TrackedBankPreparation.bankTape,
    if_neg (by omega : ¬offset M.outTape+(max w.length (extent M.outTape)-r)<offset M.outTape),
    show offset M.outTape+(max w.length (extent M.outTape)-r)-offset M.outTape=max w.length (extent M.outTape)-r by omega,
    List.length_map]

private theorem rewind_target_marker (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (r : ℕ) :
    (rewindFrame M base sigma offset extent c w r).cells (targetTape M)
      ((rewindFrame M base sigma offset extent c w r).head (targetTape M)) = some (M.startSym,true) ↔
      max w.length (extent M.outTape)≤r := by
  rw [rewind_target_scan]
  constructor
  · intro h
    have hs := congrArg Prod.fst (Option.some.inj h)
    have hp := (bit_tape_marker M w _).mp hs
    omega
  · intro h
    rw [Nat.sub_eq_zero_of_le h]
    simp [MultitapeTM.tapeOf]

end IntMul.TrackedParentOutputBridge



namespace IntMul.TrackedParentOutputBridge

open IntMul.TrackedBankedSimulation (Sym)

attribute [local instance] Classical.propDecidable

private theorem transition_protect_stay (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .stay = (a,.stay) := by cases a <;> rfl

private theorem transition_protect_right (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .right = (a,.right) := by cases a <;> rfl

private theorem transition_protect_present (M : MultitapeTM) (a : Sym M) (move : Move) (h : a ≠ none) :
    TrackedBankCleanup.protect M a a move = (a,move) := by
  cases ha : a with
  | none => exact False.elim (h ha)
  | some s => rfl

private theorem transition_protect_write (M : MultitapeTM) (a : Sym M) (s : M.Sym × Bool)
    (move : Move) (h : a ≠ none) :
    TrackedBankCleanup.protect M a (some s) move = (some s,move) := by
  cases ha : a with
  | none => exact False.elim (h ha)
  | some old => rfl

private theorem before_dispatch (M : MultitapeTM) (a : Fin (M.k+2) → Sym M)
    (done : a (bufferTape M) = some (M.startSym,true) ∧ a (targetTape M) = some (M.startSym,true)) :
    transition M .before a = (.copy,fun i => (a i,
      if i=bufferTape M ∨ i=targetTape M then .right else .stay)) := by
  classical
  simp only [transition,rawTransition,if_pos done]
  congr 1
  funext i
  split
  · exact transition_protect_right M _
  · exact transition_protect_stay M _

private theorem copy_transition (M : MultitapeTM) (a : Fin (M.k+2) → Sym M)
    (s : M.Sym) (b : Bool) (source : a (bufferTape M) = some (s,b))
    (letter : s=M.zero ∨ s=M.one) (target : a (targetTape M) ≠ none) :
    transition M .copy a = (.copy,fun i =>
      (if i=targetTape M then some (s,true) else a i,
        if i=bufferTape M ∨ i=targetTape M then .right else .stay)) := by
  classical
  have h : TrackedBankedSimulation.decode M (a (bufferTape M))=M.zero ∨
      TrackedBankedSimulation.decode M (a (bufferTape M))=M.one := by
    simpa only [source,TrackedBankedSimulation.decode] using letter
  dsimp only [transition,rawTransition]
  rw [if_pos h]
  simp only [source,TrackedBankedSimulation.decode]
  congr 1
  funext i
  by_cases hi : i=targetTape M
  · subst i
    simp only [eq_self,if_true,true_or]
    exact transition_protect_write M _ _ _ target
  · simp only [if_neg hi]
    split
    · exact transition_protect_right M _
    · exact transition_protect_stay M _

private theorem copy_dispatch (M : MultitapeTM) (a : Fin (M.k+2) → Sym M)
    (source : TrackedBankedSimulation.decode M (a (bufferTape M))=M.blank) :
    transition M .copy a = (.clearTail,fun i => (a i,.stay)) := by
  classical
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true] at hd
  have hn : ¬(TrackedBankedSimulation.decode M (a (bufferTape M))=M.zero ∨
      TrackedBankedSimulation.decode M (a (bufferTape M))=M.one) := by
    rw [source]
    tauto
  simp only [transition,rawTransition,if_neg hn,transition_protect_stay]

private theorem clear_transition (M : MultitapeTM) (a : Fin (M.k+2) → Sym M)
    (flag : TrackedBankCleanup.visited M (a (targetTape M))=true) :
    transition M .clearTail a = (.clearTail,fun i =>
      (if i=targetTape M then some (M.blank,false) else a i,
        if i=targetTape M then .right else .stay)) := by
  classical
  have hb : a (targetTape M) ≠ none := by
    intro h
    simp only [h,TrackedBankCleanup.visited] at flag
    cases flag
  simp only [transition,rawTransition,if_pos flag]
  congr 1
  funext i
  by_cases hi : i=targetTape M
  · subst i
    simp only [eq_self,if_true]
    exact transition_protect_write M _ _ _ hb
  · simp only [if_neg hi]
    exact transition_protect_stay M _

private theorem before_transition (M : MultitapeTM) (a : Fin (M.k+2) → Sym M)
    (not_done : ¬(a (bufferTape M)=some (M.startSym,true) ∧ a (targetTape M)=some (M.startSym,true)))
    (buffer : a (bufferTape M)≠none) :
    transition M .before a=(.before,fun i => (a i,
      if i=bufferTape M ∧ a i≠some (M.startSym,true) then .left else .stay)) := by
  classical
  simp only [transition,rawTransition,if_neg not_done]
  congr 1
  funext i
  by_cases hi : i=bufferTape M ∧ a i≠some (M.startSym,true)
  · rw [if_pos hi]
    exact transition_protect_present M _ _ (by simpa only [hi.1] using buffer)
  · rw [if_neg hi]
    exact transition_protect_stay M _

private theorem clear_dispatch (M : MultitapeTM) (a : Fin (M.k+2) → Sym M)
    (flag : TrackedBankCleanup.visited M (a (targetTape M))=false)
    (target : a (targetTape M)≠none) :
    transition M .clearTail a=(.rewind,fun i => (a i,if i=targetTape M then .left else .stay)) := by
  classical
  have hn : ¬TrackedBankCleanup.visited M (a (targetTape M))=true := by rw [flag]; decide
  simp only [transition,rawTransition,if_neg hn]
  congr 1
  funext i
  by_cases hi : i=targetTape M
  · rw [if_pos hi]
    exact transition_protect_present M _ _ (by simpa only [hi] using target)
  · rw [if_neg hi]
    exact transition_protect_stay M _

private theorem rewind_transition (M : MultitapeTM) (a : Fin (M.k+2) → Sym M)
    (not_done : a (targetTape M)≠some (M.startSym,true)) (target : a (targetTape M)≠none) :
    transition M .rewind a=(.rewind,fun i => (a i,if i=targetTape M then .left else .stay)) := by
  classical
  simp only [transition,rawTransition,if_neg not_done]
  congr 1
  funext i
  by_cases hi : i=targetTape M
  · rw [if_pos hi]
    exact transition_protect_present M _ _ (by simpa only [hi] using target)
  · rw [if_neg hi]
    exact transition_protect_stay M _

private theorem rewind_dispatch (M : MultitapeTM) (a : Fin (M.k+2) → Sym M)
    (done : a (targetTape M)=some (M.startSym,true)) :
    transition M .rewind a=(.halt,fun i => (a i,.stay)) := by
  simp only [transition,rawTransition,if_pos done,transition_protect_stay]

end IntMul.TrackedParentOutputBridge



namespace IntMul.TrackedParentOutputBridge

private theorem before_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem before_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (marker : c.cells M.outTape 0=M.startSym) (r : ℕ) (hr : r<w.length+1) :
    (machine M).step (beforeFrame M base sigma offset extent c w r) =
      beforeFrame M base sigma offset extent c w (r+1) := by
  classical
  let a := fun i => (beforeFrame M base sigma offset extent c w r).cells i
    ((beforeFrame M base sigma offset extent c w r).head i)
  have hn : ¬(a (bufferTape M)=some (M.startSym,true) ∧ a (targetTape M)=some (M.startSym,true)) := by
    intro h
    have h := (before_markers M base sigma offset extent c w marker r).mp h
    omega
  have ht := before_transition M a hn (before_buffer_not_global M base sigma offset extent c w r)
  dsimp only [a] at ht
  change transition M (beforeFrame M base sigma offset extent c w r).state _ = _ at ht
  apply before_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=bufferTape M
    · subst i
      have hm := before_buffer_marker M base sigma offset extent c w r
      rw [if_pos ⟨rfl,by intro h; have h := hm.mp h; omega⟩]
      simp only [beforeFrame,eq_self,if_true]
      omega
    · rw [if_neg (by intro h; exact hi h.1)]
      simp only [beforeFrame,if_neg hi]

private theorem before_run (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (marker : c.cells M.outTape 0=M.startSym) (r : ℕ) (hr : r≤w.length+1) :
    (machine M).step^[r] (beforeFrame M base sigma offset extent c w 0) =
      beforeFrame M base sigma offset extent c w r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply',ih (by omega),before_step M base sigma offset extent c w marker r (by omega)]

private theorem before_end (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (marker : c.cells M.outTape 0=M.startSym) :
    (machine M).step (beforeFrame M base sigma offset extent c w (w.length+1)) =
      copyFrame M base sigma offset extent c w 0 := by
  have ht := before_dispatch M
    (fun i => (beforeFrame M base sigma offset extent c w (w.length+1)).cells i
      ((beforeFrame M base sigma offset extent c w (w.length+1)).head i))
    ((before_markers M base sigma offset extent c w marker _).mpr le_rfl)
  change transition M (beforeFrame M base sigma offset extent c w (w.length+1)).state _ = _ at ht
  apply before_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    by_cases hi : i=targetTape M
    · subst i
      simp only [beforeFrame,copyFrame,eq_self,if_true,initial_target,copied_zero M _ _ _ _ marker]
    · simp only [beforeFrame,copyFrame,if_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=bufferTape M
    · subst i
      simp only [eq_self,true_or,if_true,beforeFrame,copyFrame,Nat.sub_self,Nat.add_zero]
    · by_cases hp : i=targetTape M
      · subst i
        simp only [eq_self,or_true,if_true,beforeFrame,copyFrame,if_neg hi,initial_target_head,Nat.add_zero]
      · simp only [if_neg (not_or.mpr ⟨hi,hp⟩),beforeFrame,copyFrame,if_neg hi,if_neg hp]

end IntMul.TrackedParentOutputBridge



namespace IntMul.TrackedParentOutputBridge


private theorem copy_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem copy_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (j : ℕ) (hj : j < w.length) :
    (machine M).step (copyFrame M base sigma offset extent c w j) =
      copyFrame M base sigma offset extent c w (j+1) := by
  classical
  let a := fun i => (copyFrame M base sigma offset extent c w j).cells i
    ((copyFrame M base sigma offset extent c w j).head i)
  have ht := copy_transition M a ((w.map M.bitSym).getD j M.blank)
    (decide (j<w.length))
    (copy_buffer_scan M base sigma offset extent c w j)
    (bit_word_letter M w j hj) (copy_target_not_global M base sigma offset extent c w j)
  dsimp only [a] at ht
  change transition M (copyFrame M base sigma offset extent c w j).state _ = _ at ht
  apply copy_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=targetTape M
    · subst i
      simp only [eq_self,if_true,copyFrame]
      exact copy_write M _ (offset M.outTape) (extent M.outTape) (c.cells M.outTape) w j
    · rw [if_neg hi,Function.update_eq_self]
      simp only [copyFrame,if_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=bufferTape M
    · subst i
      simp only [eq_self,true_or,if_true,copyFrame]
      omega
    · by_cases hp : i=targetTape M
      · subst i
        simp only [eq_self,or_true,if_true,copyFrame,if_neg hi]
        omega
      · simp only [if_neg (not_or.mpr ⟨hi,hp⟩),copyFrame,if_neg hi,if_neg hp]

private theorem copy_run (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (j : ℕ) (hj : j ≤ w.length) :
    (machine M).step^[j] (copyFrame M base sigma offset extent c w 0) =
      copyFrame M base sigma offset extent c w j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply',ih (by omega),copy_step M base sigma offset extent c w j (by omega)]

private theorem copy_end (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    (machine M).step (copyFrame M base sigma offset extent c w w.length) =
      clearFrame M base sigma offset extent c w 0 := by
  have hs : TrackedBankedSimulation.decode M
      ((copyFrame M base sigma offset extent c w w.length).cells (bufferTape M)
        ((copyFrame M base sigma offset extent c w w.length).head (bufferTape M))) = M.blank := by
    rw [copy_buffer_scan M base sigma offset extent c w]
    change (w.map M.bitSym).getD w.length M.blank=M.blank
    apply List.getD_eq_default
    simp only [List.length_map]
    exact le_rfl
  have ht := copy_dispatch M
    (fun i => (copyFrame M base sigma offset extent c w w.length).cells i
      ((copyFrame M base sigma offset extent c w w.length).head i)) hs
  change transition M (copyFrame M base sigma offset extent c w w.length).state _ = _ at ht
  apply copy_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    simp only [copyFrame,clearFrame,copied_complete]
  · simp only [MultitapeTM.step,ht]
    funext i
    simp only [copyFrame,clearFrame,Nat.add_zero]
private theorem clear_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (d : ℕ)
    (hd : d< max w.length (extent M.outTape)-w.length) :
    (machine M).step (clearFrame M base sigma offset extent c w d) =
      clearFrame M base sigma offset extent c w (d+1) := by
  classical
  have hv : w.length+d+1≤extent M.outTape := by omega
  have hf : TrackedBankCleanup.visited M
      ((clearFrame M base sigma offset extent c w d).cells (targetTape M)
        ((clearFrame M base sigma offset extent c w d).head (targetTape M)))=true := by
    rw [clear_target_scan]
    simp only [TrackedBankCleanup.visited,decide_eq_true hv]
  have ht := clear_transition M
    (fun i => (clearFrame M base sigma offset extent c w d).cells i
      ((clearFrame M base sigma offset extent c w d).head i)) hf
  change transition M (clearFrame M base sigma offset extent c w d).state _ = _ at ht
  apply copy_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=targetTape M
    · subst i
      simp only [eq_self,if_true,clearFrame,if_neg (buffer_ne_target M).symm]
      exact tail_erase M _ (offset M.outTape) (extent M.outTape) (c.cells M.outTape) w d
    · rw [if_neg hi,Function.update_eq_self]
      simp only [clearFrame,if_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=targetTape M
    · subst i
      simp only [eq_self,if_true,clearFrame,if_neg (buffer_ne_target M).symm]
      omega
    · simp only [if_neg hi,clearFrame,if_neg hi]

private theorem clear_run (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (d : ℕ)
    (hd : d≤ max w.length (extent M.outTape)-w.length) :
    (machine M).step^[d] (clearFrame M base sigma offset extent c w 0) =
      clearFrame M base sigma offset extent c w d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply',ih (by omega),clear_step M base sigma offset extent c w d (by omega)]

private theorem clear_end (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (tail : ∀ p, extent M.outTape<p → c.cells M.outTape p=M.blank) :
    (machine M).step (clearFrame M base sigma offset extent c w (max w.length (extent M.outTape)-w.length)) =
      rewindFrame M base sigma offset extent c w 0 := by
  classical
  let D := max w.length (extent M.outTape)-w.length
  change (machine M).step (clearFrame M base sigma offset extent c w D) = _
  have hlen : w.length+D=max w.length (extent M.outTape) := by dsimp [D]; omega
  have hv : ¬w.length+D+1≤extent M.outTape := by omega
  have hf : TrackedBankCleanup.visited M
      ((clearFrame M base sigma offset extent c w D).cells (targetTape M)
        ((clearFrame M base sigma offset extent c w D).head (targetTape M)))=false := by
    rw [clear_target_scan]
    simp only [TrackedBankCleanup.visited,decide_eq_false hv]
  have hb : (clearFrame M base sigma offset extent c w D).cells (targetTape M)
      ((clearFrame M base sigma offset extent c w D).head (targetTape M))≠none := by
    rw [clear_target_scan]
    exact Option.some_ne_none _
  have ht := clear_dispatch M
    (fun i => (clearFrame M base sigma offset extent c w D).cells i
      ((clearFrame M base sigma offset extent c w D).head i)) hf hb
  change transition M (clearFrame M base sigma offset extent c w D).state _ = _ at ht
  apply copy_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    simp only [clearFrame,rewindFrame]
    by_cases hi : i=targetTape M
    · simp only [if_pos hi]
      exact cleared_complete M _ (offset M.outTape) (extent M.outTape) (c.cells M.outTape) tail w
    · simp only [if_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=targetTape M
    · subst i
      simp only [eq_self,if_true,clearFrame,rewindFrame,if_neg (buffer_ne_target M).symm,Nat.sub_zero]
      omega
    · simp only [if_neg hi,clearFrame,rewindFrame,if_neg hi]

end IntMul.TrackedParentOutputBridge



namespace IntMul.TrackedParentOutputBridge

private theorem rewind_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem rewind_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (r : ℕ) (hr : r< max w.length (extent M.outTape)) :
    (machine M).step (rewindFrame M base sigma offset extent c w r) =
      rewindFrame M base sigma offset extent c w (r+1) := by
  classical
  let a := fun i => (rewindFrame M base sigma offset extent c w r).cells i
    ((rewindFrame M base sigma offset extent c w r).head i)
  have hn : a (targetTape M)≠some (M.startSym,true) := by
    intro h
    have h := (rewind_target_marker M base sigma offset extent c w r).mp h
    omega
  have hp : a (targetTape M)≠none := by
    dsimp only [a]
    rw [rewind_target_scan]
    exact Option.some_ne_none _
  have ht := rewind_transition M a hn hp
  dsimp only [a] at ht
  change transition M (rewindFrame M base sigma offset extent c w r).state _ = _ at ht
  apply rewind_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=targetTape M
    · subst i
      simp only [eq_self,if_true,rewindFrame,if_neg (buffer_ne_target M).symm]
      omega
    · simp only [if_neg hi,rewindFrame,if_neg hi]

private theorem rewind_run (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (r : ℕ) (hr : r≤ max w.length (extent M.outTape)) :
    (machine M).step^[r] (rewindFrame M base sigma offset extent c w 0) =
      rewindFrame M base sigma offset extent c w r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply',ih (by omega),rewind_step M base sigma offset extent c w r (by omega)]

private theorem rewind_end (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    (machine M).step (rewindFrame M base sigma offset extent c w (max w.length (extent M.outTape))) =
      finalFrame M base sigma offset extent c w := by
  have ht := rewind_dispatch M
    (fun i => (rewindFrame M base sigma offset extent c w (max w.length (extent M.outTape))).cells i
      ((rewindFrame M base sigma offset extent c w (max w.length (extent M.outTape))).head i))
    ((rewind_target_marker M base sigma offset extent c w _).mpr le_rfl)
  change transition M (rewindFrame M base sigma offset extent c w (max w.length (extent M.outTape))).state _ = _ at ht
  apply rewind_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    simp only [rewindFrame,finalFrame,Nat.sub_self,Nat.add_zero]

end IntMul.TrackedParentOutputBridge



namespace IntMul.TrackedParentOutputBridge

private theorem run_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (marker : c.cells M.outTape 0=M.startSym)
    (tail : ∀ p, extent M.outTape<p → c.cells M.outTape p=M.blank) :
    (machine M).step^[w.length+2*max w.length (extent M.outTape)+5]
      (initialFrame M base sigma offset extent c w) = finalFrame M base sigma offset extent c w := by
  let H := max w.length (extent M.outTape)
  let D := H-w.length
  have hlen : w.length+D=H := by dsimp [D,H]; omega
  have hbefore : (machine M).step^[w.length+2] (initialFrame M base sigma offset extent c w) =
      copyFrame M base sigma offset extent c w 0 := by
    change (machine M).step^[(w.length+1)+1] (beforeFrame M base sigma offset extent c w 0) = _
    rw [Function.iterate_succ_apply',before_run M base sigma offset extent c w marker _ le_rfl,
      before_end M base sigma offset extent c w marker]
  have hcopy : (machine M).step^[w.length+1] (copyFrame M base sigma offset extent c w 0) =
      clearFrame M base sigma offset extent c w 0 := by
    rw [Function.iterate_succ_apply',copy_run M base sigma offset extent c w _ le_rfl,
      copy_end M base sigma offset extent c w]
  have hclear : (machine M).step^[D+1] (clearFrame M base sigma offset extent c w 0) =
      rewindFrame M base sigma offset extent c w 0 := by
    rw [Function.iterate_succ_apply',clear_run M base sigma offset extent c w D le_rfl,
      clear_end M base sigma offset extent c w tail]
  have hrewind : (machine M).step^[H+1] (rewindFrame M base sigma offset extent c w 0) =
      finalFrame M base sigma offset extent c w := by
    rw [Function.iterate_succ_apply',rewind_run M base sigma offset extent c w H le_rfl,
      rewind_end M base sigma offset extent c w]
  have hcopybefore : (machine M).step^[(w.length+1)+(w.length+2)] (initialFrame M base sigma offset extent c w) =
      clearFrame M base sigma offset extent c w 0 := by
    rw [Function.iterate_add_apply,hbefore,hcopy]
  have hclearcopy : (machine M).step^[(D+1)+((w.length+1)+(w.length+2))] (initialFrame M base sigma offset extent c w) =
      rewindFrame M base sigma offset extent c w 0 := by
    rw [Function.iterate_add_apply,hcopybefore,hclear]
  change (machine M).step^[w.length+2*H+5] (initialFrame M base sigma offset extent c w) = _
  rw [show w.length+2*H+5=(H+1)+((D+1)+((w.length+1)+(w.length+2))) by omega,
    Function.iterate_add_apply,hclearcopy,hrewind]

/-- Place a physical child return word into a parent output bank, erase all
remaining old visited cells, retain the parent marker and restore its head.
Every other tape and head, including the caller buffer, stays exact. -/
private theorem output_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (marker : c.cells M.outTape 0=M.startSym)
    (tail : ∀ p, extent M.outTape<p → c.cells M.outTape p=M.blank) :
    (machine M).step^[w.length+2*max w.length (extent M.outTape)+5]
      (initialFrame M base sigma offset extent c w) = finalFrame M base sigma offset extent c w ∧
    (finalFrame M base sigma offset extent c w).state = (machine M).qHalt ∧
    (finalFrame M base sigma offset extent c w).cells (targetTape M) =
      TrackedBankPreparation.bankTape M (base.cells (targetTape M)) (offset M.outTape) (w.map M.bitSym) ∧
    (∀ p, (finalFrame M base sigma offset extent c w).cells (targetTape M) (offset M.outTape+p)=
      some (M.tapeOf (w.map M.bitSym) p,decide (p≤w.length))) ∧
    (finalFrame M base sigma offset extent c w).head (targetTape M) = offset M.outTape ∧
    (finalFrame M base sigma offset extent c w).cells (bufferTape M) =
      TrackedOutputReturn.bufferTape M (base.cells (bufferTape M)) sigma w ∧
    (finalFrame M base sigma offset extent c w).head (bufferTape M) = sigma+w.length+1 ∧
    (∀ i, i≠targetTape M → (finalFrame M base sigma offset extent c w).cells i =
      (initialFrame M base sigma offset extent c w).cells i) ∧
    (∀ i, i≠targetTape M → (finalFrame M base sigma offset extent c w).head i =
      (initialFrame M base sigma offset extent c w).head i) := by
  refine ⟨run_correct M base sigma offset extent c w marker tail,rfl,?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [finalFrame,eq_self,if_true]
  · intro p
    simp only [finalFrame,eq_self,if_true,TrackedBankPreparation.bankTape,
      if_neg (by omega : ¬offset M.outTape+p<offset M.outTape),
      show offset M.outTape+p-offset M.outTape=p by omega,List.length_map]
  · simp only [finalFrame,if_neg (buffer_ne_target M).symm,eq_self,if_true]
  · simp only [finalFrame,if_neg (buffer_ne_target M),initial_buffer]
  · simp only [finalFrame,eq_self,if_true]
  · intro i hi
    simp only [finalFrame,if_neg hi,initialFrame,beforeFrame]
  · intro i hi
    simp only [finalFrame,if_neg hi,initialFrame,beforeFrame,Nat.sub_zero,Nat.add_assoc]

end IntMul.TrackedParentOutputBridge


open IntMul IntMul.TrackedParentOutputBridge

theorem solution (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (marker : c.cells M.outTape 0=M.startSym)
    (tail : ∀ p, extent M.outTape<p → c.cells M.outTape p=M.blank) :
    (machine M).step^[w.length+2*max w.length (extent M.outTape)+5]
      (initialFrame M base sigma offset extent c w) = finalFrame M base sigma offset extent c w ∧
    (finalFrame M base sigma offset extent c w).state = (machine M).qHalt ∧
    (finalFrame M base sigma offset extent c w).cells (targetTape M) =
      TrackedBankPreparation.bankTape M (base.cells (targetTape M)) (offset M.outTape) (w.map M.bitSym) ∧
    (∀ p, (finalFrame M base sigma offset extent c w).cells (targetTape M) (offset M.outTape+p)=
      some (M.tapeOf (w.map M.bitSym) p,decide (p≤w.length))) ∧
    (finalFrame M base sigma offset extent c w).head (targetTape M) = offset M.outTape ∧
    (finalFrame M base sigma offset extent c w).cells (bufferTape M) =
      TrackedOutputReturn.bufferTape M (base.cells (bufferTape M)) sigma w ∧
    (finalFrame M base sigma offset extent c w).head (bufferTape M) = sigma+w.length+1 ∧
    (∀ i, i≠targetTape M → (finalFrame M base sigma offset extent c w).cells i =
      (initialFrame M base sigma offset extent c w).cells i) ∧
    (∀ i, i≠targetTape M → (finalFrame M base sigma offset extent c w).head i =
      (initialFrame M base sigma offset extent c w).head i) :=
  IntMul.TrackedParentOutputBridge.output_correct M base sigma offset extent c w marker tail

#print axioms solution
