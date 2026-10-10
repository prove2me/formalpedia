-- Prove2me | solution 1 for IntMul.TrackedReturnReplacement.return_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T01:29:20.883907+00:00
-- url     : https://prove2.me/submissions/dbca8f1c-29e4-4217-9048-8fef5f1a6b8c

import Definitions.Def_IntMul_TrackedReturnReplacement
import Mathlib.Data.List.GetD
import Mathlib.Tactic


namespace IntMul.TrackedWordInputBridge

open IntMul.TrackedBankedSimulation (Sym)


private theorem word_tape_blank_ne_start (M : MultitapeTM) : M.blank ≠ M.startSym := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,and_true] at hd
  tauto

private theorem word_tape_letters_ne_start (M : MultitapeTM) :
    M.zero ≠ M.startSym ∧ M.one ≠ M.startSym ∧ M.sep ≠ M.startSym := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,and_true] at hd
  tauto

private theorem word_tape_word_letter (M : MultitapeTM) (w : ValidWord M) (a : M.Sym)
    (ha : a ∈ word M w) : a=M.zero ∨ a=M.one ∨ a=M.sep := w.property a ha

private theorem word_read (M : MultitapeTM) (w : ValidWord M) (j : ℕ) (hj : j < (word M w).length) :
    (word M w).getD j M.blank = M.zero ∨ (word M w).getD j M.blank = M.one ∨
      (word M w).getD j M.blank = M.sep := by
  rw [List.getD_eq_getElem _ _ hj]
  exact word_tape_word_letter M w _ (List.getElem_mem hj)

private theorem word_tape_getD_not_start (M : MultitapeTM) (w : List M.Sym)
    (h : ∀ a ∈ w, a ≠ M.startSym) (j : ℕ) : w.getD j M.blank ≠ M.startSym := by
  by_cases hj : j < w.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact h _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact word_tape_blank_ne_start M

private theorem packet_unique (M : MultitapeTM) (w : ValidWord M) (p : ℕ) :
    M.tapeOf (word M w) p = M.startSym ↔ p = 0 := by
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
      have h := word_tape_getD_not_start M (word M w) (by
        intro a ha
        rcases word_tape_word_letter M w a ha with h | h | h
        · rw [h]; exact (word_tape_letters_ne_start M).1
        · rw [h]; exact (word_tape_letters_ne_start M).2.1
        · rw [h]; exact (word_tape_letters_ne_start M).2.2) p
      change (word M w).getD p M.blank = M.startSym ↔ p + 1 = 0
      constructor
      · intro hs; exact False.elim (h hs)
      · intro hz; omega

private theorem old_buffer_marker (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (v : List Bool) (p : ℕ) :
    TrackedOutputReturn.bufferTape M base sigma v (sigma + p) = some (M.startSym,true) ↔ p = 0 := by
  cases p with
  | zero => simp [TrackedOutputReturn.bufferTape]
  | succ p =>
      have h := word_tape_getD_not_start M (v.map M.bitSym) (by
        intro a ha
        rcases List.mem_map.mp ha with ⟨b,_,rfl⟩
        cases b <;> simp only [MultitapeTM.bitSym,Bool.false_eq_true,if_false,if_true]
        · exact (word_tape_letters_ne_start M).1
        · exact (word_tape_letters_ne_start M).2.1) p
      have he : sigma + (p + 1) - sigma - 1 = p := by omega
      simp only [TrackedOutputReturn.bufferTape,if_neg (by omega : ¬sigma + (p + 1) < sigma),
        if_neg (by omega : sigma + (p + 1) ≠ sigma),he]
      constructor
      · intro hs
        have hf := congrArg Prod.fst (Option.some.inj hs)
        exact False.elim (h hf)
      · intro hz
        omega

private theorem copy_write (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ)
    (w : List M.Sym) (v : List Bool) (j : ℕ) :
    Function.update (copiedTape M base sigma w v j) (sigma + j + 1) (some (w.getD j M.blank,true)) =
      copiedTape M base sigma w v (j + 1) := by
  funext p
  by_cases he : p = sigma + j + 1
  · subst p
    simp [copiedTape,show ¬sigma + j + 1 < sigma by omega,show sigma + j + 1 ≠ sigma by omega,
      show sigma + j + 1 - sigma - 1 = j by omega]
  · rw [Function.update_of_ne he]
    by_cases hp : p < sigma
    · simp [copiedTape,hp]
    · by_cases hm : p = sigma
      · simp [copiedTape,hm]
      · by_cases hj : p < sigma + j + 1
        · simp [copiedTape,hp,hm,hj,show p < sigma + (j + 1) + 1 by omega]
        · simp [copiedTape,hp,hm,hj,show ¬p < sigma + (j + 1) + 1 by omega]

private theorem copied_zero (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List M.Sym) (v : List Bool) :
    copiedTape M base sigma w v 0 = TrackedOutputReturn.bufferTape M base sigma v := by
  funext p
  by_cases hp : p < sigma
  · simp [copiedTape,TrackedOutputReturn.bufferTape,hp]
  · by_cases hm : p = sigma
    · simp [copiedTape,TrackedOutputReturn.bufferTape,hm]
    · simp only [copiedTape,if_neg hp,if_neg hm,if_neg (by omega : ¬p < sigma + 0 + 1)]

private theorem copied_complete (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List M.Sym) (v : List Bool) :
    copiedTape M base sigma w v w.length = clearedTape M base sigma w v 0 := by
  funext p
  simp only [copiedTape,clearedTape,Nat.add_zero]
  split_ifs <;> rfl

private theorem tail_read (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ)
    (w : List M.Sym) (v : List Bool) (d : ℕ) :
    clearedTape M base sigma w v d (sigma + w.length + d + 1) =
      some ((v.map M.bitSym).getD (w.length + d) M.blank,decide (w.length + d < v.length)) := by
  simp only [clearedTape,if_neg (by omega : ¬sigma + w.length + d + 1 < sigma),
    if_neg (by omega : sigma + w.length + d + 1 ≠ sigma),
    if_neg (by omega : ¬sigma + w.length + d + 1 < sigma + w.length + 1),
    if_neg (by omega : ¬sigma + w.length + d + 1 < sigma + w.length + d + 1),
    TrackedOutputReturn.bufferTape,show sigma + w.length + d + 1 - sigma - 1 = w.length + d by omega]

private theorem tail_erase (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ)
    (w : List M.Sym) (v : List Bool) (d : ℕ) :
    Function.update (clearedTape M base sigma w v d) (sigma + w.length + d + 1) (some (M.blank,false)) =
      clearedTape M base sigma w v (d + 1) := by
  funext p
  by_cases he : p = sigma + w.length + d + 1
  · subst p
    simp [clearedTape,show ¬sigma + w.length + d + 1 < sigma by omega,
      show sigma + w.length + d + 1 ≠ sigma by omega,show ¬sigma + w.length + d + 1 < sigma + w.length + 1 by omega]
  · rw [Function.update_of_ne he]
    by_cases hp : p < sigma
    · simp [clearedTape,hp]
    · by_cases hm : p = sigma
      · simp [clearedTape,hm]
      · by_cases hw : p < sigma + w.length + 1
        · simp [clearedTape,hp,hm,hw]
        · by_cases hd : p < sigma + w.length + d + 1
          · simp [clearedTape,hp,hm,hw,hd,show p < sigma + w.length + (d + 1) + 1 by omega]
          · simp [clearedTape,hp,hm,hw,hd,show ¬p < sigma + w.length + (d + 1) + 1 by omega]

private theorem marked_payload (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List M.Sym) (p : ℕ) :
    TrackedBankPreparation.bankTape M base sigma w (sigma + p + 1) =
      some (w.getD p M.blank,decide (p < w.length)) := by
  simp only [TrackedBankPreparation.bankTape,if_neg (by omega : ¬sigma + p + 1 < sigma),
    show sigma + p + 1 - sigma = p + 1 by omega,MultitapeTM.tapeOf,
    show p + 1 ≤ w.length ↔ p < w.length by omega]

private theorem source_payload (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List M.Sym) (p : ℕ) :
    TrackedBankPreparation.sourceTape M base sigma w (sigma + p + 1) =
      some (w.getD p M.blank,decide (p < w.length)) := by
  simp only [TrackedBankPreparation.sourceTape,if_neg (by omega : ¬sigma + p + 1 < sigma),
    if_neg (by omega : sigma + p + 1 ≠ sigma),show sigma + p + 1 - sigma - 1 = p by omega]

private theorem cleared_payload (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ)
    (w : List M.Sym) (v : List Bool) (d p : ℕ) :
    clearedTape M base sigma w v d (sigma + p + 1) =
      if p < w.length then some (w.getD p M.blank,true)
      else if p < w.length + d then some (M.blank,false)
      else some ((v.map M.bitSym).getD p M.blank,decide (p < v.length)) := by
  simp only [clearedTape,if_neg (by omega : ¬sigma + p + 1 < sigma),
    if_neg (by omega : sigma + p + 1 ≠ sigma),show sigma + p + 1 - sigma - 1 = p by omega,
    show sigma + p + 1 < sigma + w.length + 1 ↔ p < w.length by omega,
    show sigma + p + 1 < sigma + w.length + d + 1 ↔ p < w.length + d by omega,
    TrackedOutputReturn.bufferTape]

/-- Copying and physically clearing the excess old word leaves exactly the
canonical marked request packet, including its entire fresh blank tail. -/
private theorem cleared_complete (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ)
    (w : List M.Sym) (v : List Bool) :
    clearedTape M base sigma w v (max w.length v.length - w.length) =
      TrackedBankPreparation.bankTape M base sigma w := by
  funext p
  by_cases hp : p < sigma
  · simp [clearedTape,TrackedBankPreparation.bankTape,hp]
  · by_cases hm : p = sigma
    · subst p
      simp [clearedTape,TrackedBankPreparation.bankTape,MultitapeTM.tapeOf]
    · have he : p = sigma + (p - sigma - 1) + 1 := by omega
      rw [he,cleared_payload,marked_payload]
      by_cases hw : p - sigma - 1 < w.length
      · simp only [hw,if_true,decide_true]
      · rw [if_neg hw,List.getD_eq_default w M.blank (by omega)]
        by_cases ht : p - sigma - 1 < w.length + (max w.length v.length - w.length)
        · simp only [if_pos ht,hw,decide_false]
        · rw [if_neg ht]
          have hv : ¬p - sigma - 1 < v.length := by omega
          rw [List.getD_eq_default (v.map M.bitSym) M.blank (by simp only [List.length_map]; omega)]
          simp only [hw,hv,decide_false]

/-- The last actual write clears only the temporary local buffer marker,
producing the exact physical source packet required by child preparation. -/
private theorem marker_to_source (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List M.Sym) :
    Function.update (TrackedBankPreparation.bankTape M base sigma w) sigma (some (M.blank,false)) =
      TrackedBankPreparation.sourceTape M base sigma w := by
  funext p
  by_cases hm : p = sigma
  · subst p
    simp [TrackedBankPreparation.sourceTape]
  · rw [Function.update_of_ne hm]
    by_cases hp : p < sigma
    · simp [TrackedBankPreparation.bankTape,TrackedBankPreparation.sourceTape,hp]
    · have he : p = sigma + (p - sigma - 1) + 1 := by omega
      rw [he,marked_payload,source_payload]

end IntMul.TrackedWordInputBridge




namespace IntMul.TrackedWordInputBridge

open IntMul.TrackedBankedSimulation (Sym)


private theorem buffer_ne_packet (M : MultitapeTM) : bufferTape M ≠ packetTape M := by
  intro h
  have h := congrArg Fin.val h
  simp only [bufferTape,packetTape,BankedSimulation.workTape,MultitapeTM.outTape] at h
  omega

private theorem work_ne_buffer (M : MultitapeTM) (j : Fin M.k) :
    BankedSimulation.workTape M j ≠ bufferTape M := by
  intro h
  have h := congrArg Fin.val h
  simp only [bufferTape,BankedSimulation.workTape] at h
  omega

private theorem initial_buffer (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) :
    initialCells M base sigma offset extent c v (bufferTape M) =
      TrackedOutputReturn.bufferTape M (base.cells (bufferTape M)) sigma v := by
  funext p
  simp [initialCells,TrackedBankedSimulation.embed,parentBase,bufferTape]

private theorem initial_work (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) (j : Fin M.k) (p : ℕ) :
    initialCells M base sigma offset extent c v (BankedSimulation.workTape M j) (offset j + p) =
      some (c.cells j p,decide (p ≤ extent j)) := by
  simp only [initialCells,TrackedBankedSimulation.embed,BankedSimulation.workTape]
  rw [dif_pos (by omega)]
  have hi : BankedSimulation.innerTape M ⟨j.val+2,by omega⟩ (by change 2 ≤ j.val+2; omega) = j := by
    apply Fin.ext
    simp [BankedSimulation.innerTape]
  simp only [hi,if_neg (by omega : ¬offset j+p < offset j),show offset j+p-offset j=p by omega]

private theorem initial_work_head (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) (j : Fin M.k) :
    initialHeads M base sigma offset extent c v (BankedSimulation.workTape M j) = offset j + c.head j := by
  simp only [initialHeads,TrackedBankedSimulation.embed,BankedSimulation.workTape]
  rw [dif_pos (by omega)]
  have hi : BankedSimulation.innerTape M ⟨j.val+2,by omega⟩ (by change 2 ≤ j.val+2; omega) = j := by
    apply Fin.ext
    simp [BankedSimulation.innerTape]
  rw [hi]

private theorem tagged_marker (M : MultitapeTM) (w : ValidWord M) (p e : ℕ) :
    some (M.tapeOf (word M w) p,decide (p ≤ e)) = some (M.startSym,true) ↔ p = 0 := by
  constructor
  · intro h
    have hs := congrArg Prod.fst (Option.some.inj h)
    exact (packet_unique M w p).mp hs
  · intro h
    subst p
    simp [MultitapeTM.tapeOf]

private theorem before_buffer_scan (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) (r : ℕ) :
    (beforeFrame M base sigma offset extent c v r).cells (bufferTape M)
      ((beforeFrame M base sigma offset extent c v r).head (bufferTape M)) =
      TrackedOutputReturn.bufferTape M (base.cells (bufferTape M)) sigma v (sigma+(v.length+1-r)) := by
  simp only [beforeFrame,if_pos rfl,if_true,if_false,eq_self,initial_buffer]

private theorem before_packet_scan (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (packet : c.cells M.outTape = M.tapeOf (word M w)) (r : ℕ) :
    (beforeFrame M base sigma offset extent c v r).cells (packetTape M)
      ((beforeFrame M base sigma offset extent c v r).head (packetTape M)) =
      some (M.tapeOf (word M w) (c.head M.outTape-r),decide (c.head M.outTape-r ≤ extent M.outTape)) := by
  simp only [beforeFrame,if_neg (buffer_ne_packet M).symm,if_pos rfl,if_true,if_false,eq_self,packetTape,work_ne_buffer,Nat.add_assoc,
    initial_work,packet]

private theorem before_markers (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (packet : c.cells M.outTape = M.tapeOf (word M w)) (r : ℕ) :
    ((beforeFrame M base sigma offset extent c v r).cells (bufferTape M)
        ((beforeFrame M base sigma offset extent c v r).head (bufferTape M)) = some (M.startSym,true) ∧
      (beforeFrame M base sigma offset extent c v r).cells (packetTape M)
        ((beforeFrame M base sigma offset extent c v r).head (packetTape M)) = some (M.startSym,true)) ↔
      max (c.head M.outTape) (v.length+1) ≤ r := by
  rw [before_buffer_scan,before_packet_scan M base sigma offset extent c v w packet,
    old_buffer_marker,tagged_marker]
  omega

private theorem before_buffer_not_global (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) (r : ℕ) :
    (beforeFrame M base sigma offset extent c v r).cells (bufferTape M)
      ((beforeFrame M base sigma offset extent c v r).head (bufferTape M)) ≠ none := by
  rw [before_buffer_scan]
  simp only [TrackedOutputReturn.bufferTape,if_neg (by omega : ¬sigma+(v.length+1-r)< sigma)]
  split_ifs <;> exact Option.some_ne_none _

private theorem before_packet_not_global (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) (r : ℕ) :
    (beforeFrame M base sigma offset extent c v r).cells (packetTape M)
      ((beforeFrame M base sigma offset extent c v r).head (packetTape M)) ≠ none := by
  simp only [beforeFrame,if_neg (buffer_ne_packet M).symm,if_pos rfl,if_true,if_false,eq_self,packetTape,work_ne_buffer,Nat.add_assoc,initial_work]
  exact Option.some_ne_none _

private theorem copy_packet_scan (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (packet : c.cells M.outTape = M.tapeOf (word M w)) (j : ℕ) :
    (copyFrame M base sigma offset extent c v w j).cells (packetTape M)
      ((copyFrame M base sigma offset extent c v w j).head (packetTape M)) =
      some ((word M w).getD j M.blank,decide (j+1 ≤ extent M.outTape)) := by
  simp only [copyFrame,if_neg (buffer_ne_packet M).symm,if_pos rfl,if_true,if_false,eq_self,packetTape,work_ne_buffer,Nat.add_assoc,initial_work,packet,
    MultitapeTM.tapeOf]

private theorem copy_buffer_not_global (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (j : ℕ) :
    (copyFrame M base sigma offset extent c v w j).cells (bufferTape M)
      ((copyFrame M base sigma offset extent c v w j).head (bufferTape M)) ≠ none := by
  simp only [copyFrame,if_pos rfl,if_true,if_false,eq_self,copiedTape,if_neg (by omega : ¬sigma+j+1< sigma),
    if_neg (by omega : sigma+j+1≠sigma),if_neg (by omega : ¬sigma+j+1< sigma+j+1)]
  simp [TrackedOutputReturn.bufferTape,show ¬sigma+j+1< sigma by omega,show sigma+j+1≠sigma by omega]

private theorem clear_buffer_scan (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (d : ℕ) :
    (clearFrame M base sigma offset extent c v w d).cells (bufferTape M)
      ((clearFrame M base sigma offset extent c v w d).head (bufferTape M)) =
      some ((v.map M.bitSym).getD ((word M w).length+d) M.blank,
        decide ((word M w).length+d < v.length)) := by
  simp only [clearFrame,if_pos rfl,if_true,if_false,eq_self,tail_read]

private theorem clear_packet_not_global (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (d : ℕ) :
    (clearFrame M base sigma offset extent c v w d).cells (packetTape M)
      ((clearFrame M base sigma offset extent c v w d).head (packetTape M)) ≠ none := by
  simp only [clearFrame,if_neg (buffer_ne_packet M).symm,if_pos rfl,if_true,if_false,eq_self,packetTape,work_ne_buffer,Nat.add_assoc,initial_work]
  exact Option.some_ne_none _

private theorem rewind_buffer_scan (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (r : ℕ) :
    (rewindFrame M base sigma offset extent c v w r).cells (bufferTape M)
      ((rewindFrame M base sigma offset extent c v w r).head (bufferTape M)) =
      some (M.tapeOf (word M w) (max (word M w).length v.length-r),
        decide (max (word M w).length v.length-r ≤ (word M w).length)) := by
  simp only [rewindFrame,if_pos rfl,if_true,if_false,eq_self,TrackedBankPreparation.bankTape,
    if_neg (by omega : ¬sigma+(max (word M w).length v.length-r)< sigma),
    show sigma+(max (word M w).length v.length-r)-sigma=max (word M w).length v.length-r by omega]

private theorem rewind_packet_scan (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (packet : c.cells M.outTape = M.tapeOf (word M w)) (r : ℕ) :
    (rewindFrame M base sigma offset extent c v w r).cells (packetTape M)
      ((rewindFrame M base sigma offset extent c v w r).head (packetTape M)) =
      some (M.tapeOf (word M w) ((word M w).length-r),
        decide ((word M w).length-r ≤ extent M.outTape)) := by
  simp only [rewindFrame,if_neg (buffer_ne_packet M).symm,if_pos rfl,if_true,if_false,eq_self,packetTape,work_ne_buffer,Nat.add_assoc,initial_work,packet]

private theorem rewind_markers (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (packet : c.cells M.outTape = M.tapeOf (word M w)) (r : ℕ) :
    ((rewindFrame M base sigma offset extent c v w r).cells (bufferTape M)
        ((rewindFrame M base sigma offset extent c v w r).head (bufferTape M)) = some (M.startSym,true) ∧
      (rewindFrame M base sigma offset extent c v w r).cells (packetTape M)
        ((rewindFrame M base sigma offset extent c v w r).head (packetTape M)) = some (M.startSym,true)) ↔
      max (word M w).length v.length ≤ r := by
  rw [rewind_buffer_scan,rewind_packet_scan M base sigma offset extent c v w packet,tagged_marker,tagged_marker]
  omega


private theorem before_buffer_marker (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) (r : ℕ) :
    (beforeFrame M base sigma offset extent c v r).cells (bufferTape M)
      ((beforeFrame M base sigma offset extent c v r).head (bufferTape M)) = some (M.startSym,true) ↔ v.length+1 ≤ r := by
  rw [before_buffer_scan,old_buffer_marker]
  omega

private theorem before_packet_marker (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (packet : c.cells M.outTape = M.tapeOf (word M w)) (r : ℕ) :
    (beforeFrame M base sigma offset extent c v r).cells (packetTape M)
      ((beforeFrame M base sigma offset extent c v r).head (packetTape M)) = some (M.startSym,true) ↔ c.head M.outTape ≤ r := by
  rw [before_packet_scan M base sigma offset extent c v w packet,tagged_marker]
  omega

private theorem rewind_buffer_marker (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) (w : ValidWord M) (r : ℕ) :
    (rewindFrame M base sigma offset extent c v w r).cells (bufferTape M)
      ((rewindFrame M base sigma offset extent c v w r).head (bufferTape M)) = some (M.startSym,true) ↔
        max (word M w).length v.length ≤ r := by
  rw [rewind_buffer_scan,tagged_marker]
  omega

private theorem rewind_packet_marker (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (packet : c.cells M.outTape = M.tapeOf (word M w)) (r : ℕ) :
    (rewindFrame M base sigma offset extent c v w r).cells (packetTape M)
      ((rewindFrame M base sigma offset extent c v w r).head (packetTape M)) = some (M.startSym,true) ↔
        (word M w).length ≤ r := by
  rw [rewind_packet_scan M base sigma offset extent c v w packet,tagged_marker]
  omega

end IntMul.TrackedWordInputBridge



namespace IntMul.TrackedWordInputBridge

open IntMul.TrackedBankedSimulation (Sym)

attribute [local instance] Classical.propDecidable

private theorem word_transitions_protect_stay (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .stay = (a,.stay) := by cases a <;> rfl

private theorem word_transitions_protect_right (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .right = (a,.right) := by cases a <;> rfl

private theorem word_transitions_protect_present (M : MultitapeTM) (a : Sym M) (move : Move) (h : a ≠ none) :
    TrackedBankCleanup.protect M a a move = (a,move) := by
  cases ha : a with
  | none => exact False.elim (h ha)
  | some s => rfl

private theorem word_transitions_protect_write (M : MultitapeTM) (a : Sym M) (s : M.Sym × Bool)
    (move : Move) (h : a ≠ none) :
    TrackedBankCleanup.protect M a (some s) move = (some s,move) := by
  cases ha : a with
  | none => exact False.elim (h ha)
  | some old => rfl

private theorem rewind_transition (M : MultitapeTM) (a : Fin (M.k+2) → Sym M) (q : State)
    (phase : q = .before ∨ q = .rewind)
    (not_done : ¬(a (bufferTape M) = some (M.startSym,true) ∧ a (packetTape M) = some (M.startSym,true)))
    (buffer : a (bufferTape M) ≠ none) (packet : a (packetTape M) ≠ none) :
    transition M q a = (q,fun i => (a i,
      if (i=bufferTape M ∨ i=packetTape M) ∧ a i ≠ some (M.startSym,true) then .left else .stay)) := by
  classical
  have hr : rawTransition M q a = (q,fun i => (a i,
      if (i=bufferTape M ∨ i=packetTape M) ∧ a i ≠ some (M.startSym,true) then .left else .stay)) := by
    rcases phase with rfl | rfl <;> simp only [rawTransition,if_neg not_done]
  simp only [transition,hr]
  congr 1
  funext i
  by_cases hi : (i=bufferTape M ∨ i=packetTape M) ∧ a i ≠ some (M.startSym,true)
  · rw [if_pos hi]
    apply word_transitions_protect_present
    rcases hi.1 with rfl | rfl
    · exact buffer
    · exact packet
  · rw [if_neg hi]
    exact word_transitions_protect_stay M _

private theorem before_dispatch (M : MultitapeTM) (a : Fin (M.k+2) → Sym M)
    (done : a (bufferTape M) = some (M.startSym,true) ∧ a (packetTape M) = some (M.startSym,true)) :
    transition M .before a = (.copy,fun i => (a i,
      if i=bufferTape M ∨ i=packetTape M then .right else .stay)) := by
  classical
  simp only [transition,rawTransition,if_pos done]
  congr 1
  funext i
  split
  · exact word_transitions_protect_right M _
  · exact word_transitions_protect_stay M _

private theorem copy_transition (M : MultitapeTM) (a : Fin (M.k+2) → Sym M)
    (s : M.Sym) (b : Bool) (source : a (packetTape M) = some (s,b))
    (letter : s=M.zero ∨ s=M.one ∨ s=M.sep) (buffer : a (bufferTape M) ≠ none) :
    transition M .copy a = (.copy,fun i =>
      (if i=bufferTape M then some (s,true) else a i,
        if i=bufferTape M ∨ i=packetTape M then .right else .stay)) := by
  classical
  have h : TrackedBankedSimulation.decode M (a (packetTape M))=M.zero ∨
      TrackedBankedSimulation.decode M (a (packetTape M))=M.one ∨
      TrackedBankedSimulation.decode M (a (packetTape M))=M.sep := by
    simpa only [source,TrackedBankedSimulation.decode] using letter
  dsimp only [transition,rawTransition]
  rw [if_pos h]
  simp only [source,TrackedBankedSimulation.decode]
  congr 1
  funext i
  by_cases hi : i=bufferTape M
  · subst i
    simp only [eq_self,if_true,true_or]
    exact word_transitions_protect_write M _ _ _ buffer
  · simp only [if_neg hi]
    split
    · exact word_transitions_protect_right M _
    · exact word_transitions_protect_stay M _

private theorem copy_dispatch (M : MultitapeTM) (a : Fin (M.k+2) → Sym M)
    (source : TrackedBankedSimulation.decode M (a (packetTape M))=M.blank) :
    transition M .copy a = (.clearTail,fun i => (a i,.stay)) := by
  classical
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true] at hd
  have hn : ¬(TrackedBankedSimulation.decode M (a (packetTape M))=M.zero ∨
      TrackedBankedSimulation.decode M (a (packetTape M))=M.one ∨
      TrackedBankedSimulation.decode M (a (packetTape M))=M.sep) := by
    rw [source]
    tauto
  simp only [transition,rawTransition,if_neg hn,word_transitions_protect_stay]

private theorem clear_transition (M : MultitapeTM) (a : Fin (M.k+2) → Sym M)
    (flag : TrackedBankCleanup.visited M (a (bufferTape M))=true) :
    transition M .clearTail a = (.clearTail,fun i =>
      (if i=bufferTape M then some (M.blank,false) else a i,
        if i=bufferTape M then .right else .stay)) := by
  classical
  have hb : a (bufferTape M) ≠ none := by
    intro h
    simp only [h,TrackedBankCleanup.visited] at flag
    cases flag
  simp only [transition,rawTransition,if_pos flag]
  congr 1
  funext i
  by_cases hi : i=bufferTape M
  · subst i
    simp only [eq_self,if_true]
    exact word_transitions_protect_write M _ _ _ hb
  · simp only [if_neg hi]
    exact word_transitions_protect_stay M _

private theorem clear_dispatch (M : MultitapeTM) (a : Fin (M.k+2) → Sym M)
    (flag : TrackedBankCleanup.visited M (a (bufferTape M))=false)
    (buffer : a (bufferTape M) ≠ none) (packet : a (packetTape M) ≠ none) :
    transition M .clearTail a = (.rewind,fun i => (a i,
      if i=bufferTape M ∨ i=packetTape M then .left else .stay)) := by
  classical
  have hn : ¬TrackedBankCleanup.visited M (a (bufferTape M))=true := by rw [flag]; decide
  simp only [transition,rawTransition,if_neg hn]
  congr 1
  funext i
  by_cases hi : i=bufferTape M ∨ i=packetTape M
  · rw [if_pos hi]
    apply word_transitions_protect_present
    rcases hi with rfl | rfl
    · exact buffer
    · exact packet
  · rw [if_neg hi]
    exact word_transitions_protect_stay M _

private theorem rewind_dispatch (M : MultitapeTM) (a : Fin (M.k+2) → Sym M)
    (done : a (bufferTape M) = some (M.startSym,true) ∧ a (packetTape M) = some (M.startSym,true)) :
    transition M .rewind a = (.halt,fun i =>
      (if i=bufferTape M then some (M.blank,false) else a i,.stay)) := by
  classical
  simp only [transition,rawTransition,if_pos done]
  congr 1
  funext i
  by_cases hi : i=bufferTape M
  · subst i
    simp only [eq_self,if_true,done.1,TrackedBankCleanup.protect]
  · simp only [if_neg hi]
    exact word_transitions_protect_stay M _

end IntMul.TrackedWordInputBridge



namespace IntMul.TrackedWordInputBridge



private theorem word_before_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem before_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (packet : c.cells M.outTape = M.tapeOf (word M w))
    (r : ℕ) (hr : r < max (c.head M.outTape) (v.length+1)) :
    (machine M).step (beforeFrame M base sigma offset extent c v r) =
      beforeFrame M base sigma offset extent c v (r+1) := by
  classical
  let a := fun i => (beforeFrame M base sigma offset extent c v r).cells i
    ((beforeFrame M base sigma offset extent c v r).head i)
  have hn : ¬(a (bufferTape M)=some (M.startSym,true) ∧ a (packetTape M)=some (M.startSym,true)) := by
    intro h
    have h := (before_markers M base sigma offset extent c v w packet r).mp h
    omega
  have ht := rewind_transition M a .before (Or.inl rfl) hn
    (before_buffer_not_global M base sigma offset extent c v r)
    (before_packet_not_global M base sigma offset extent c v r)
  dsimp only [a] at ht
  change transition M (beforeFrame M base sigma offset extent c v r).state _ = _ at ht
  apply word_before_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hb : i=bufferTape M
    · subst i
      have hm := before_buffer_marker M base sigma offset extent c v r
      by_cases hd : r < v.length+1
      · rw [if_pos ⟨Or.inl rfl,by intro h; have h := hm.mp h; omega⟩]
        simp only [beforeFrame,eq_self,if_true]
        omega
      · rw [if_neg (by intro h; exact h.2 (hm.mpr (by omega)))]
        simp only [beforeFrame,eq_self,if_true]
        omega
    · by_cases hp : i=packetTape M
      · subst i
        have hm := before_packet_marker M base sigma offset extent c v w packet r
        by_cases hd : r < c.head M.outTape
        · rw [if_pos ⟨Or.inr rfl,by intro h; have h := hm.mp h; omega⟩]
          simp only [beforeFrame,if_neg hb,eq_self,if_true]
          omega
        · rw [if_neg (by intro h; exact h.2 (hm.mpr (by omega)))]
          simp only [beforeFrame,if_neg hb,eq_self,if_true]
          omega
      · rw [if_neg (by intro h; rcases h.1 with h | h; exact hb h; exact hp h)]
        simp only [beforeFrame,if_neg hb,if_neg hp]

private theorem before_run (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (packet : c.cells M.outTape = M.tapeOf (word M w))
    (r : ℕ) (hr : r ≤ max (c.head M.outTape) (v.length+1)) :
    (machine M).step^[r] (beforeFrame M base sigma offset extent c v 0) =
      beforeFrame M base sigma offset extent c v r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply',ih (by omega),before_step M base sigma offset extent c v w packet r (by omega)]

private theorem before_end (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (packet : c.cells M.outTape = M.tapeOf (word M w)) :
    (machine M).step (beforeFrame M base sigma offset extent c v (max (c.head M.outTape) (v.length+1))) =
      copyFrame M base sigma offset extent c v w 0 := by
  let A := max (c.head M.outTape) (v.length+1)
  have ha : c.head M.outTape ≤ A := le_max_left _ _
  have hb : v.length+1 ≤ A := le_max_right _ _
  have ht := before_dispatch M
    (fun i => (beforeFrame M base sigma offset extent c v A).cells i
      ((beforeFrame M base sigma offset extent c v A).head i))
    ((before_markers M base sigma offset extent c v w packet A).mpr le_rfl)
  change transition M (beforeFrame M base sigma offset extent c v A).state _ = _ at ht
  dsimp only [A] at ht
  apply word_before_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    by_cases hi : i=bufferTape M
    · subst i
      simp only [beforeFrame,copyFrame,eq_self,if_true,initial_buffer,copied_zero]
    · simp only [beforeFrame,copyFrame,if_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=bufferTape M
    · subst i
      simp only [eq_self,true_or,if_true,beforeFrame,copyFrame]
      omega
    · by_cases hp : i=packetTape M
      · subst i
        simp only [eq_self,or_true,if_true,beforeFrame,copyFrame,if_neg hi]
        omega
      · simp only [if_neg (not_or.mpr ⟨hi,hp⟩),beforeFrame,copyFrame,if_neg hi,if_neg hp]

end IntMul.TrackedWordInputBridge



namespace IntMul.TrackedWordInputBridge



private theorem word_copy_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem copy_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (packet : c.cells M.outTape = M.tapeOf (word M w))
    (j : ℕ) (hj : j < (word M w).length) :
    (machine M).step (copyFrame M base sigma offset extent c v w j) =
      copyFrame M base sigma offset extent c v w (j+1) := by
  classical
  let a := fun i => (copyFrame M base sigma offset extent c v w j).cells i
    ((copyFrame M base sigma offset extent c v w j).head i)
  have ht := copy_transition M a ((word M w).getD j M.blank)
    (decide (j+1≤ extent M.outTape))
    (copy_packet_scan M base sigma offset extent c v w packet j)
    (word_read M w j hj) (copy_buffer_not_global M base sigma offset extent c v w j)
  dsimp only [a] at ht
  change transition M (copyFrame M base sigma offset extent c v w j).state _ = _ at ht
  apply word_copy_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=bufferTape M
    · subst i
      simp only [eq_self,if_true,copyFrame]
      exact copy_write M _ sigma (word M w) v j
    · rw [if_neg hi,Function.update_eq_self]
      simp only [copyFrame,if_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=bufferTape M
    · subst i
      simp only [eq_self,true_or,if_true,copyFrame]
      omega
    · by_cases hp : i=packetTape M
      · subst i
        simp only [eq_self,or_true,if_true,copyFrame,if_neg hi]
        omega
      · simp only [if_neg (not_or.mpr ⟨hi,hp⟩),copyFrame,if_neg hi,if_neg hp]

private theorem copy_run (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (packet : c.cells M.outTape = M.tapeOf (word M w))
    (j : ℕ) (hj : j ≤ (word M w).length) :
    (machine M).step^[j] (copyFrame M base sigma offset extent c v w 0) =
      copyFrame M base sigma offset extent c v w j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply',ih (by omega),copy_step M base sigma offset extent c v w packet j (by omega)]

private theorem copy_end (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (packet : c.cells M.outTape = M.tapeOf (word M w)) :
    (machine M).step (copyFrame M base sigma offset extent c v w (word M w).length) =
      clearFrame M base sigma offset extent c v w 0 := by
  have hs : TrackedBankedSimulation.decode M
      ((copyFrame M base sigma offset extent c v w (word M w).length).cells (packetTape M)
        ((copyFrame M base sigma offset extent c v w (word M w).length).head (packetTape M))) = M.blank := by
    rw [copy_packet_scan M base sigma offset extent c v w packet]
    simp only [TrackedBankedSimulation.decode,List.getD_eq_default _ _ le_rfl]
  have ht := copy_dispatch M
    (fun i => (copyFrame M base sigma offset extent c v w (word M w).length).cells i
      ((copyFrame M base sigma offset extent c v w (word M w).length).head i)) hs
  change transition M (copyFrame M base sigma offset extent c v w (word M w).length).state _ = _ at ht
  apply word_copy_cfg_ext
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
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (d : ℕ)
    (hd : d < max (word M w).length v.length-(word M w).length) :
    (machine M).step (clearFrame M base sigma offset extent c v w d) =
      clearFrame M base sigma offset extent c v w (d+1) := by
  classical
  have hv : (word M w).length+d < v.length := by omega
  have hf : TrackedBankCleanup.visited M
      ((clearFrame M base sigma offset extent c v w d).cells (bufferTape M)
        ((clearFrame M base sigma offset extent c v w d).head (bufferTape M))) = true := by
    rw [clear_buffer_scan]
    simp only [TrackedBankCleanup.visited,decide_eq_true hv]
  have ht := clear_transition M
    (fun i => (clearFrame M base sigma offset extent c v w d).cells i
      ((clearFrame M base sigma offset extent c v w d).head i)) hf
  change transition M (clearFrame M base sigma offset extent c v w d).state _ = _ at ht
  apply word_copy_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=bufferTape M
    · subst i
      simp only [eq_self,if_true,clearFrame]
      exact tail_erase M _ sigma (word M w) v d
    · rw [if_neg hi,Function.update_eq_self]
      simp only [clearFrame,if_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=bufferTape M
    · subst i
      simp only [eq_self,if_true,clearFrame]
      omega
    · simp only [if_neg hi,clearFrame,if_neg hi]

private theorem clear_run (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (d : ℕ)
    (hd : d ≤ max (word M w).length v.length-(word M w).length) :
    (machine M).step^[d] (clearFrame M base sigma offset extent c v w 0) =
      clearFrame M base sigma offset extent c v w d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply',ih (by omega),clear_step M base sigma offset extent c v w d (by omega)]

private theorem clear_end (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) (w : ValidWord M) :
    (machine M).step (clearFrame M base sigma offset extent c v w
      (max (word M w).length v.length-(word M w).length)) =
      rewindFrame M base sigma offset extent c v w 0 := by
  classical
  let D := max (word M w).length v.length-(word M w).length
  change (machine M).step (clearFrame M base sigma offset extent c v w D) = _
  have hlen : (word M w).length+D=max (word M w).length v.length := by dsimp [D]; omega
  have hv : ¬(word M w).length+D < v.length := by omega
  have hf : TrackedBankCleanup.visited M
      ((clearFrame M base sigma offset extent c v w D).cells (bufferTape M)
        ((clearFrame M base sigma offset extent c v w D).head (bufferTape M))) = false := by
    rw [clear_buffer_scan]
    simp only [TrackedBankCleanup.visited,decide_eq_false hv]
  have hb : (clearFrame M base sigma offset extent c v w D).cells (bufferTape M)
      ((clearFrame M base sigma offset extent c v w D).head (bufferTape M)) ≠ none := by
    rw [clear_buffer_scan]
    exact Option.some_ne_none _
  have ht := clear_dispatch M
    (fun i => (clearFrame M base sigma offset extent c v w D).cells i
      ((clearFrame M base sigma offset extent c v w D).head i)) hf hb
    (clear_packet_not_global M base sigma offset extent c v w D)
  change transition M (clearFrame M base sigma offset extent c v w D).state _ = _ at ht
  apply word_copy_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    simp only [clearFrame,rewindFrame]
    by_cases hi : i=bufferTape M
    · simp only [if_pos hi]
      exact cleared_complete M _ sigma (word M w) v
    · simp only [if_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=bufferTape M
    · subst i
      simp only [eq_self,true_or,if_true,clearFrame,rewindFrame,Nat.sub_zero]
      omega
    · by_cases hp : i=packetTape M
      · subst i
        simp only [eq_self,or_true,if_true,clearFrame,rewindFrame,if_neg hi,Nat.sub_zero]
        omega
      · simp only [if_neg (not_or.mpr ⟨hi,hp⟩),clearFrame,rewindFrame,if_neg hi,if_neg hp]

end IntMul.TrackedWordInputBridge



namespace IntMul.TrackedWordInputBridge



private theorem word_rewind_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem rewind_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (packet : c.cells M.outTape = M.tapeOf (word M w))
    (r : ℕ) (hr : r < max (word M w).length v.length) :
    (machine M).step (rewindFrame M base sigma offset extent c v w r) =
      rewindFrame M base sigma offset extent c v w (r+1) := by
  classical
  let a := fun i => (rewindFrame M base sigma offset extent c v w r).cells i
    ((rewindFrame M base sigma offset extent c v w r).head i)
  have hn : ¬(a (bufferTape M)=some (M.startSym,true) ∧ a (packetTape M)=some (M.startSym,true)) := by
    intro h
    have h := (rewind_markers M base sigma offset extent c v w packet r).mp h
    omega
  have hb : a (bufferTape M) ≠ none := by
    dsimp only [a]
    rw [rewind_buffer_scan]
    exact Option.some_ne_none _
  have hp : a (packetTape M) ≠ none := by
    dsimp only [a]
    rw [rewind_packet_scan M base sigma offset extent c v w packet]
    exact Option.some_ne_none _
  have ht := rewind_transition M a .rewind (Or.inr rfl) hn hb hp
  dsimp only [a] at ht
  change transition M (rewindFrame M base sigma offset extent c v w r).state _ = _ at ht
  apply word_rewind_cfg_ext
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
      have hm := rewind_buffer_marker M base sigma offset extent c v w r
      rw [if_pos ⟨Or.inl rfl,by intro h; have h := hm.mp h; omega⟩]
      simp only [rewindFrame,eq_self,if_true]
      omega
    · by_cases hp : i=packetTape M
      · subst i
        have hm := rewind_packet_marker M base sigma offset extent c v w packet r
        by_cases hd : r < (word M w).length
        · rw [if_pos ⟨Or.inr rfl,by intro h; have h := hm.mp h; omega⟩]
          simp only [rewindFrame,if_neg hi,eq_self,if_true]
          omega
        · rw [if_neg (by intro h; exact h.2 (hm.mpr (by omega)))]
          simp only [rewindFrame,if_neg hi,eq_self,if_true]
          omega
      · rw [if_neg (by intro h; rcases h.1 with h | h; exact hi h; exact hp h)]
        simp only [rewindFrame,if_neg hi,if_neg hp]

private theorem rewind_run (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (packet : c.cells M.outTape = M.tapeOf (word M w))
    (r : ℕ) (hr : r ≤ max (word M w).length v.length) :
    (machine M).step^[r] (rewindFrame M base sigma offset extent c v w 0) =
      rewindFrame M base sigma offset extent c v w r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply',ih (by omega),rewind_step M base sigma offset extent c v w packet r (by omega)]

private theorem rewind_end (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (packet : c.cells M.outTape = M.tapeOf (word M w)) :
    (machine M).step (rewindFrame M base sigma offset extent c v w (max (word M w).length v.length)) =
      finalFrame M base sigma offset extent c v w := by
  have ht := rewind_dispatch M
    (fun i => (rewindFrame M base sigma offset extent c v w (max (word M w).length v.length)).cells i
      ((rewindFrame M base sigma offset extent c v w (max (word M w).length v.length)).head i))
    ((rewind_markers M base sigma offset extent c v w packet _).mpr le_rfl)
  change transition M (rewindFrame M base sigma offset extent c v w (max (word M w).length v.length)).state _ = _ at ht
  apply word_rewind_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=bufferTape M
    · subst i
      simp only [eq_self,if_true,rewindFrame,finalFrame,Nat.sub_self,Nat.add_zero]
      exact marker_to_source M _ sigma (word M w)
    · rw [if_neg hi,Function.update_eq_self]
      simp only [rewindFrame,finalFrame,if_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=bufferTape M
    · subst i
      simp only [rewindFrame,finalFrame,eq_self,if_true,Nat.sub_self,Nat.add_zero]
    · by_cases hp : i=packetTape M
      · subst i
        simp only [rewindFrame,finalFrame,if_neg hi,eq_self,if_true,
          Nat.sub_eq_zero_of_le (le_max_left (word M w).length v.length),Nat.add_zero]
      · simp only [rewindFrame,finalFrame,if_neg hi,if_neg hp]

end IntMul.TrackedWordInputBridge



namespace IntMul.TrackedWordInputBridge



private theorem source_idempotent (M : MultitapeTM) (base : ℕ → TrackedBankedSimulation.Sym M)
    (sigma : ℕ) (w : List M.Sym) :
    TrackedBankPreparation.sourceTape M (TrackedBankPreparation.sourceTape M base sigma w) sigma w =
      TrackedBankPreparation.sourceTape M base sigma w := by
  funext p
  by_cases hp : p< sigma
  · simp [TrackedBankPreparation.sourceTape,hp]
  · by_cases hm : p=sigma
    · simp [TrackedBankPreparation.sourceTape,hm]
    · simp [TrackedBankPreparation.sourceTape,hp,hm]

private theorem run_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (packet : c.cells M.outTape = M.tapeOf (word M w)) :
    (machine M).step^[max (c.head M.outTape) (v.length+1) + 2*max (word M w).length v.length + 4]
      (initialFrame M base sigma offset extent c v) = finalFrame M base sigma offset extent c v w := by
  let A := max (c.head M.outTape) (v.length+1)
  let L := (word M w).length
  let H := max L v.length
  let D := H-L
  have hlen : L+D=H := by dsimp [D,H]; omega
  have hbefore : (machine M).step^[A+1] (initialFrame M base sigma offset extent c v) =
      copyFrame M base sigma offset extent c v w 0 := by
    change (machine M).step^[A+1] (beforeFrame M base sigma offset extent c v 0) = _
    rw [Function.iterate_succ_apply',before_run M base sigma offset extent c v w packet A le_rfl,
      before_end M base sigma offset extent c v w packet]
  have hcopy : (machine M).step^[L+1] (copyFrame M base sigma offset extent c v w 0) =
      clearFrame M base sigma offset extent c v w 0 := by
    rw [Function.iterate_succ_apply',copy_run M base sigma offset extent c v w packet L le_rfl,
      copy_end M base sigma offset extent c v w packet]
  have hclear : (machine M).step^[D+1] (clearFrame M base sigma offset extent c v w 0) =
      rewindFrame M base sigma offset extent c v w 0 := by
    rw [Function.iterate_succ_apply',clear_run M base sigma offset extent c v w D le_rfl,
      clear_end M base sigma offset extent c v w]
  have hrewind : (machine M).step^[H+1] (rewindFrame M base sigma offset extent c v w 0) =
      finalFrame M base sigma offset extent c v w := by
    rw [Function.iterate_succ_apply',rewind_run M base sigma offset extent c v w packet H le_rfl,
      rewind_end M base sigma offset extent c v w packet]
  have hcopybefore : (machine M).step^[(L+1)+(A+1)] (initialFrame M base sigma offset extent c v) =
      clearFrame M base sigma offset extent c v w 0 := by
    rw [Function.iterate_add_apply,hbefore,hcopy]
  have hclearcopy : (machine M).step^[(D+1)+((L+1)+(A+1))] (initialFrame M base sigma offset extent c v) =
      rewindFrame M base sigma offset extent c v w 0 := by
    rw [Function.iterate_add_apply,hcopybefore,hclear]
  change (machine M).step^[A+2*H+4] (initialFrame M base sigma offset extent c v) = _
  rw [show A+2*H+4=(H+1)+((D+1)+((L+1)+(A+1))) by omega,
    Function.iterate_add_apply,hclearcopy,hrewind]

/-- Physically marshal an already computed parent request into the reusable
caller buffer. This theorem includes the complete actual run, the exact
self-consistent child-input condition, every retained parent cell/flag, and
the source rewind and unchanged remaining parent heads. -/
private theorem word_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (packet : c.cells M.outTape = M.tapeOf (word M w)) :
    (machine M).step^[max (c.head M.outTape) (v.length+1) + 2*max (word M w).length v.length + 4]
      (initialFrame M base sigma offset extent c v) = finalFrame M base sigma offset extent c v w ∧
    (finalFrame M base sigma offset extent c v w).state = (machine M).qHalt ∧
    (finalFrame M base sigma offset extent c v w).cells (bufferTape M) =
      TrackedBankPreparation.sourceTape M (base.cells (bufferTape M)) sigma (word M w) ∧
    (finalFrame M base sigma offset extent c v w).cells (bufferTape M) =
      TrackedBankPreparation.sourceTape M
        ((finalFrame M base sigma offset extent c v w).cells (bufferTape M)) sigma (word M w) ∧
    (finalFrame M base sigma offset extent c v w).head (bufferTape M) = sigma ∧
    (∀ j, (finalFrame M base sigma offset extent c v w).cells (BankedSimulation.workTape M j) =
      (initialFrame M base sigma offset extent c v).cells (BankedSimulation.workTape M j)) ∧
    (∀ j, (finalFrame M base sigma offset extent c v w).head (BankedSimulation.workTape M j) =
      if j=M.outTape then offset j else offset j+c.head j) := by
  refine ⟨run_correct M base sigma offset extent c v w packet,rfl,?_,?_,?_,?_,?_⟩
  · simp only [finalFrame,eq_self,if_true]
  · simp only [finalFrame,eq_self,if_true]
    exact (source_idempotent M _ sigma (word M w)).symm
  · simp only [finalFrame,eq_self,if_true]
  · intro j
    simp only [finalFrame,if_neg (work_ne_buffer M j),initialFrame,beforeFrame]
  · intro j
    simp only [finalFrame,if_neg (work_ne_buffer M j)]
    by_cases hj : j=M.outTape
    · subst j
      simp only [packetTape,eq_self,if_true]
    · have hn : BankedSimulation.workTape M j ≠ packetTape M := by
        intro h
        apply hj
        apply Fin.ext
        have h := congrArg Fin.val h
        simp only [BankedSimulation.workTape,packetTape] at h
        omega
      simp only [if_neg hn,if_neg hj,initial_work_head]

end IntMul.TrackedWordInputBridge



namespace IntMul.TrackedReturnReplacement

private theorem return_programs_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem return_programs_fixed_iterate (N : MultitapeTM) (c : N.Cfg) (fixed : N.step c=c) (T : ℕ) :
    N.step^[T] c=c := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,fixed]

private theorem return_programs_halted_step (N : MultitapeTM) (c : N.Cfg) (halt : c.state=N.qHalt) : N.step c=c := by
  apply return_programs_cfg_ext
  · simp [MultitapeTM.step,halt,N.halt_fixed]
  · funext i
    simp only [MultitapeTM.step,halt,N.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,N.halt_fixed]

/-- First entry to any family of quiescent service exits preserves the exact
complete supplied terminal configuration, including all tape heads. -/
private theorem return_programs_first_exit (N : MultitapeTM) (P : N.K → Prop)
    (fixed : ∀ d : N.Cfg, P d.state → N.step d=d) (c : N.Cfg) (T : ℕ)
    (exit : P (N.step^[T] c).state) :
    ∃ t, t≤ T ∧ N.step^[t] c=N.step^[T] c ∧ ∀ s, s< t → ¬P (N.step^[s] c).state := by
  classical
  have hex : ∃ t, P (N.step^[t] c).state := ⟨T,exit⟩
  let t := Nat.find hex
  have ht : t≤ T := Nat.find_min' hex exit
  have hp : P (N.step^[t] c).state := Nat.find_spec hex
  refine ⟨t,ht,?_,?_⟩
  · rw [show T=(T-t)+t by omega,Function.iterate_add_apply,return_programs_fixed_iterate N _ (fixed _ hp)]
  · intro s hs
    exact Nat.find_min hex hs

private theorem lift_input_step (M : MultitapeTM) (c : (TrackedWordInputBridge.machine M).Cfg)
    (live : c.state ≠ (TrackedWordInputBridge.machine M).qHalt) :
    (machine M).step (liftInput M c)=liftInput M ((TrackedWordInputBridge.machine M).step c) := by
  have ht : transition M (.inl c.state) (fun i => c.cells i (c.head i))=
      (.inl ((TrackedWordInputBridge.machine M).δ c.state (fun i => c.cells i (c.head i))).1,
        ((TrackedWordInputBridge.machine M).δ c.state (fun i => c.cells i (c.head i))).2) := by
    simp only [transition,if_neg live]
  apply return_programs_cfg_ext
  · simp only [MultitapeTM.step,liftInput,ht]
  · simp only [MultitapeTM.step,liftInput,ht]
  · simp only [MultitapeTM.step,liftInput,ht]

private theorem lift_input_iterate (M : MultitapeTM) (c : (TrackedWordInputBridge.machine M).Cfg)
    (T : ℕ) (live : ∀ s, s < T → ((TrackedWordInputBridge.machine M).step^[s] c).state ≠
      (TrackedWordInputBridge.machine M).qHalt) :
    (machine M).step^[T] (liftInput M c)=liftInput M ((TrackedWordInputBridge.machine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      lift_input_step M _ (live T (by omega)),Function.iterate_succ_apply']

private theorem run_input_to_seal (M : MultitapeTM) (c : (TrackedWordInputBridge.machine M).Cfg)
    (T : ℕ) (exit : ((TrackedWordInputBridge.machine M).step^[T] c).state=
      (TrackedWordInputBridge.machine M).qHalt) :
    ∃ t, t ≤ T ∧ (machine M).step^[t] (liftInput M c)=
      liftInput M ((TrackedWordInputBridge.machine M).step^[T] c) := by
  obtain ⟨t,ht,he,hlive⟩ := return_programs_first_exit (TrackedWordInputBridge.machine M)
    (fun q => q=(TrackedWordInputBridge.machine M).qHalt)
    (by intro d hd; exact return_programs_halted_step _ d hd) c T exit
  refine ⟨t,ht,?_⟩
  rw [lift_input_iterate M c t hlive,he]

end IntMul.TrackedReturnReplacement



namespace IntMul.TrackedReturnReplacement

private theorem return_seek_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem source_to_return (M : MultitapeTM) (base : ℕ → TrackedBankedSimulation.Sym M)
    (sigma : ℕ) (w : List Bool) :
    Function.update (TrackedBankPreparation.sourceTape M base sigma (w.map M.bitSym)) sigma
      (some (M.startSym,true))=TrackedOutputReturn.bufferTape M base sigma w := by
  funext p
  by_cases hm : p=sigma
  · subst p
    simp [TrackedOutputReturn.bufferTape]
  · rw [Function.update_of_ne hm]
    by_cases hp : p < sigma
    · simp [TrackedBankPreparation.sourceTape,TrackedOutputReturn.bufferTape,hp]
    · simp [TrackedBankPreparation.sourceTape,TrackedOutputReturn.bufferTape,hp,hm]

private theorem seal_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) :
    (machine M).step (liftInput M
      (TrackedWordInputBridge.finalFrame M (inputBase M base) sigma offset extent c v (bitWord M w)))=
      seekFrame M base sigma offset extent c v w 0 := by
  classical
  let d := TrackedWordInputBridge.finalFrame M (inputBase M base) sigma offset extent c v (bitWord M w)
  have ht : transition M (.inl d.state) (fun i => d.cells i (d.head i))=
      (.inr false,sealActions M (fun i => d.cells i (d.head i))) := by
    simp only [transition]
    have h : d.state=TrackedWordInputBridge.State.halt := rfl
    rw [if_pos h]
  have hb : d.cells (bufferTape M) (d.head (bufferTape M))=some (M.blank,false) := by
    simp [d,TrackedWordInputBridge.finalFrame,bufferTape,TrackedBankPreparation.sourceTape]
  dsimp only [d] at ht hb
  apply return_seek_cfg_ext
  · simp only [MultitapeTM.step,liftInput,ht]
    rfl
  · simp only [MultitapeTM.step,liftInput,ht]
    funext i
    by_cases hi : i=bufferTape M
    · subst i
      simp only [sealActions,eq_self,if_true,hb,TrackedBankCleanup.protect]
      change Function.update (TrackedBankPreparation.sourceTape M (base.cells (bufferTape M)) sigma (w.map M.bitSym))
        sigma (some (M.startSym,true))=_
      rw [source_to_return]
      rfl
    · simp only [sealActions,if_neg hi]
      have he : TrackedBankCleanup.protect M (d.cells i (d.head i)) (d.cells i (d.head i)) .stay=
          (d.cells i (d.head i),.stay) := by cases d.cells i (d.head i) <;> rfl
      rw [he,Function.update_eq_self]
      simp only [seekFrame,if_neg hi]
  · simp only [MultitapeTM.step,liftInput,ht]
    funext i
    by_cases hi : i=bufferTape M
    · subst i
      simp only [sealActions,eq_self,if_true,hb,TrackedBankCleanup.protect,seekFrame]
      change sigma+1=sigma+0+1
      omega
    · simp only [sealActions,if_neg hi]
      cases h : d.cells i (d.head i) <;> simp [TrackedBankCleanup.protect,h,seekFrame,hi,d]

private theorem seek_scan (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (j : ℕ) :
    TrackedBankCleanup.visited M
      ((seekFrame M base sigma offset extent c v w j).cells (bufferTape M)
        ((seekFrame M base sigma offset extent c v w j).head (bufferTape M)))=decide (j < w.length) := by
  simp only [seekFrame,eq_self,if_true,TrackedOutputReturn.bufferTape,
    if_neg (by omega : ¬sigma+j+1 < sigma),if_neg (by omega : sigma+j+1≠sigma),
    show sigma+j+1-sigma-1=j by omega,TrackedBankCleanup.visited]

private theorem seek_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool)
    (j : ℕ) (hj : j < w.length) :
    (machine M).step (seekFrame M base sigma offset extent c v w j)=
      seekFrame M base sigma offset extent c v w (j+1) := by
  classical
  have ht : transition M (seekFrame M base sigma offset extent c v w j).state
      (fun i => (seekFrame M base sigma offset extent c v w j).cells i
        ((seekFrame M base sigma offset extent c v w j).head i))=
      (.inr false,seekActions M
        (fun i => (seekFrame M base sigma offset extent c v w j).cells i
          ((seekFrame M base sigma offset extent c v w j).head i))) := by
    change transition M (.inr false) _ = _
    simp only [transition]
    rw [seek_scan,if_pos (by simp only [hj,decide_true])]
  apply return_seek_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht,seekActions]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht,seekActions]
    funext i
    by_cases hi : i=bufferTape M
    · simp [seekFrame,hi,Nat.add_assoc]
    · simp [seekFrame,hi]

private theorem seek_run (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool)
    (j : ℕ) (hj : j ≤ w.length) :
    (machine M).step^[j] (seekFrame M base sigma offset extent c v w 0)=
      seekFrame M base sigma offset extent c v w j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply',ih (by omega),seek_step M base sigma offset extent c v w j (by omega)]

private theorem seek_end (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) :
    (machine M).step (seekFrame M base sigma offset extent c v w w.length)=
      finalFrame M base sigma offset extent c v w := by
  have ht : transition M (seekFrame M base sigma offset extent c v w w.length).state
      (fun i => (seekFrame M base sigma offset extent c v w w.length).cells i
        ((seekFrame M base sigma offset extent c v w w.length).head i))=
      (.inr true,fun i => ((seekFrame M base sigma offset extent c v w w.length).cells i
        ((seekFrame M base sigma offset extent c v w w.length).head i),.stay)) := by
    change transition M (.inr false) _ = _
    simp only [transition]
    rw [seek_scan,if_neg (by simp)]
  apply return_seek_cfg_ext
  · simp only [MultitapeTM.step,ht,finalFrame]
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht,finalFrame]

end IntMul.TrackedReturnReplacement



namespace IntMul.TrackedReturnReplacement

/-- Physically replace any older returned bit word by the actual output-bank
word, including empty and shorter replacements, with a full fresh tail and
the head just after the new result. All source banks and flags are retained. -/
private theorem return_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool)
    (packet : c.cells M.outTape=M.tapeOf (w.map M.bitSym)) :
    ∃ t, t ≤ max (c.head M.outTape) (v.length+1)+2*max w.length v.length+w.length+6 ∧
      (machine M).step^[t] (initialFrame M base sigma offset extent c v)=
        finalFrame M base sigma offset extent c v w ∧
      (finalFrame M base sigma offset extent c v w).state=(machine M).qHalt ∧
      (finalFrame M base sigma offset extent c v w).cells (bufferTape M)=
        TrackedOutputReturn.bufferTape M (base.cells (bufferTape M)) sigma w ∧
      (finalFrame M base sigma offset extent c v w).head (bufferTape M)=sigma+w.length+1 ∧
      (∀ j, (finalFrame M base sigma offset extent c v w).cells (BankedSimulation.workTape M j)=
        (initialFrame M base sigma offset extent c v).cells (BankedSimulation.workTape M j)) ∧
      (∀ j, (finalFrame M base sigma offset extent c v w).head (BankedSimulation.workTape M j)=
        if j=M.outTape then offset j else offset j+c.head j) := by
  let I := max (c.head M.outTape) (v.length+1)+2*max w.length v.length+4
  have hWord := TrackedWordInputBridge.word_correct M (inputBase M base) sigma offset extent c v
    (bitWord M w) packet
  have hInput : (TrackedWordInputBridge.machine M).step^[I]
      (TrackedWordInputBridge.initialFrame M (inputBase M base) sigma offset extent c v)=
      TrackedWordInputBridge.finalFrame M (inputBase M base) sigma offset extent c v (bitWord M w) := by
    simpa only [I,TrackedWordInputBridge.word,bitWord,List.length_map] using hWord.1
  have hHalt : ((TrackedWordInputBridge.machine M).step^[I]
      (TrackedWordInputBridge.initialFrame M (inputBase M base) sigma offset extent c v)).state=
      (TrackedWordInputBridge.machine M).qHalt := by rw [hInput]; rfl
  obtain ⟨s,hs,hsRun⟩ := run_input_to_seal M
    (TrackedWordInputBridge.initialFrame M (inputBase M base) sigma offset extent c v) I hHalt
  rw [hInput] at hsRun
  have hSeal : (machine M).step^[s+1] (initialFrame M base sigma offset extent c v)=
      seekFrame M base sigma offset extent c v w 0 := by
    rw [Function.iterate_succ_apply']
    change (machine M).step ((machine M).step^[s]
      (liftInput M (TrackedWordInputBridge.initialFrame M (inputBase M base) sigma offset extent c v)))=_
    rw [hsRun,seal_step]
  have hSeek : (machine M).step^[w.length+1] (seekFrame M base sigma offset extent c v w 0)=
      finalFrame M base sigma offset extent c v w := by
    rw [Function.iterate_succ_apply',seek_run M base sigma offset extent c v w _ le_rfl,seek_end]
  refine ⟨(w.length+1)+(s+1),?_,?_,rfl,?_,?_,?_,?_⟩
  · dsimp only [I] at hs
    omega
  · rw [Function.iterate_add_apply,hSeal,hSeek]
  · simp only [finalFrame,seekFrame,eq_self,if_true]
  · simp only [finalFrame,seekFrame,eq_self,if_true]
  · intro j
    have hn : BankedSimulation.workTape M j ≠ bufferTape M := TrackedWordInputBridge.work_ne_buffer M j
    simp only [finalFrame,seekFrame,if_neg hn]
    exact hWord.2.2.2.2.2.1 j
  · intro j
    have hn : BankedSimulation.workTape M j ≠ bufferTape M := TrackedWordInputBridge.work_ne_buffer M j
    simp only [finalFrame,seekFrame,if_neg hn]
    exact hWord.2.2.2.2.2.2 j

end IntMul.TrackedReturnReplacement


open IntMul IntMul.TrackedReturnReplacement

theorem solution (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool)
    (packet : c.cells M.outTape=M.tapeOf (w.map M.bitSym)) :
    ∃ t, t ≤ max (c.head M.outTape) (v.length+1)+2*max w.length v.length+w.length+6 ∧
      (machine M).step^[t] (initialFrame M base sigma offset extent c v)=
        finalFrame M base sigma offset extent c v w ∧
      (finalFrame M base sigma offset extent c v w).state=(machine M).qHalt ∧
      (finalFrame M base sigma offset extent c v w).cells (bufferTape M)=
        TrackedOutputReturn.bufferTape M (base.cells (bufferTape M)) sigma w ∧
      (finalFrame M base sigma offset extent c v w).head (bufferTape M)=sigma+w.length+1 ∧
      (∀ j, (finalFrame M base sigma offset extent c v w).cells (BankedSimulation.workTape M j)=
        (initialFrame M base sigma offset extent c v).cells (BankedSimulation.workTape M j)) ∧
      (∀ j, (finalFrame M base sigma offset extent c v w).head (BankedSimulation.workTape M j)=
        if j=M.outTape then offset j else offset j+c.head j) :=
  IntMul.TrackedReturnReplacement.return_correct M base sigma offset extent c v w packet

#print axioms solution
