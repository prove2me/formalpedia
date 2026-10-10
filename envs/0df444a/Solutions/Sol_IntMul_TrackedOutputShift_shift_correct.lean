-- Prove2me | solution 1 for IntMul.TrackedOutputShift.shift_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T23:14:13.168093+00:00
-- url     : https://prove2.me/submissions/b73aea89-38b2-4302-a89f-d76304ce880a

import Definitions.Def_IntMul_TrackedOutputShift
import Mathlib.Data.List.GetD
import Mathlib.Tactic


namespace IntMul.TrackedOutputShift

open IntMul.TrackedBankedSimulation (Sym)

private theorem tape_payload_not_marker (M : MultitapeTM) (w : List Bool) (p : ℕ) :
    (w.map M.bitSym).getD p M.blank ≠ M.startSym := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at hd
  by_cases hp : p < w.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hp),List.getElem_map]
    cases w[p] <;> simp only [MultitapeTM.bitSym,Bool.false_eq_true,if_false,if_true] <;> aesop
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    aesop

private theorem buffer_boundary (M : MultitapeTM) (base : ℕ → Sym M) (w : List Bool) :
    TrackedOutputReturn.bufferTape M base 1 w 1 = some (M.startSym,true) := by
  simp [TrackedOutputReturn.bufferTape]

private theorem buffer_payload (M : MultitapeTM) (base : ℕ → Sym M) (w : List Bool) (p : ℕ) :
    TrackedOutputReturn.bufferTape M base 1 w (p + 2) =
      some ((w.map M.bitSym).getD p M.blank,decide (p < w.length)) := by
  simp [TrackedOutputReturn.bufferTape,show ¬p + 2 < 1 by omega,show p + 2 ≠ 1 by omega]

private theorem buffer_ne_marker (M : MultitapeTM) (base : ℕ → Sym M) (w : List Bool) (p : ℕ)
    (hp : 1 < p) : TrackedOutputReturn.bufferTape M base 1 w p ≠ some (M.startSym,true) := by
  have he : p = (p - 2) + 2 := by omega
  rw [he,buffer_payload]
  intro h
  exact tape_payload_not_marker M w _ (congrArg Prod.fst (Option.some.inj h))

private theorem buffer_nonzero (M : MultitapeTM) (base : ℕ → Sym M) (w : List Bool) (p : ℕ)
    (hp : 0 < p) : TrackedOutputReturn.bufferTape M base 1 w p ≠ none := by
  by_cases he : p = 1
  · subst p
    simp [TrackedOutputReturn.bufferTape]
  · simp [TrackedOutputReturn.bufferTape,show ¬p < 1 by omega,he]

private theorem mixed_zero (M : MultitapeTM) (base : ℕ → Sym M) (w : List Bool) :
    mixedTape M base w 0 = TrackedOutputReturn.bufferTape M base 1 w := by
  funext p
  cases p with
  | zero => simp [mixedTape,TrackedOutputReturn.bufferTape]
  | succ p => simp [mixedTape]

private theorem mixed_read (M : MultitapeTM) (base : ℕ → Sym M) (w : List Bool) (j : ℕ) :
    mixedTape M base w j (j + 2) =
      some ((w.map M.bitSym).getD j M.blank,decide (j < w.length)) := by
  simp only [mixedTape,if_neg (by omega : j + 2 ≠ 0),if_neg (by omega : ¬j + 2 ≤ j)]
  exact buffer_payload M base w j

private theorem mixed_nonzero (M : MultitapeTM) (base : ℕ → Sym M) (w : List Bool) (j p : ℕ)
    (hp : 0 < p) : mixedTape M base w j p ≠ none := by
  simp only [mixedTape,if_neg (by omega : p ≠ 0)]
  split
  · simp
  · exact buffer_nonzero M base w p hp

/-- One stored bit overwrites its destination immediately to the left;
all unread source bits, the global marker and earlier destinations remain. -/
private theorem mixed_write (M : MultitapeTM) (base : ℕ → Sym M) (w : List Bool) (j : ℕ) (hj : j < w.length) :
    Function.update (mixedTape M base w j) (j + 1) (some (M.bitSym w[j],true)) =
      mixedTape M base w (j + 1) := by
  classical
  funext p
  by_cases he : p = j + 1
  · subst p
    simp only [Function.update_self,mixedTape,if_neg (by omega : j + 1 ≠ 0),if_pos le_rfl,Nat.add_sub_cancel]
    rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]
  · rw [Function.update_of_ne he]
    by_cases hp : p = 0
    · simp only [mixedTape,if_pos hp]
    · simp only [mixedTape,if_neg hp]
      have hc : p ≤ j + 1 ↔ p ≤ j := by omega
      simp only [hc]

/-- After all bits are shifted, one physical erase clears the last duplicate
or the empty word's local marker and leaves a canonical blank tail. -/
private theorem mixed_erase (M : MultitapeTM) (base : ℕ → Sym M) (w : List Bool) :
    Function.update (mixedTape M base w w.length) (w.length + 1) (some (M.blank,false)) =
      outputTape M base w := by
  classical
  funext p
  by_cases he : p = w.length + 1
  · subst p
    simp [outputTape]
  · rw [Function.update_of_ne he]
    by_cases hz : p = 0
    · simp [mixedTape,outputTape,hz]
    · by_cases hp : p ≤ w.length
      · have hl : p - 1 < w.length := by omega
        simp [mixedTape,outputTape,hz,hp,hl]
      · have hg : w.length + 1 < p := by omega
        simp only [mixedTape,outputTape,if_neg hz,if_neg hp]
        have hn : p = (p - 2) + 2 := by omega
        have hb := buffer_payload M base w (p - 2)
        rw [←hn] at hb
        rw [hb]
        have h1 : w.length ≤ p - 2 := by omega
        have h2 : w.length ≤ p - 1 := by omega
        rw [List.getD_eq_default (w.map M.bitSym) M.blank (n := p - 2) (by simpa using h1),
          List.getD_eq_default (w.map M.bitSym) M.blank (n := p - 1) (by simpa using h2)]
        simp only [show ¬p - 2 < w.length by omega,show ¬p - 1 < w.length by omega,decide_false]

private theorem output_native (M : MultitapeTM) (base : ℕ → Sym M) (w : List Bool) (h0 : base 0 = none) :
    outputTape M base w = (machine M).tapeOf (w.map (machine M).bitSym) := by
  have h : (machine M).bitSym = fun b => some (M.bitSym b,true) := by
    funext b
    cases b <;> rfl
  funext p
  cases p with
  | zero => simp [outputTape,h0,MultitapeTM.tapeOf]
  | succ p =>
      simp only [outputTape,Nat.succ_ne_zero,if_false,Nat.add_sub_cancel,MultitapeTM.tapeOf]
      by_cases hp : p < w.length
      · rw [List.getD_eq_getElem _ _ (by simpa using hp),List.getElem_map,
          List.getD_eq_getElem _ _ (by simpa using hp),List.getElem_map,h]
        simp [hp]
      · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
        simp [hp]

end IntMul.TrackedOutputShift



namespace IntMul.TrackedOutputShift

open IntMul.TrackedBankedSimulation (Sym)

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

private theorem rewind_rewind_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Sym M)
    (hmarker : a ⟨1,by omega⟩ ≠ some (M.startSym,true)) (hglobal : a ⟨1,by omega⟩ ≠ none) :
    transition M .rewind a = (.rewind,fun i => (a i,if i.val = 1 then .left else .stay)) := by
  classical
  simp only [transition,rawTransition,if_neg hmarker]
  congr 1
  funext i
  by_cases hi : i.val = 1
  · have he : i = ⟨1,by omega⟩ := Fin.ext hi
    simp only [if_pos hi]
    exact rewind_protect_left M _ (by simpa only [he] using hglobal)
  · simp only [if_neg hi,rewind_protect_stay]

private theorem rewind_step (M : MultitapeTM) (base : (machine M).Cfg) (w : List Bool) (p : ℕ) (hp : 1 < p) :
    (machine M).step (rewindFrame M base w p) = rewindFrame M base w (p - 1) := by
  have hm : (rewindFrame M base w p).cells ⟨1,by change 1 < M.k + 2; omega⟩
      ((rewindFrame M base w p).head ⟨1,by change 1 < M.k + 2; omega⟩) ≠ some (M.startSym,true) :=
    buffer_ne_marker M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) w p hp
  have hg : (rewindFrame M base w p).cells ⟨1,by change 1 < M.k + 2; omega⟩
      ((rewindFrame M base w p).head ⟨1,by change 1 < M.k + 2; omega⟩) ≠ none :=
    buffer_nonzero M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) w p (by omega)
  have ht := rewind_rewind_transition M (fun i => (rewindFrame M base w p).cells i ((rewindFrame M base w p).head i)) hm hg
  change transition M (rewindFrame M base w p).state _ = _ at ht
  apply rewind_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    simp only [Function.update_eq_self,rewindFrame]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i.val = 1 <;> simp [rewindFrame,hi]

private theorem rewind_run (M : MultitapeTM) (base : (machine M).Cfg) (w : List Bool) (p : ℕ) :
    (machine M).step^[p] (rewindFrame M base w (p + 1)) = rewindFrame M base w 1 := by
  induction p with
  | zero => rfl
  | succ p ih =>
      rw [Function.iterate_succ_apply,rewind_step M base w (p + 1 + 1) (by omega)]
      simpa only [Nat.add_sub_cancel] using ih

private theorem rewind_marker (M : MultitapeTM) (base : (machine M).Cfg) (w : List Bool) :
    (machine M).step (rewindFrame M base w 1) = readFrame M base w 0 := by
  have hm : (rewindFrame M base w 1).cells ⟨1,by change 1 < M.k + 2; omega⟩
      ((rewindFrame M base w 1).head ⟨1,by change 1 < M.k + 2; omega⟩) = some (M.startSym,true) :=
    buffer_boundary M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) w
  have ht : transition M .rewind
      (fun i => (rewindFrame M base w 1).cells i ((rewindFrame M base w 1).head i)) =
      (.read,fun i => ((rewindFrame M base w 1).cells i ((rewindFrame M base w 1).head i),
        if i.val = 1 then .right else .stay)) := by
    simp only [transition,rawTransition,if_pos hm]
    congr 1
    funext i
    split <;> first | exact rewind_protect_right M _ | exact rewind_protect_stay M _
  change transition M (rewindFrame M base w 1).state _ = _ at ht
  apply rewind_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    simp only [Function.update_eq_self,rewindFrame,readFrame]
    by_cases hi : i.val = 1
    · simp only [if_pos hi]
      exact (mixed_zero M (base.cells i) w).symm
    · simp only [if_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i.val = 1 <;> simp [rewindFrame,readFrame,hi]

private theorem rewind_correct (M : MultitapeTM) (base : (machine M).Cfg) (w : List Bool) :
    (machine M).step^[w.length + 2] (rewindFrame M base w (w.length + 2)) = readFrame M base w 0 := by
  rw [show w.length + 2 = (w.length + 1) + 1 by omega,Function.iterate_succ_apply',rewind_run,rewind_marker]

end IntMul.TrackedOutputShift



namespace IntMul.TrackedOutputShift

open IntMul.TrackedBankedSimulation (Sym)

private theorem bits_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem bits_protect_stay (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .stay = (a,.stay) := by cases a <;> rfl

private theorem bits_protect_right (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .right = (a,.right) := by cases a <;> rfl

private theorem bits_protect_left (M : MultitapeTM) (a : Sym M) (ha : a ≠ none) :
    TrackedBankCleanup.protect M a a .left = (a,.left) := by
  cases a with
  | none => exact False.elim (ha rfl)
  | some s => rfl

private theorem bits_one_ne_zero (M : MultitapeTM) : M.one ≠ M.zero := by
  have h := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at h
  aesop

private theorem bits_read_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Sym M)
    (b : Bool) (source : a ⟨1,by omega⟩ = some (M.bitSym b,true)) :
    transition M .read a = (.write b,fun i => (a i,if i.val = 1 then .left else .stay)) := by
  classical
  have hr : rawTransition M .read a = (.write b,fun i => (a i,if i.val = 1 then .left else .stay)) := by
    dsimp only [rawTransition]
    rw [source]
    cases b <;> simp only [TrackedBankedSimulation.decode,MultitapeTM.bitSym,
      Bool.false_eq_true,if_false,if_true,if_neg (bits_one_ne_zero M)]
  simp only [transition,hr]
  congr 1
  funext i
  by_cases hi : i.val = 1
  · have he : i = ⟨1,by omega⟩ := Fin.ext hi
    simp only [if_pos hi]
    exact bits_protect_left M _ (by rw [he,source]; simp)
  · simp only [if_neg hi,bits_protect_stay]

private theorem read_step (M : MultitapeTM) (base : (machine M).Cfg) (w : List Bool) (j : ℕ) (hj : j < w.length) :
    (machine M).step (readFrame M base w j) = writeFrame M base w j w[j] := by
  have hs : (readFrame M base w j).cells ⟨1,by change 1 < M.k + 2; omega⟩
      ((readFrame M base w j).head ⟨1,by change 1 < M.k + 2; omega⟩) = some (M.bitSym w[j],true) := by
    change mixedTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) w j (j + 2) = _
    rw [mixed_read,List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]
    simp only [hj,decide_true]
  have ht := bits_read_transition M (fun i => (readFrame M base w j).cells i ((readFrame M base w j).head i)) w[j] hs
  change transition M (readFrame M base w j).state _ = _ at ht
  apply bits_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    simp only [Function.update_eq_self,writeFrame]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i.val = 1 <;> simp [readFrame,writeFrame,hi]

private theorem bits_write_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Sym M) (b : Bool)
    (h : a ⟨1,by omega⟩ ≠ none) :
    transition M (.write b) a = (.advance,fun i =>
      (if i.val = 1 then some (M.bitSym b,true) else a i,if i.val = 1 then .right else .stay)) := by
  classical
  simp only [transition,rawTransition]
  congr 1
  funext i
  by_cases hi : i.val = 1
  · have he : i = ⟨1,by omega⟩ := Fin.ext hi
    simp only [if_pos hi]
    have hn : a i ≠ none := by simpa only [he] using h
    cases hs : a i with
    | none => exact False.elim (hn hs)
    | some s => rfl
  · simp only [if_neg hi,bits_protect_stay]

private theorem write_step (M : MultitapeTM) (base : (machine M).Cfg) (w : List Bool) (j : ℕ) (hj : j < w.length) :
    (machine M).step (writeFrame M base w j w[j]) = advanceFrame M base w j := by
  have hn : (writeFrame M base w j w[j]).cells ⟨1,by change 1 < M.k + 2; omega⟩
      ((writeFrame M base w j w[j]).head ⟨1,by change 1 < M.k + 2; omega⟩) ≠ none := by
    change mixedTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) w j (j + 1) ≠ none
    exact mixed_nonzero M _ w j _ (by omega)
  have ht := bits_write_transition M (fun i => (writeFrame M base w j w[j]).cells i ((writeFrame M base w j w[j]).head i)) w[j] hn
  change transition M (writeFrame M base w j w[j]).state _ = _ at ht
  apply bits_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i.val = 1
    · simp only [if_pos hi,writeFrame,readFrame,if_pos hi,advanceFrame]
      exact mixed_write M (base.cells i) w j hj
    · simp only [if_neg hi]
      rw [Function.update_eq_self]
      simp only [writeFrame,readFrame,advanceFrame,if_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i.val = 1 <;> simp [writeFrame,advanceFrame,hi]

private theorem advance_step (M : MultitapeTM) (base : (machine M).Cfg) (w : List Bool) (j : ℕ) :
    (machine M).step (advanceFrame M base w j) = readFrame M base w (j + 1) := by
  have ht : ∀ a, transition M .advance a = (.read,fun i => (a i,if i.val = 1 then .right else .stay)) := by
    intro a
    simp only [transition,rawTransition]
    congr 1
    funext i
    split <;> first | exact bits_protect_right M _ | exact bits_protect_stay M _
  apply bits_cfg_ext
  · simp only [MultitapeTM.step,advanceFrame,ht]
    rfl
  · simp only [MultitapeTM.step,advanceFrame,ht]
    funext i
    simp only [Function.update_eq_self]
  · simp only [MultitapeTM.step,advanceFrame,ht]
    funext i
    by_cases hi : i.val = 1 <;> simp [readFrame,hi]

private theorem shift_bit (M : MultitapeTM) (base : (machine M).Cfg) (w : List Bool) (j : ℕ) (hj : j < w.length) :
    (machine M).step^[3] (readFrame M base w j) = readFrame M base w (j + 1) := by
  rw [Function.iterate_succ_apply',Function.iterate_succ_apply',Function.iterate_succ_apply',
    Function.iterate_zero_apply,read_step M base w j hj,write_step M base w j hj,advance_step]

private theorem shift_run (M : MultitapeTM) (base : (machine M).Cfg) (w : List Bool) (j : ℕ) (hj : j ≤ w.length) :
    (machine M).step^[3 * j] (readFrame M base w 0) = readFrame M base w j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [show 3 * (j + 1) = 3 + 3 * j by omega,Function.iterate_add_apply,ih (by omega),shift_bit M base w j (by omega)]

end IntMul.TrackedOutputShift



namespace IntMul.TrackedOutputShift

open IntMul.TrackedBankedSimulation (Sym)

private theorem complete_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem complete_protect_stay (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .stay = (a,.stay) := by cases a <;> rfl

private theorem complete_protect_left (M : MultitapeTM) (a : Sym M) (ha : a ≠ none) :
    TrackedBankCleanup.protect M a a .left = (a,.left) := by
  cases a with
  | none => exact False.elim (ha rfl)
  | some s => rfl

private theorem complete_blank_ne_zero (M : MultitapeTM) : M.blank ≠ M.zero := by
  have h := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at h
  aesop

private theorem complete_blank_ne_one (M : MultitapeTM) : M.blank ≠ M.one := by
  have h := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at h
  aesop

private theorem complete_read_end_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Sym M)
    (source : a ⟨1,by omega⟩ = some (M.blank,false)) :
    transition M .read a = (.erase,fun i => (a i,if i.val = 1 then .left else .stay)) := by
  classical
  have hr : rawTransition M .read a = (.erase,fun i => (a i,if i.val = 1 then .left else .stay)) := by
    have hz : TrackedBankedSimulation.decode M (a ⟨1,by omega⟩) ≠ M.zero := by
      rw [source]
      exact complete_blank_ne_zero M
    have ho : TrackedBankedSimulation.decode M (a ⟨1,by omega⟩) ≠ M.one := by
      rw [source]
      exact complete_blank_ne_one M
    simp only [rawTransition,if_neg hz,if_neg ho]
  simp only [transition,hr]
  congr 1
  funext i
  by_cases hi : i.val = 1
  · have he : i = ⟨1,by omega⟩ := Fin.ext hi
    simp only [if_pos hi]
    exact complete_protect_left M _ (by rw [he,source]; simp)
  · simp only [if_neg hi,complete_protect_stay]

private theorem read_end (M : MultitapeTM) (base : (machine M).Cfg) (w : List Bool) :
    (machine M).step (readFrame M base w w.length) = eraseFrame M base w := by
  have hs : (readFrame M base w w.length).cells ⟨1,by change 1 < M.k + 2; omega⟩
      ((readFrame M base w w.length).head ⟨1,by change 1 < M.k + 2; omega⟩) = some (M.blank,false) := by
    change mixedTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) w w.length (w.length + 2) = _
    rw [mixed_read,List.getD_eq_default _ _ (by simp)]
    simp
  have ht := complete_read_end_transition M (fun i => (readFrame M base w w.length).cells i
    ((readFrame M base w w.length).head i)) hs
  change transition M (readFrame M base w w.length).state _ = _ at ht
  apply complete_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    simp only [Function.update_eq_self,eraseFrame]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i.val = 1 <;> simp [readFrame,eraseFrame,hi]

private theorem complete_erase_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Sym M)
    (h : a ⟨1,by omega⟩ ≠ none) :
    transition M .erase a = (.halt,fun i => (if i.val = 1 then some (M.blank,false) else a i,.stay)) := by
  classical
  simp only [transition,rawTransition]
  congr 1
  funext i
  by_cases hi : i.val = 1
  · have he : i = ⟨1,by omega⟩ := Fin.ext hi
    simp only [if_pos hi]
    have hn : a i ≠ none := by simpa only [he] using h
    cases hs : a i with
    | none => exact False.elim (hn hs)
    | some s => rfl
  · simp only [if_neg hi,complete_protect_stay]

private theorem erase_end (M : MultitapeTM) (base : (machine M).Cfg) (w : List Bool) :
    (machine M).step (eraseFrame M base w) = finalFrame M base w := by
  have hn : (eraseFrame M base w).cells ⟨1,by change 1 < M.k + 2; omega⟩
      ((eraseFrame M base w).head ⟨1,by change 1 < M.k + 2; omega⟩) ≠ none := by
    change mixedTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) w w.length (w.length + 1) ≠ none
    exact mixed_nonzero M _ w w.length _ (by omega)
  have ht := complete_erase_transition M (fun i => (eraseFrame M base w).cells i ((eraseFrame M base w).head i)) hn
  change transition M (eraseFrame M base w).state _ = _ at ht
  apply complete_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i.val = 1
    · simp only [if_pos hi,eraseFrame,readFrame,if_pos hi,finalFrame]
      exact mixed_erase M (base.cells i) w
    · simp only [if_neg hi]
      rw [Function.update_eq_self]
      simp only [eraseFrame,readFrame,finalFrame,if_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i.val = 1 <;> simp [eraseFrame,finalFrame,hi]

/-- The physically returned buffer is shifted to native output position in
exactly 4*outputLength+4 real transitions, preserving every other tape and
head. The temporary local marker and last duplicate are physically erased. -/
private theorem shift_correct (M : MultitapeTM) (base : (machine M).Cfg) (w : List Bool) :
    (machine M).step^[4 * w.length + 4] (rewindFrame M base w (w.length + 2)) =
      finalFrame M base w := by
  have hr : (machine M).step^[3 * w.length + (w.length + 2)] (rewindFrame M base w (w.length + 2)) =
      readFrame M base w w.length := by
    rw [Function.iterate_add_apply,rewind_correct,shift_run M base w _ le_rfl]
  rw [show 4 * w.length + 4 = (3 * w.length + (w.length + 2)) + 1 + 1 by omega,
    Function.iterate_succ_apply',Function.iterate_succ_apply',hr,read_end,erase_end]

end IntMul.TrackedOutputShift


open IntMul IntMul.TrackedOutputShift

theorem solution (M : MultitapeTM) (base : (machine M).Cfg) (w : List Bool) :
    (machine M).step^[4 * w.length + 4] (rewindFrame M base w (w.length + 2)) =
      finalFrame M base w :=
  IntMul.TrackedOutputShift.shift_correct M base w

#print axioms solution
