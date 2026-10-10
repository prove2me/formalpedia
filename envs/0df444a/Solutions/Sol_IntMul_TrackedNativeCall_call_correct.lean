-- Prove2me | solution 1 for IntMul.TrackedNativeCall.call_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T23:31:16.649177+00:00
-- url     : https://prove2.me/submissions/8f8930d8-5416-4e56-bba5-37f4f8d9b312

import Definitions.Def_IntMul_TrackedNativeCall
import Theorems.Thm_IntMul_TrackedRootInputCopy_copy_correct
import Theorems.Thm_IntMul_TrackedBankedCall_call_correct
import Theorems.Thm_IntMul_TrackedOutputShift_shift_correct
import Mathlib.Data.List.GetD
import Mathlib.Tactic
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents)
open IntMul.TrackedBankPreparation (inputWord initialExtent)


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

private theorem native_output_tape (M : MultitapeTM) (base : ℕ → Sym M) (w : List Bool) (h0 : base 0 = none) :
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



namespace IntMul.TrackedNativeCall

private theorem program_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def startCall (M : MultitapeTM) (c : (TrackedRootInputCopy.machine M).Cfg) :
    (TrackedBankedCall.machine M).Cfg where
  state := .inl .mark
  cells := c.cells
  head := c.head

private noncomputable def startShift (M : MultitapeTM) (c : (TrackedBankedCall.machine M).Cfg) :
    (TrackedOutputShift.machine M).Cfg where
  state := .rewind
  cells := c.cells
  head := c.head

private theorem program_lift_root_step (M : MultitapeTM) (c : (TrackedRootInputCopy.machine M).Cfg)
    (live : c.state ≠ .halt) :
    (machine M).step (liftRoot M c) = liftRoot M ((TrackedRootInputCopy.machine M).step c) := by
  classical
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftRoot,transition,live]
  · simp [MultitapeTM.step,liftRoot,transition,live]
  · simp [MultitapeTM.step,liftRoot,transition,live]

private theorem program_lift_call_step (M : MultitapeTM) (c : (TrackedBankedCall.machine M).Cfg)
    (live : c.state ≠ (TrackedBankedCall.machine M).qHalt) :
    (machine M).step (liftCall M c) = liftCall M ((TrackedBankedCall.machine M).step c) := by
  classical
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftCall,transition,live]
  · simp [MultitapeTM.step,liftCall,transition,live]
  · simp [MultitapeTM.step,liftCall,transition,live]

private theorem lift_shift_step (M : MultitapeTM) (c : (TrackedOutputShift.machine M).Cfg) :
    (machine M).step (liftShift M c) = liftShift M ((TrackedOutputShift.machine M).step c) := by
  classical
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftShift,transition]
  · simp [MultitapeTM.step,liftShift,transition]
  · simp [MultitapeTM.step,liftShift,transition]

private theorem program_lift_root_iterate (M : MultitapeTM) (c : (TrackedRootInputCopy.machine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((TrackedRootInputCopy.machine M).step^[s] c).state ≠ .halt) :
    (machine M).step^[T] (liftRoot M c) = liftRoot M ((TrackedRootInputCopy.machine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
        program_lift_root_step M _ (live T (by omega)),Function.iterate_succ_apply']

private theorem program_lift_call_iterate (M : MultitapeTM) (c : (TrackedBankedCall.machine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((TrackedBankedCall.machine M).step^[s] c).state ≠ (TrackedBankedCall.machine M).qHalt) :
    (machine M).step^[T] (liftCall M c) = liftCall M ((TrackedBankedCall.machine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
        program_lift_call_step M _ (live T (by omega)),Function.iterate_succ_apply']

private theorem lift_shift_iterate (M : MultitapeTM) (c : (TrackedOutputShift.machine M).Cfg) (T : ℕ) :
    (machine M).step^[T] (liftShift M c) = liftShift M ((TrackedOutputShift.machine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,lift_shift_step,Function.iterate_succ_apply']

private theorem program_root_dispatch (M : MultitapeTM) (c : (TrackedRootInputCopy.machine M).Cfg)
    (halt : c.state = .halt) :
    (machine M).step (liftRoot M c) = liftCall M (startCall M c) := by
  classical
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftRoot,liftCall,startCall,transition,halt]
  · funext i
    simp only [MultitapeTM.step,liftRoot,liftCall,startCall,transition,if_pos halt]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,liftRoot,liftCall,startCall,transition,halt]

private theorem program_call_dispatch (M : MultitapeTM) (c : (TrackedBankedCall.machine M).Cfg)
    (halt : c.state = (TrackedBankedCall.machine M).qHalt) :
    (machine M).step (liftCall M c) = liftShift M (startShift M c) := by
  classical
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftCall,liftShift,startShift,transition,halt]
  · funext i
    simp only [MultitapeTM.step,liftCall,liftShift,startShift,transition,if_pos halt]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,liftCall,liftShift,startShift,transition,halt]

private theorem program_halted_step (N : MultitapeTM) (c : N.Cfg) (h : c.state = N.qHalt) : N.step c = c := by
  apply program_cfg_ext
  · simp [MultitapeTM.step,h,N.halt_fixed]
  · funext i
    simp only [MultitapeTM.step,h,N.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,h,N.halt_fixed]

private theorem program_halted_iterate (N : MultitapeTM) (c : N.Cfg) (h : c.state = N.qHalt) (T : ℕ) :
    N.step^[T] c = c := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,program_halted_step N c h]

private theorem program_first_halt (N : MultitapeTM) (c : N.Cfg) (T : ℕ) (h : (N.step^[T] c).state = N.qHalt) :
    ∃ t, t ≤ T ∧ N.step^[t] c = N.step^[T] c ∧ ∀ s, s < t → (N.step^[s] c).state ≠ N.qHalt := by
  classical
  have hex : ∃ t, (N.step^[t] c).state = N.qHalt := ⟨T,h⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex h
  have hh : (N.step^[t] c).state = N.qHalt := Nat.find_spec hex
  refine ⟨t,ht,?_,?_⟩
  · rw [show T = (T - t) + t by omega,Function.iterate_add_apply,program_halted_iterate N _ hh]
  · intro s hs
    exact Nat.find_min hex hs

/-- Child execution stops at its first halt; the full terminal flags and
cells are those of the supplied padded clock, then one dispatch is charged. -/
private theorem run_root_to_call (M : MultitapeTM) (c : (TrackedRootInputCopy.machine M).Cfg) (T : ℕ)
    (halt : ((TrackedRootInputCopy.machine M).step^[T] c).state = .halt) :
    ∃ t, t ≤ T + 1 ∧ (machine M).step^[t] (liftRoot M c) =
      liftCall M (startCall M ((TrackedRootInputCopy.machine M).step^[T] c)) := by
  obtain ⟨t,ht,he,hn⟩ := program_first_halt (TrackedRootInputCopy.machine M) c T halt
  refine ⟨t + 1,by omega,?_⟩
  rw [Function.iterate_succ_apply',program_lift_root_iterate M c t hn,he,program_root_dispatch M _ halt]

/-- Output return likewise dispatches at its first halt, preserving its
entire returned buffer and child banks, including a charged switch step. -/
private theorem run_call_to_shift (M : MultitapeTM) (c : (TrackedBankedCall.machine M).Cfg) (T : ℕ)
    (halt : ((TrackedBankedCall.machine M).step^[T] c).state = (TrackedBankedCall.machine M).qHalt) :
    ∃ t, t ≤ T + 1 ∧ (machine M).step^[t] (liftCall M c) =
      liftShift M (startShift M ((TrackedBankedCall.machine M).step^[T] c)) := by
  obtain ⟨t,ht,he,hn⟩ := program_first_halt (TrackedBankedCall.machine M) c T halt
  refine ⟨t + 1,by omega,?_⟩
  rw [Function.iterate_succ_apply',program_lift_call_iterate M c t hn,he,program_call_dispatch M _ halt]

end IntMul.TrackedNativeCall



namespace IntMul.TrackedNativeCall

open IntMul.TrackedBankedSimulation (Sym)

private theorem frame_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem frame_source_idem (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List M.Sym) :
    TrackedBankPreparation.sourceTape M (TrackedBankPreparation.sourceTape M base sigma w) sigma w =
      TrackedBankPreparation.sourceTape M base sigma w := by
  funext p
  by_cases hp : p < sigma
  · simp only [TrackedBankPreparation.sourceTape,if_pos hp]
  · simp only [TrackedBankPreparation.sourceTape,if_neg hp]

private theorem frame_fresh_native (M : MultitapeTM) :
    TrackedBankPreparation.freshTape M ((TrackedRootInputCopy.machine M).tapeOf []) 1 =
      (TrackedRootInputCopy.machine M).tapeOf [] := by
  funext p
  cases p with
  | zero => rfl
  | succ p => simp [TrackedBankPreparation.freshTape,MultitapeTM.tapeOf]

private theorem frame_root_initial_empty (M : MultitapeTM) (x y : List Bool) (i : Fin (M.k + 2)) (hi : i.val ≠ 0) :
    ((TrackedRootInputCopy.machine M).initCfg x y).cells i = (TrackedRootInputCopy.machine M).tapeOf [] := by
  simp only [MultitapeTM.initCfg]
  rw [if_neg (by intro h; exact hi (congrArg Fin.val h))]

/-- The root input bridge physically produces the complete initial frame
of the interior caller, with all child offsets exactly one. -/
private theorem root_ready (M : MultitapeTM) (x y : List Bool) :
    startCall M (TrackedRootInputCopy.finalFrame M x y) =
      TrackedBankedCall.initialFrame M (callBase M x y) 1 (fun _ => 1) x y := by
  apply frame_cfg_ext
  · rfl
  · funext i
    simp only [startCall,TrackedBankedCall.initialFrame,TrackedBankedCall.liftPreparation,
      TrackedBankPreparation.initialFrame,TrackedBankedCall.preparationBase,callBase]
    by_cases hw : 2 ≤ i.val
    · simp only [dif_pos hw,TrackedRootInputCopy.finalFrame,TrackedRootInputCopy.copyFrame,
        if_neg (by omega : i.val ≠ 1)]
      rw [frame_root_initial_empty M x y i (by omega)]
      exact (frame_fresh_native M).symm
    · simp only [dif_neg hw]
      by_cases hi : i.val = 1
      · simp only [if_pos hi,TrackedRootInputCopy.finalFrame,TrackedRootInputCopy.copyFrame,
          if_pos hi,List.take_length]
        exact (frame_source_idem M _ 1 _).symm
      · simp only [if_neg hi]
  · funext i
    simp only [startCall,TrackedBankedCall.initialFrame,TrackedBankedCall.liftPreparation,
      TrackedBankPreparation.initialFrame,TrackedBankedCall.preparationBase,callBase]
    by_cases hw : 2 ≤ i.val
    · simp only [dif_pos hw,TrackedRootInputCopy.finalFrame,if_neg (by omega : i.val ≠ 0)]
    · simp only [dif_neg hw]
      by_cases hi : i.val = 1
      · simp only [if_pos hi,TrackedRootInputCopy.finalFrame,if_neg (by omega : i.val ≠ 0)]
      · simp only [if_neg hi]

private theorem frame_call_final_buffer (M : MultitapeTM) (base : (TrackedBankedCall.machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    (TrackedBankedCall.finalFrame M base sigma offset extent c w).cells ⟨1,by change 1 < M.k + 2; omega⟩ =
      TrackedOutputReturn.bufferTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma w ∧
      (TrackedBankedCall.finalFrame M base sigma offset extent c w).head ⟨1,by change 1 < M.k + 2; omega⟩ = sigma + w.length + 1 := by
  simp [TrackedBankedCall.finalFrame,TrackedBankedCall.liftCall,TrackedReturnCall.finalFrame,TrackedReturnCall.liftCleanup,
    TrackedBankCleanup.finalFrame,TrackedReturnCall.cleanupBase,TrackedOutputReturn.finalFrame,
    TrackedOutputReturn.copyFrame,TrackedReturnCall.returnBase,TrackedBankedCall.callBase]

/-- Charged dispatch enters the output shift without any free cell rewrite
or head movement: the complete returned buffer is its initial frame. -/
private theorem call_ready (M : MultitapeTM) (base : (TrackedBankedCall.machine M).Cfg)
    (extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    startShift M (TrackedBankedCall.finalFrame M base 1 (fun _ => 1) extent c w) =
      TrackedOutputShift.rewindFrame M
        (shiftBase M (TrackedBankedCall.finalFrame M base 1 (fun _ => 1) extent c w)) w (w.length + 2) := by
  apply frame_cfg_ext
  · rfl
  · funext i
    simp only [startShift,TrackedOutputShift.rewindFrame,shiftBase]
    by_cases hi : i.val = 1
    · simp only [if_pos hi]
      have he : i = ⟨1,by change 1 < M.k + 2; omega⟩ := Fin.ext hi
      rw [he,(frame_call_final_buffer M base 1 (fun _ => 1) extent c w).1]
      funext p
      by_cases hp : p < 1
      · simp only [TrackedOutputReturn.bufferTape,if_pos hp]
      · simp only [TrackedOutputReturn.bufferTape,if_neg hp]
    · simp only [if_neg hi]
  · funext i
    simp only [startShift,TrackedOutputShift.rewindFrame,shiftBase]
    by_cases hi : i.val = 1
    · simp only [if_pos hi]
      have he : i = ⟨1,by change 1 < M.k + 2; omega⟩ := Fin.ext hi
      rw [he,(frame_call_final_buffer M base 1 (fun _ => 1) extent c w).2]
      omega
    · simp only [if_neg hi]

private theorem native_initial (M : MultitapeTM) (x y : List Bool) :
    liftRoot M ((TrackedRootInputCopy.machine M).initCfg x y) = (machine M).initCfg x y := rfl

private theorem frame_work_ge (M : MultitapeTM) (j : Fin M.k) :
    2 ≤ (BankedSimulation.workTape M j).val := by simp [BankedSimulation.workTape]

private theorem frame_inner_work (M : MultitapeTM) (j : Fin M.k)
    (h : 2 ≤ (BankedSimulation.workTape M j).val) :
    BankedSimulation.innerTape M (BankedSimulation.workTape M j) h = j := by
  apply Fin.ext
  simp [BankedSimulation.workTape,BankedSimulation.innerTape]

/-- The entire native output tape, including the global marker and blank
tail, is literal tapeOf w, rather than only a decoded value. -/
private theorem final_output (M : MultitapeTM) (x y : List Bool) (T : ℕ) (w : List Bool) :
    (finalFrame M x y T w).cells (machine M).outTape = (machine M).tapeOf (w.map (machine M).bitSym) := by
  let e := TrackedBankedSimulation.extents M (M.initCfg x y) (TrackedBankPreparation.initialExtent M x y) T
  let d := M.step^[T] (M.initCfg x y)
  let c := TrackedBankedCall.finalFrame M (callBase M x y) 1 (fun _ => 1) e d w
  have h0 : (shiftBase M c).cells ⟨1,by change 1 < M.k + 2; omega⟩ 0 = none := by
    change (TrackedBankedCall.finalFrame M (callBase M x y) 1 (fun _ => 1) e d w).cells
      ⟨1,by change 1 < M.k + 2; omega⟩ 0 = none
    rw [(frame_call_final_buffer M (callBase M x y) 1 (fun _ => 1) e d w).1]
    change ((TrackedRootInputCopy.machine M).initCfg x y).cells
      ⟨1,by change 1 < M.k + 2; omega⟩ 0 = none
    simp only [MultitapeTM.initCfg]
    split <;> rfl
  change TrackedOutputShift.outputTape M ((shiftBase M c).cells ⟨1,by change 1 < M.k + 2; omega⟩) w = _
  exact TrackedOutputShift.native_output_tape M _ w h0

/-- All child work tapes are fresh after output placement and every head is
parked at one; the native output shift uses no additional bank. -/
private theorem final_fresh_banks (M : MultitapeTM) (x y : List Bool) (T : ℕ) (w : List Bool) :
    (∀ j p, 1 ≤ p → (finalFrame M x y T w).cells (BankedSimulation.workTape M j) p = some (M.blank,false)) ∧
    (∀ j, (finalFrame M x y T w).head (BankedSimulation.workTape M j) = 1) := by
  constructor
  · intro j p hp
    simp [finalFrame,liftShift,TrackedOutputShift.finalFrame,shiftBase,
      TrackedBankedCall.finalFrame,TrackedBankedCall.liftCall,TrackedReturnCall.finalFrame,
      TrackedReturnCall.liftCleanup,TrackedBankCleanup.finalFrame,frame_work_ge,frame_inner_work,
      show (BankedSimulation.workTape M j).val ≠ 1 by have := frame_work_ge M j; omega,
      TrackedBankCleanup.freshTape,show ¬p < 1 by omega]
  · intro j
    simp [finalFrame,liftShift,TrackedOutputShift.finalFrame,shiftBase,
      TrackedBankedCall.finalFrame,TrackedBankedCall.liftCall,TrackedReturnCall.finalFrame,
      TrackedReturnCall.liftCleanup,TrackedBankCleanup.finalFrame,frame_work_ge,frame_inner_work,
      show (BankedSimulation.workTape M j).val ≠ 1 by have := frame_work_ge M j; omega]

end IntMul.TrackedNativeCall



namespace IntMul.TrackedNativeCall

open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

/-- One fixed native caller runs the physical input bridge, complete tracked
setup/execution/output/cleanup and native output placement. All transitions
and both outer dispatches are charged; no prepared input is assumed. -/
private theorem run_correct (M : MultitapeTM) (x y : List Bool) (T : ℕ)
    (halt : (M.step^[T] (M.initCfg x y)).state = M.qHalt)
    (w : List Bool) (out : (M.step^[T] (M.initCfg x y)).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    ∃ t, t ≤ T + 5 * span M (extents M (M.initCfg x y) (initialExtent M x y) T) +
        4 * (inputWord M x y).length + 4 * w.length + 24 ∧
      (machine M).step^[t] ((machine M).initCfg x y) = finalFrame M x y T w := by
  have root := TrackedRootInputCopy.copy_correct M x y
  have hh : ((TrackedRootInputCopy.machine M).step^[2 * (inputWord M x y).length + 5]
      ((TrackedRootInputCopy.machine M).initCfg x y)).state = .halt := by
    rw [root]
    rfl
  obtain ⟨p,hp,hprun⟩ := run_root_to_call M ((TrackedRootInputCopy.machine M).initCfg x y)
    (2 * (inputWord M x y).length + 5) hh
  rw [root,root_ready,native_initial] at hprun
  obtain ⟨q,hq,hqrun⟩ := TrackedBankedCall.call_correct M (callBase M x y) 1 (fun _ => 1)
    (by intro j; omega) x y T halt w out
  have hc : ((TrackedBankedCall.machine M).step^[q]
      (TrackedBankedCall.initialFrame M (callBase M x y) 1 (fun _ => 1) x y)).state =
        (TrackedBankedCall.machine M).qHalt := by
    rw [hqrun]
    rfl
  obtain ⟨s,hs,hsrun⟩ := run_call_to_shift M
    (TrackedBankedCall.initialFrame M (callBase M x y) 1 (fun _ => 1) x y) q hc
  rw [hqrun,call_ready] at hsrun
  have shift := TrackedOutputShift.shift_correct M
    (shiftBase M (TrackedBankedCall.finalFrame M (callBase M x y) 1 (fun _ => 1)
      (extents M (M.initCfg x y) (initialExtent M x y) T) (M.step^[T] (M.initCfg x y)) w)) w
  have hsp : (machine M).step^[s + p] ((machine M).initCfg x y) =
      liftShift M (TrackedOutputShift.rewindFrame M
        (shiftBase M (TrackedBankedCall.finalFrame M (callBase M x y) 1 (fun _ => 1)
          (extents M (M.initCfg x y) (initialExtent M x y) T) (M.step^[T] (M.initCfg x y)) w)) w (w.length + 2)) := by
    rw [Function.iterate_add_apply,hprun,hsrun]
  refine ⟨(4 * w.length + 4) + (s + p),by omega,?_⟩
  rw [Function.iterate_add_apply,hsp,lift_shift_iterate,shift]
  rfl

/-- Actual native multiplication-subroutine semantics plus completely
fresh reusable work banks, with coefficient one on the supplied child time. -/
private theorem call_correct (M : MultitapeTM) (x y : List Bool) (T : ℕ)
    (halt : (M.step^[T] (M.initCfg x y)).state = M.qHalt)
    (w : List Bool) (out : (M.step^[T] (M.initCfg x y)).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    ∃ t, t ≤ T + 5 * span M (extents M (M.initCfg x y) (initialExtent M x y) T) +
        4 * (inputWord M x y).length + 4 * w.length + 24 ∧
      (machine M).HaltsWithOutput x y t w ∧
      (∀ j p, 1 ≤ p → ((machine M).step^[t] ((machine M).initCfg x y)).cells (BankedSimulation.workTape M j) p =
        some (M.blank,false)) ∧
      (∀ j, ((machine M).step^[t] ((machine M).initCfg x y)).head (BankedSimulation.workTape M j) = 1) := by
  obtain ⟨t,ht,hr⟩ := run_correct M x y T halt w out
  refine ⟨t,ht,?_,?_,?_⟩
  · unfold MultitapeTM.HaltsWithOutput
    rw [hr]
    exact ⟨rfl,final_output M x y T w⟩
  · rw [hr]
    exact (final_fresh_banks M x y T w).1
  · rw [hr]
    exact (final_fresh_banks M x y T w).2

end IntMul.TrackedNativeCall



open IntMul IntMul.TrackedNativeCall

theorem solution (M : MultitapeTM) (x y : List Bool) (T : ℕ)
    (halt : (M.step^[T] (M.initCfg x y)).state = M.qHalt)
    (w : List Bool) (out : (M.step^[T] (M.initCfg x y)).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    ∃ t, t ≤ T + 5 * span M (extents M (M.initCfg x y) (initialExtent M x y) T) +
        4 * (inputWord M x y).length + 4 * w.length + 24 ∧
      (machine M).HaltsWithOutput x y t w ∧
      (∀ j p, 1 ≤ p → ((machine M).step^[t] ((machine M).initCfg x y)).cells (BankedSimulation.workTape M j) p =
        some (M.blank,false)) ∧
      (∀ j, ((machine M).step^[t] ((machine M).initCfg x y)).head (BankedSimulation.workTape M j) = 1) :=
  IntMul.TrackedNativeCall.call_correct M x y T halt w out

#print axioms solution
