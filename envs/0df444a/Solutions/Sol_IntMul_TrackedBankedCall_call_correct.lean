-- Prove2me | solution 1 for IntMul.TrackedBankedCall.call_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T23:04:32.270985+00:00
-- url     : https://prove2.me/submissions/5d02860d-8b61-4858-b607-9819a56fc399

import Definitions.Def_IntMul_TrackedBankedCall
import Theorems.Thm_IntMul_TrackedBankPreparation_setup_correct
import Theorems.Thm_IntMul_TrackedReturnCall_call_correct
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents)
open IntMul.TrackedBankPreparation (inputWord initialExtent)


namespace IntMul.TrackedBankPreparation

open IntMul.TrackedBankedSimulation (extents nextExtent)

private theorem initial_word_letter (M : MultitapeTM) (x y : List Bool) (a : M.Sym)
    (ha : a ∈ inputWord M x y) : a = M.zero ∨ a = M.one ∨ a = M.sep := by
  simp only [inputWord,List.mem_append,List.mem_cons,List.mem_map] at ha
  rcases ha with ⟨b,_,rfl⟩ | (ha | ⟨b,_,rfl⟩)
  · cases b <;> simp [MultitapeTM.bitSym]
  · exact Or.inr (Or.inr ha)
  · cases b <;> simp [MultitapeTM.bitSym]

private theorem initial_word_payload_ne_start (M : MultitapeTM) (x y : List Bool) (p : ℕ) :
    (inputWord M x y).getD p M.blank ≠ M.startSym := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at hd
  by_cases hp : p < (inputWord M x y).length
  · rw [List.getD_eq_getElem _ _ hp]
    have hl := initial_word_letter M x y (inputWord M x y)[p] (List.getElem_mem hp)
    aesop
  · rw [List.getD_eq_default _ _ (by omega)]
    aesop

private theorem banked_initial_unique_markers (M : MultitapeTM) (x y : List Bool) :
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
        have h := initial_word_payload_ne_start M x y p
        simp only [h,Nat.succ_ne_zero]
      · simp only [if_neg hj,MultitapeTM.tapeOf,List.getD_nil]
        have hd := M.syms_distinct
        simp only [List.nodup_cons,List.mem_cons,not_or] at hd
        aesop

private theorem banked_initial_blank_tails (M : MultitapeTM) (x y : List Bool) :
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

private theorem banked_initial_heads_near (M : MultitapeTM) (x y : List Bool) :
    ∀ j, (M.initCfg x y).head j ≤ initialExtent M x y j + 1 := by
  intro j
  simp [MultitapeTM.initCfg]

/-- All tracked extents retain the initial physically prepared prefix. -/
private theorem banked_initial_extent_le_run (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ) (T : ℕ) :
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
private theorem banked_prepared_buffer_near (M : MultitapeTM) (x y : List Bool) (T : ℕ) :
    (inputWord M x y).length + 1 ≤
      TrackedBankCleanup.span M (extents M (M.initCfg x y) (initialExtent M x y) T) + 1 := by
  have hi := banked_initial_extent_le_run M (M.initCfg x y) (initialExtent M x y) T M.inTape
  simp only [initialExtent,if_true] at hi
  have hs : extents M (M.initCfg x y) (initialExtent M x y) T M.inTape ≤
      TrackedBankCleanup.span M (extents M (M.initCfg x y) (initialExtent M x y) T) :=
    Finset.le_sup (Finset.mem_univ M.inTape)
  omega

end IntMul.TrackedBankPreparation



namespace IntMul.TrackedBankedSpace

open IntMul.TrackedBankedSimulation (nextExtent extents)

private theorem space_cfg_ext (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem space_halted_step (M : MultitapeTM) (c : M.Cfg) (halt : c.state = M.qHalt) : M.step c = c := by
  apply space_cfg_ext
  · simp [MultitapeTM.step,halt,M.halt_fixed]
  · funext j
    simp only [MultitapeTM.step,halt,M.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,M.halt_fixed]

private theorem space_blank_tail_step (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    ∀ j p, nextExtent M c extent j < p → (M.step c).cells j p = M.blank := by
  classical
  intro j p hp
  by_cases halt : c.state = M.qHalt
  · rw [space_halted_step M c halt]
    simp only [nextExtent,if_pos halt] at hp
    exact tail j p hp
  · simp only [nextExtent,if_neg halt] at hp
    change Function.update (c.cells j) (c.head j)
      ((M.δ c.state (fun j => c.cells j (c.head j))).2 j).1 p = _
    rw [Function.update_of_ne (by omega : p ≠ c.head j)]
    exact tail j p (by omega)

/-- Blank tails remain blank beyond the tracked extent. This is the explicit
precondition needed to turn a false visited flag into a fresh-bank boundary. -/
private theorem blank_tail_run (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ) (T : ℕ)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    ∀ j p, extents M c extent T j < p → (M.step^[T] c).cells j p = M.blank := by
  induction T with
  | zero => exact tail
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact space_blank_tail_step M _ _ ih

private theorem space_unique_marker_step (M : MultitapeTM) (c : M.Cfg)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0) :
    ∀ j p, (M.step c).cells j p = M.startSym ↔ p = 0 := by
  classical
  intro j p
  change Function.update (c.cells j) (c.head j)
    ((M.δ c.state (fun j => c.cells j (c.head j))).2 j).1 p = M.startSym ↔ p = 0
  by_cases hp : p = c.head j
  · rw [hp,Function.update_self]
    by_cases hz : c.head j = 0
    · have hs := (M.start_preserved c.state (fun j => c.cells j (c.head j)) j ((unique j _).mpr hz)).1
      simp only [hs,hz,iff_true]
    · have hn := M.start_only_at_start c.state (fun j => c.cells j (c.head j)) j
        (mt (unique j _).mp hz)
      simp only [hn,hz,iff_false]
  · rw [Function.update_of_ne hp]
    exact unique j p

/-- Local markers stay unique in every actual child run, so a physical
rewind cannot stop at an interior payload cell. -/
private theorem unique_marker_run (M : MultitapeTM) (c : M.Cfg) (T : ℕ)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0) :
    ∀ j p, (M.step^[T] c).cells j p = M.startSym ↔ p = 0 := by
  induction T with
  | zero => exact unique
  | succ T ih => rw [Function.iterate_succ_apply']; exact space_unique_marker_step M _ ih

private theorem space_head_step_bound (M : MultitapeTM) (c : M.Cfg) (j : Fin M.k) :
    (M.step c).head j ≤ c.head j + 1 := by
  simp only [MultitapeTM.step]
  split <;> omega

private theorem space_near_step (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ)
    (near : ∀ j, c.head j ≤ extent j + 1) :
    ∀ j, (M.step c).head j ≤ nextExtent M c extent j + 1 := by
  classical
  intro j
  by_cases halt : c.state = M.qHalt
  · rw [space_halted_step M c halt]
    simpa only [nextExtent,if_pos halt] using near j
  · simp only [nextExtent,if_neg halt]
    have hh := space_head_step_bound M c j
    have hm := Nat.le_max_right (extent j) (c.head j)
    omega

private theorem heads_near_run (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ) (T : ℕ)
    (near : ∀ j, c.head j ≤ extent j + 1) :
    ∀ j, (M.step^[T] c).head j ≤ extents M c extent T j + 1 := by
  induction T with
  | zero => exact near
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact space_near_step M _ _ ih


end IntMul.TrackedBankedSpace



namespace IntMul.TrackedReturnCall
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents)
private theorem workspace_bit_ne_blank (M : MultitapeTM) (b : Bool) : M.bitSym b ≠ M.blank := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at hd
  cases b <;> simp only [MultitapeTM.bitSym,Bool.false_eq_true,if_false,if_true] <;> aesop

/-- Blank-tail initialization forces every nonblank output bit to lie inside
the tracked extent; output copying therefore does not create a farther head. -/
private theorem output_length_le_extent (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym))
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) : w.length ≤ extent M.outTape := by
  by_contra h
  have hn : 0 < w.length := by omega
  have hj : w.length - 1 < w.length := by omega
  have hb := tail M.outTape w.length (by omega)
  have hv : c.cells M.outTape w.length = M.bitSym w[w.length - 1] := by
    rw [out]
    conv_lhs => rw [show w.length = (w.length - 1) + 1 by omega]
    change (w.map M.bitSym).getD (w.length - 1) M.blank = _
    rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]
  exact workspace_bit_ne_blank M _ (hv.symm.trans hb)

private theorem post_copy_near (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ)
    (w : List Bool) (near : ∀ j, c.head j ≤ extent j + 1)
    (output_extent : w.length ≤ extent M.outTape) :
    ∀ j, postCopyHeads M c w j ≤ extent j + 1 := by
  classical
  intro j
  by_cases hj : j = M.outTape
  · subst j
    simp only [postCopyHeads,if_true]
    omega
  · simp only [postCopyHeads,if_neg hj]
    exact near j

private theorem workspace_space_le (M : MultitapeTM) (f : Fin M.k → ℕ) (j : Fin M.k) :
    f j ≤ span M f := Finset.le_sup (Finset.mem_univ j)

private theorem workspace_space_sup_le (M : MultitapeTM) (f : Fin M.k → ℕ) (n : ℕ)
    (h : ∀ j, f j ≤ n) : span M f ≤ n := Finset.sup_le (by intro j _; exact h j)

/-- The child-time coefficient is one. If the prepared buffer-head distance
is within the final tracked workspace, the entire call costs T+5*space+9. -/
private theorem banked_call_workspace_bounded (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma a : ℕ) (offset extent : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (c : M.Cfg) (T : ℕ) (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank)
    (near : ∀ j, c.head j ≤ extent j + 1)
    (halt : (M.step^[T] c).state = M.qHalt)
    (w : List Bool) (out : (M.step^[T] c).cells M.outTape = M.tapeOf (w.map M.bitSym))
    (buffer_near : a ≤ span M (extents M c extent T) + 1) :
    ∃ t, t ≤ T + 5 * span M (extents M c extent T) + 9 ∧
      (machine M).step^[t] (initialFrame M base sigma a offset extent c) =
        finalFrame M base sigma offset (extents M c extent T) (M.step^[T] c) w := by
  obtain ⟨t,ht,hr⟩ := call_correct M base sigma a offset extent positive c T unique tail near halt w out
  have he := TrackedBankedSpace.heads_near_run M c extent T near
  have htail := TrackedBankedSpace.blank_tail_run M c extent T tail
  have hw := output_length_le_extent M (M.step^[T] c) (extents M c extent T) w out htail
  have hout := workspace_space_le M (extents M c extent T) M.outTape
  have hh := he M.outTape
  have hpost := workspace_space_sup_le M (postCopyHeads M (M.step^[T] c) w) (span M (extents M c extent T) + 1) (by
    intro j
    have hj := post_copy_near M (M.step^[T] c) (extents M c extent T) w he hw j
    have hs := workspace_space_le M (extents M c extent T) j
    exact show postCopyHeads M (M.step^[T] c) w j ≤ span M (extents M c extent T) + 1 by omega)
  exact ⟨t,by omega,hr⟩


end IntMul.TrackedReturnCall


namespace IntMul.TrackedBankedCall

private theorem program_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem program_lift_preparation_step (M : MultitapeTM) (c : (TrackedBankPreparation.machine M).Cfg)
    (live : c.state ≠ .halt) :
    (machine M).step (liftPreparation M c) = liftPreparation M ((TrackedBankPreparation.machine M).step c) := by
  classical
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftPreparation,transition,live]
  · simp [MultitapeTM.step,liftPreparation,transition,live]
  · simp [MultitapeTM.step,liftPreparation,transition,live]

private theorem program_lift_preparation_iterate (M : MultitapeTM) (c : (TrackedBankPreparation.machine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((TrackedBankPreparation.machine M).step^[s] c).state ≠ .halt) :
    (machine M).step^[T] (liftPreparation M c) = liftPreparation M ((TrackedBankPreparation.machine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
        program_lift_preparation_step M _ (live T (by omega)),Function.iterate_succ_apply']

private noncomputable def startCall (M : MultitapeTM) (c : (TrackedBankPreparation.machine M).Cfg) :
    (TrackedReturnCall.machine M).Cfg where
  state := .inl M.qStart
  cells := c.cells
  head := c.head

private theorem lift_call_step (M : MultitapeTM) (c : (TrackedReturnCall.machine M).Cfg) :
    (machine M).step (liftCall M c) = liftCall M ((TrackedReturnCall.machine M).step c) := by
  classical
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftCall,transition]
  · simp [MultitapeTM.step,liftCall,transition]
  · simp [MultitapeTM.step,liftCall,transition]

private theorem lift_call_iterate (M : MultitapeTM) (c : (TrackedReturnCall.machine M).Cfg) (T : ℕ) :
    (machine M).step^[T] (liftCall M c) = liftCall M ((TrackedReturnCall.machine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,lift_call_step,Function.iterate_succ_apply']

private theorem program_preparation_dispatch (M : MultitapeTM) (c : (TrackedBankPreparation.machine M).Cfg)
    (halt : c.state = .halt) :
    (machine M).step (liftPreparation M c) = liftCall M (startCall M c) := by
  classical
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftPreparation,liftCall,startCall,transition,halt]
  · funext i
    simp only [MultitapeTM.step,liftPreparation,liftCall,startCall,transition,if_pos halt]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,liftPreparation,liftCall,startCall,transition,halt]

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

private theorem run_preparation_to_call (M : MultitapeTM) (c : (TrackedBankPreparation.machine M).Cfg) (T : ℕ)
    (halt : ((TrackedBankPreparation.machine M).step^[T] c).state = .halt) :
    ∃ t, t ≤ T + 1 ∧ (machine M).step^[t] (liftPreparation M c) =
      liftCall M (startCall M ((TrackedBankPreparation.machine M).step^[T] c)) := by
  obtain ⟨t,ht,he,hn⟩ := program_first_halt (TrackedBankPreparation.machine M) c T halt
  refine ⟨t + 1,by omega,?_⟩
  rw [Function.iterate_succ_apply',program_lift_preparation_iterate M c t hn,he,program_preparation_dispatch M _ halt]

end IntMul.TrackedBankedCall



namespace IntMul.TrackedBankedCall

private theorem frame_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem frame_empty_tape_eq (M : MultitapeTM) (base : ℕ → TrackedBankedSimulation.Sym M) (sigma : ℕ) :
    TrackedBankPreparation.bankTape M base sigma [] = TrackedOutputReturn.bufferTape M base sigma [] := by
  funext p
  by_cases hp : p < sigma
  · simp [TrackedBankPreparation.bankTape,TrackedOutputReturn.bufferTape,hp]
  · by_cases he : p = sigma
    · subst p
      simp [TrackedBankPreparation.bankTape,TrackedOutputReturn.bufferTape,MultitapeTM.tapeOf]
    · rcases Nat.exists_eq_succ_of_ne_zero (by omega : p - sigma ≠ 0) with ⟨q,hq⟩
      simp [TrackedBankPreparation.bankTape,TrackedOutputReturn.bufferTape,MultitapeTM.tapeOf,hp,he,hq]

private theorem frame_prepared_caller_eq (M : MultitapeTM) (base : (machine M).Cfg) (sigma : ℕ) (x y : List Bool) :
    TrackedBankPreparation.callerBase M (preparationBase M base) sigma x y =
      TrackedReturnCall.childBase M (callBase M base) sigma ((TrackedBankPreparation.inputWord M x y).length + 1) := by
  apply frame_cfg_ext
  · rfl
  · funext i
    simp only [TrackedBankPreparation.callerBase,preparationBase,TrackedReturnCall.childBase,
      TrackedOutputReturn.callerBase,TrackedReturnCall.returnBase,callBase]
    split
    · exact frame_empty_tape_eq M _ sigma
    · rfl
  · funext i
    simp only [TrackedBankPreparation.callerBase,preparationBase,TrackedReturnCall.childBase,
      TrackedOutputReturn.callerBase,TrackedReturnCall.returnBase,callBase]
    split
    · omega
    · rfl

/-- Physical preparation produces exactly the full initial configuration of
our prepared caller, including flags, buffer head and every child head. -/
private theorem preparation_ready (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) :
    startCall M (TrackedBankPreparation.readyFrame M (preparationBase M base) sigma offset x y) =
      TrackedReturnCall.initialFrame M (callBase M base) sigma
        ((TrackedBankPreparation.inputWord M x y).length + 1) offset
        (TrackedBankPreparation.initialExtent M x y) (M.initCfg x y) := by
  apply frame_cfg_ext
  · rfl
  · simp only [startCall,TrackedBankPreparation.readyFrame,TrackedReturnCall.initialFrame,
      TrackedReturnCall.liftChild,frame_prepared_caller_eq]
  · simp only [startCall,TrackedBankPreparation.readyFrame,TrackedReturnCall.initialFrame,
      TrackedReturnCall.liftChild,frame_prepared_caller_eq]

/-- The outer buffer contains the complete returned word with a fresh blank tail. -/
private theorem final_buffer (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    (finalFrame M base sigma offset extent c w).cells ⟨1,by change 1 < M.k + 2; omega⟩ =
      TrackedOutputReturn.bufferTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma w ∧
      (finalFrame M base sigma offset extent c w).head ⟨1,by change 1 < M.k + 2; omega⟩ = sigma + w.length + 1 := by
  simp [finalFrame,liftCall,TrackedReturnCall.finalFrame,TrackedReturnCall.liftCleanup,
    TrackedBankCleanup.finalFrame,TrackedReturnCall.cleanupBase,TrackedOutputReturn.finalFrame,
    TrackedOutputReturn.copyFrame,TrackedReturnCall.returnBase,callBase]

private theorem frame_work_ge (M : MultitapeTM) (j : Fin M.k) :
    2 ≤ (BankedSimulation.workTape M j).val := by simp [BankedSimulation.workTape]

private theorem frame_inner_work (M : MultitapeTM) (j : Fin M.k)
    (h : 2 ≤ (BankedSimulation.workTape M j).val) :
    BankedSimulation.innerTape M (BankedSimulation.workTape M j) h = j := by
  apply Fin.ext
  simp [BankedSimulation.workTape,BankedSimulation.innerTape]

/-- Every child bank is fresh blank at and after its original offset,
including the erased local marker, and every work head is parked there. -/
private theorem final_fresh_banks (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    (∀ j p, offset j ≤ p →
      (finalFrame M base sigma offset extent c w).cells (BankedSimulation.workTape M j) p =
        some (M.blank,false)) ∧
    (∀ j, (finalFrame M base sigma offset extent c w).head (BankedSimulation.workTape M j) = offset j) := by
  constructor
  · intro j p hp
    simp [finalFrame,liftCall,TrackedReturnCall.finalFrame,TrackedReturnCall.liftCleanup,
      TrackedBankCleanup.finalFrame,frame_work_ge,frame_inner_work,TrackedBankCleanup.freshTape,
      show ¬p < offset j by omega]
  · intro j
    simp [finalFrame,liftCall,TrackedReturnCall.finalFrame,TrackedReturnCall.liftCleanup,
      TrackedBankCleanup.finalFrame,frame_work_ge,frame_inner_work]

end IntMul.TrackedBankedCall



namespace IntMul.TrackedBankedCall

open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

/-- The complete physical interior call prepares its child, runs it once,
returns its output and leaves every child bank fresh for reuse. No phase
uses extra tapes, an address oracle, free flag writes or free dispatches. -/
private theorem call_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (x y : List Bool) (T : ℕ) (halt : (M.step^[T] (M.initCfg x y)).state = M.qHalt)
    (w : List Bool) (out : (M.step^[T] (M.initCfg x y)).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    ∃ t, t ≤ T + 5 * span M (extents M (M.initCfg x y) (initialExtent M x y) T) +
        2 * (inputWord M x y).length + 13 ∧
      (machine M).step^[t] (initialFrame M base sigma offset x y) =
        finalFrame M base sigma offset (extents M (M.initCfg x y) (initialExtent M x y) T)
          (M.step^[T] (M.initCfg x y)) w := by
  have setup := TrackedBankPreparation.setup_correct M (preparationBase M base) sigma offset x y
  have hh : ((TrackedBankPreparation.machine M).step^[2 * (inputWord M x y).length + 3]
      (TrackedBankPreparation.initialFrame M (preparationBase M base) sigma offset x y)).state = .halt := by
    rw [setup]
    rfl
  obtain ⟨p,hp,hprun⟩ := run_preparation_to_call M
    (TrackedBankPreparation.initialFrame M (preparationBase M base) sigma offset x y)
    (2 * (inputWord M x y).length + 3) hh
  rw [setup,preparation_ready] at hprun
  obtain ⟨q,hq,hqrun⟩ := TrackedReturnCall.banked_call_workspace_bounded M (callBase M base) sigma
    ((inputWord M x y).length + 1) offset (initialExtent M x y) positive (M.initCfg x y) T
    (TrackedBankPreparation.banked_initial_unique_markers M x y)
    (TrackedBankPreparation.banked_initial_blank_tails M x y)
    (TrackedBankPreparation.banked_initial_heads_near M x y) halt w out
    (TrackedBankPreparation.banked_prepared_buffer_near M x y T)
  refine ⟨q + p,by omega,?_⟩
  change (machine M).step^[q + p]
    (liftPreparation M (TrackedBankPreparation.initialFrame M (preparationBase M base) sigma offset x y)) = _
  rw [Function.iterate_add_apply,hprun,lift_call_iterate,hqrun]
  rfl

end IntMul.TrackedBankedCall


open IntMul IntMul.TrackedBankedCall

theorem solution (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (x y : List Bool) (T : ℕ) (halt : (M.step^[T] (M.initCfg x y)).state = M.qHalt)
    (w : List Bool) (out : (M.step^[T] (M.initCfg x y)).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    ∃ t, t ≤ T + 5 * span M (extents M (M.initCfg x y) (initialExtent M x y) T) +
        2 * (inputWord M x y).length + 13 ∧
      (machine M).step^[t] (initialFrame M base sigma offset x y) =
        finalFrame M base sigma offset (extents M (M.initCfg x y) (initialExtent M x y) T)
          (M.step^[T] (M.initCfg x y)) w :=
  IntMul.TrackedBankedCall.call_correct M base sigma offset positive x y T halt w out

#print axioms solution
