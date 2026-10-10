-- Prove2me | solution 1 for IntMul.TrackedReentrantCall.call_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T23:54:12.138246+00:00
-- url     : https://prove2.me/submissions/8c2a85d1-8adf-4167-b5bf-8c006f7fe2f1

import Definitions.Def_IntMul_TrackedReentrantCall
import Theorems.Thm_IntMul_TrackedBankReservation_reserve_correct
import Theorems.Thm_IntMul_TrackedBankedCall_call_correct
import Theorems.Thm_IntMul_TrackedParentRestore_restore_correct
import Mathlib.Tactic
open IntMul.BankedSimulation (workTape)
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

namespace IntMul.TrackedBankReservation
open IntMul.TrackedBankCleanup (span)
private theorem reentrant_reservation_workspace_bound (M : MultitapeTM) (extent pos : Fin M.k → ℕ) :
    span M (distance M extent pos) + 1 ≤ span M extent + 2 := by
  have h : span M (distance M extent pos) ≤ span M extent + 1 := by
    apply Finset.sup_le
    intro j _
    have hj : extent j ≤ span M extent := Finset.le_sup (Finset.mem_univ j)
    unfold distance
    omega
  omega

end IntMul.TrackedBankReservation

namespace IntMul.TrackedParentRestore
open IntMul.TrackedBankCleanup (span)
private theorem reentrant_restoration_workspace_bound (M : MultitapeTM) (extent : Fin M.k → ℕ) :
    span M (fun j => extent j + 1) + 1 ≤ span M extent + 2 := by
  have h : span M (fun j => extent j + 1) ≤ span M extent + 1 := by
    apply Finset.sup_le
    intro j _
    have hj : extent j ≤ span M extent := Finset.le_sup (Finset.mem_univ j)
    omega
  omega

end IntMul.TrackedParentRestore


namespace IntMul.TrackedReentrantCall

private theorem program_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

noncomputable def startCall (M : MultitapeTM) (c : (TrackedBankReservation.machine M).Cfg) :
    (TrackedBankedCall.machine M).Cfg where
  state := .inl .mark
  cells := c.cells
  head := c.head

noncomputable def startRestore (M : MultitapeTM) (c : (TrackedBankedCall.machine M).Cfg) :
    (TrackedParentRestore.machine M).Cfg where
  state := .rewind
  cells := c.cells
  head := c.head

private theorem program_lift_reservation_step (M : MultitapeTM) (c : (TrackedBankReservation.machine M).Cfg)
    (live : c.state ≠ .halt) :
    (machine M).step (liftReservation M c) = liftReservation M ((TrackedBankReservation.machine M).step c) := by
  classical
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftReservation,transition,live]
  · simp [MultitapeTM.step,liftReservation,transition,live]
  · simp [MultitapeTM.step,liftReservation,transition,live]

private theorem program_lift_call_step (M : MultitapeTM) (c : (TrackedBankedCall.machine M).Cfg)
    (live : c.state ≠ (TrackedBankedCall.machine M).qHalt) :
    (machine M).step (liftCall M c) = liftCall M ((TrackedBankedCall.machine M).step c) := by
  classical
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftCall,transition,live]
  · simp [MultitapeTM.step,liftCall,transition,live]
  · simp [MultitapeTM.step,liftCall,transition,live]

private theorem lift_restore_step (M : MultitapeTM) (c : (TrackedParentRestore.machine M).Cfg) :
    (machine M).step (liftRestore M c) = liftRestore M ((TrackedParentRestore.machine M).step c) := by
  classical
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftRestore,transition]
  · simp [MultitapeTM.step,liftRestore,transition]
  · simp [MultitapeTM.step,liftRestore,transition]

private theorem program_lift_reservation_iterate (M : MultitapeTM) (c : (TrackedBankReservation.machine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((TrackedBankReservation.machine M).step^[s] c).state ≠ .halt) :
    (machine M).step^[T] (liftReservation M c) = liftReservation M ((TrackedBankReservation.machine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
        program_lift_reservation_step M _ (live T (by omega)),Function.iterate_succ_apply']

private theorem program_lift_call_iterate (M : MultitapeTM) (c : (TrackedBankedCall.machine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((TrackedBankedCall.machine M).step^[s] c).state ≠ (TrackedBankedCall.machine M).qHalt) :
    (machine M).step^[T] (liftCall M c) = liftCall M ((TrackedBankedCall.machine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
        program_lift_call_step M _ (live T (by omega)),Function.iterate_succ_apply']

private theorem lift_restore_iterate (M : MultitapeTM) (c : (TrackedParentRestore.machine M).Cfg) (T : ℕ) :
    (machine M).step^[T] (liftRestore M c) = liftRestore M ((TrackedParentRestore.machine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,lift_restore_step,Function.iterate_succ_apply']

private theorem program_reservation_dispatch (M : MultitapeTM) (c : (TrackedBankReservation.machine M).Cfg)
    (halt : c.state = .halt) :
    (machine M).step (liftReservation M c) = liftCall M (startCall M c) := by
  classical
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftReservation,liftCall,startCall,transition,halt]
  · funext i
    simp only [MultitapeTM.step,liftReservation,liftCall,startCall,transition,if_pos halt]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,liftReservation,liftCall,startCall,transition,halt]

private theorem program_call_dispatch (M : MultitapeTM) (c : (TrackedBankedCall.machine M).Cfg)
    (halt : c.state = (TrackedBankedCall.machine M).qHalt) :
    (machine M).step (liftCall M c) = liftRestore M (startRestore M c) := by
  classical
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftCall,liftRestore,startRestore,transition,halt]
  · funext i
    simp only [MultitapeTM.step,liftCall,liftRestore,startRestore,transition,if_pos halt]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,liftCall,liftRestore,startRestore,transition,halt]

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
private theorem run_reservation_to_call (M : MultitapeTM) (c : (TrackedBankReservation.machine M).Cfg) (T : ℕ)
    (halt : ((TrackedBankReservation.machine M).step^[T] c).state = .halt) :
    ∃ t, t ≤ T + 1 ∧ (machine M).step^[t] (liftReservation M c) =
      liftCall M (startCall M ((TrackedBankReservation.machine M).step^[T] c)) := by
  obtain ⟨t,ht,he,hn⟩ := program_first_halt (TrackedBankReservation.machine M) c T halt
  refine ⟨t + 1,by omega,?_⟩
  rw [Function.iterate_succ_apply',program_lift_reservation_iterate M c t hn,he,program_reservation_dispatch M _ halt]

/-- Output return likewise dispatches at its first halt, preserving its
entire returned buffer and child banks, including a charged switch step. -/
private theorem run_call_to_restore (M : MultitapeTM) (c : (TrackedBankedCall.machine M).Cfg) (T : ℕ)
    (halt : ((TrackedBankedCall.machine M).step^[T] c).state = (TrackedBankedCall.machine M).qHalt) :
    ∃ t, t ≤ T + 1 ∧ (machine M).step^[t] (liftCall M c) =
      liftRestore M (startRestore M ((TrackedBankedCall.machine M).step^[T] c)) := by
  obtain ⟨t,ht,he,hn⟩ := program_first_halt (TrackedBankedCall.machine M) c T halt
  refine ⟨t + 1,by omega,?_⟩
  rw [Function.iterate_succ_apply',program_lift_call_iterate M c t hn,he,program_call_dispatch M _ halt]

end IntMul.TrackedReentrantCall



namespace IntMul.TrackedReentrantCall

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)
open IntMul.TrackedBankReservation (newOffsets)

private theorem frame_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem frame_work_ge (M : MultitapeTM) (j : Fin M.k) :
    2 ≤ (workTape M j).val := by simp [workTape]

private theorem frame_inner_work (M : MultitapeTM) (j : Fin M.k) (h : 2 ≤ (workTape M j).val) :
    innerTape M (workTape M j) h = j := by
  apply Fin.ext
  simp [workTape,innerTape]

private theorem frame_work_inner (M : MultitapeTM) (i : Fin (M.k + 2)) (h : 2 ≤ i.val) :
    workTape M (innerTape M i h) = i := by
  apply Fin.ext
  simp only [workTape,innerTape]
  omega

/-- The fresh suffix found by reservation is already present on the actual
parent tape; the child's initial-frame function introduces no cell rewrite. -/
private theorem fresh_reserved (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (tail : ∀ j p, extent j < p → c.cells j p = M.blank) (j : Fin M.k) :
    TrackedBankPreparation.freshTape M ((callBase M base offset extent c).cells (workTape M j))
      (newOffsets M offset extent j) = (callBase M base offset extent c).cells (workTape M j) := by
  funext p
  by_cases hp : p < newOffsets M offset extent j
  · simp only [TrackedBankPreparation.freshTape,if_pos hp]
  · simp only [TrackedBankPreparation.freshTape,if_neg hp]
    have ho : ¬p < offset j := by unfold newOffsets at hp; omega
    have he : extent j < p - offset j := by unfold newOffsets at hp; omega
    simp only [callBase,TrackedBankReservation.finalFrame,TrackedBankedSimulation.embed,
      dif_pos (frame_work_ge M j),frame_inner_work,if_neg ho]
    rw [tail j (p - offset j) he]
    simp only [decide_eq_false_iff_not.mpr (by omega : ¬p - offset j ≤ extent j)]

/-- The charged reservation dispatch enters actual child setup with exactly
the existing cells and heads. The caller must already hold its input buffer. -/
private theorem reservation_ready (M : MultitapeTM) (base : (machine M).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) (x y : List Bool)
    (source : base.cells ⟨1,by change 1 < M.k + 2; omega⟩ =
      TrackedBankPreparation.sourceTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩)
        sigma (TrackedBankPreparation.inputWord M x y))
    (source_head : base.head ⟨1,by change 1 < M.k + 2; omega⟩ = sigma) :
    startCall M (TrackedBankReservation.finalFrame M (reservationBase M base) offset extent c) =
      TrackedBankedCall.initialFrame M (callBase M base offset extent c) sigma
        (newOffsets M offset extent) x y := by
  apply frame_cfg_ext
  · rfl
  · funext i
    simp only [startCall,TrackedBankedCall.initialFrame,TrackedBankedCall.liftPreparation,
      TrackedBankPreparation.initialFrame,TrackedBankedCall.preparationBase]
    by_cases hw : 2 ≤ i.val
    · simp only [dif_pos hw]
      have hf := fresh_reserved M base offset extent c tail (innerTape M i hw)
      rw [frame_work_inner M i hw] at hf
      exact hf.symm
    · simp only [dif_neg hw]
      by_cases hi : i.val = 1
      · simp only [if_pos hi,callBase,TrackedBankReservation.finalFrame,TrackedBankedSimulation.embed,
          dif_neg hw,TrackedBankReservation.parentBase,reservationBase]
        have he : i = ⟨1,by change 1 < M.k + 2; omega⟩ := Fin.ext hi
        rw [he]
        exact source
      · simp only [if_neg hi,callBase]
  · funext i
    simp only [startCall,TrackedBankedCall.initialFrame,TrackedBankedCall.liftPreparation,
      TrackedBankPreparation.initialFrame,TrackedBankedCall.preparationBase]
    by_cases hw : 2 ≤ i.val
    · simp only [dif_pos hw,TrackedBankReservation.finalFrame]
    · simp only [dif_neg hw]
      by_cases hi : i.val = 1
      · simp only [if_pos hi,TrackedBankReservation.finalFrame,dif_neg hw,reservationBase]
        have he : i = ⟨1,by change 1 < M.k + 2; omega⟩ := Fin.ext hi
        rw [he]
        exact source_head
      · simp only [if_neg hi,callBase]

private theorem frame_call_final_work (M : MultitapeTM) (base : (TrackedBankedCall.machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (j : Fin M.k) :
    (TrackedBankedCall.finalFrame M base sigma offset extent c w).cells (workTape M j) =
      TrackedBankPreparation.freshTape M (base.cells (workTape M j)) (offset j) := by
  funext p
  simp only [TrackedBankedCall.finalFrame,TrackedBankedCall.liftCall,TrackedReturnCall.finalFrame,
    TrackedReturnCall.liftCleanup,TrackedBankCleanup.finalFrame,dif_pos (frame_work_ge M j),frame_inner_work,
    TrackedBankCleanup.freshTape,TrackedBankPreparation.freshTape]
  by_cases hp : p < offset j
  · simp only [if_pos hp,TrackedReturnCall.cleanupBase,TrackedOutputReturn.finalFrame,
      TrackedOutputReturn.copyFrame,if_neg (by have := frame_work_ge M j; omega : (workTape M j).val ≠ 1),
      TrackedBankedSimulation.embed,dif_pos (frame_work_ge M j),frame_inner_work,if_pos hp,
      TrackedOutputReturn.callerBase,TrackedReturnCall.returnBase,TrackedBankedCall.callBase]
  · simp only [if_neg hp]

/-- Complete cleanup reinstates the entire parent bank, including its
unvisited tail and all earlier ancestor prefixes. No child marker remains. -/
private theorem child_preserves_parent (M : MultitapeTM) (base : (machine M).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank)
    (x y : List Bool) (T : ℕ) (w : List Bool) (j : Fin M.k) :
    (childFinal M base sigma offset extent c x y T w).cells (workTape M j) =
      (callBase M base offset extent c).cells (workTape M j) := by
  unfold childFinal
  rw [frame_call_final_work,fresh_reserved M base offset extent c tail]

private theorem frame_child_heads (M : MultitapeTM) (base : (machine M).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (x y : List Bool) (T : ℕ) (w : List Bool) (j : Fin M.k) :
    (childFinal M base sigma offset extent c x y T w).head (workTape M j) = newOffsets M offset extent j := by
  simp [childFinal,TrackedBankedCall.finalFrame,TrackedBankedCall.liftCall,TrackedReturnCall.finalFrame,
    TrackedReturnCall.liftCleanup,TrackedBankCleanup.finalFrame,frame_work_ge,frame_inner_work]

/-- After cleanup, actual cells and heads are precisely the parent rewind
frame. The child boundary is reached physically; no head reset is assumed. -/
private theorem child_ready (M : MultitapeTM) (base : (machine M).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank)
    (x y : List Bool) (T : ℕ) (w : List Bool) :
    startRestore M (childFinal M base sigma offset extent c x y T w) =
      TrackedParentRestore.initialFrame M (restoreBase M (childFinal M base sigma offset extent c x y T w))
        offset extent c (fun j => extent j + 1) := by
  apply frame_cfg_ext
  · rfl
  · funext i p
    simp only [startRestore,TrackedParentRestore.initialFrame,TrackedParentRestore.rewindFrame,
      TrackedBankedSimulation.embed,TrackedParentRestore.parentBase,restoreBase]
    by_cases hi : 2 ≤ i.val
    · simp only [dif_pos hi]
      have h := child_preserves_parent M base sigma offset extent c tail x y T w (innerTape M i hi)
      rw [frame_work_inner M i hi] at h
      by_cases hp : p < offset (innerTape M i hi)
      · simp only [if_pos hp]
      · simp only [if_neg hp]
        rw [congrFun h p]
        simp only [callBase,TrackedBankReservation.finalFrame,TrackedBankedSimulation.embed,
          dif_pos hi,if_neg hp]
    · simp only [dif_neg hi]
  · funext i
    simp only [startRestore,TrackedParentRestore.initialFrame,TrackedParentRestore.rewindFrame,
      Nat.sub_zero,restoreBase]
    by_cases hi : 2 ≤ i.val
    · simp only [dif_pos hi]
      have h := frame_child_heads M base sigma offset extent c x y T w (innerTape M i hi)
      rw [frame_work_inner M i hi] at h
      rw [h]
      simp only [newOffsets]
      omega
    · simp only [dif_neg hi]

end IntMul.TrackedReentrantCall



namespace IntMul.TrackedReentrantCall

open IntMul.BankedSimulation (workTape)
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents)
open IntMul.TrackedBankPreparation (inputWord initialExtent)
open IntMul.TrackedBankReservation (newOffsets distance)

/-- A single fixed caller performs actual reservation, physical child setup,
tracked execution, output return, complete cleanup and parent-head rewind.
The only buffer premise describes input already physically produced by the
caller. Every seek and both outer dispatches are included in the clock. -/
private theorem run_correct (M : MultitapeTM) (base : (machine M).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (near : ∀ j, c.head j ≤ extent j + 1)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0)
    (x y : List Bool)
    (source : base.cells ⟨1,by change 1 < M.k + 2; omega⟩ =
      TrackedBankPreparation.sourceTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma (inputWord M x y))
    (source_head : base.head ⟨1,by change 1 < M.k + 2; omega⟩ = sigma)
    (T : ℕ) (halt : (M.step^[T] (M.initCfg x y)).state = M.qHalt)
    (w : List Bool) (out : (M.step^[T] (M.initCfg x y)).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    ∃ t, t ≤ T + 5 * span M (extents M (M.initCfg x y) (initialExtent M x y) T) +
        2 * (inputWord M x y).length + 2 * span M extent + 19 ∧
      (machine M).step^[t] (initialFrame M base offset extent c) =
        finalFrame M base sigma offset extent c x y T w := by
  have reservation := (TrackedBankReservation.reserve_correct M (reservationBase M base) offset extent c near tail).1
  have rhalt : ((TrackedBankReservation.machine M).step^[span M (distance M extent c.head) + 1]
      (TrackedBankReservation.initialFrame M (reservationBase M base) offset extent c)).state = .halt := by
    rw [reservation]
    rfl
  obtain ⟨p,hp,hprun⟩ := run_reservation_to_call M
    (TrackedBankReservation.initialFrame M (reservationBase M base) offset extent c)
    (span M (distance M extent c.head) + 1) rhalt
  rw [reservation,reservation_ready M base sigma offset extent c tail x y source source_head] at hprun
  change (machine M).step^[p] (initialFrame M base offset extent c) = _ at hprun
  obtain ⟨q,hq,hqrun⟩ := TrackedBankedCall.call_correct M (callBase M base offset extent c)
    sigma (newOffsets M offset extent) (by intro j; unfold newOffsets; omega) x y T halt w out
  have chalt : ((TrackedBankedCall.machine M).step^[q]
      (TrackedBankedCall.initialFrame M (callBase M base offset extent c) sigma
        (newOffsets M offset extent) x y)).state = (TrackedBankedCall.machine M).qHalt := by
    rw [hqrun]
    rfl
  obtain ⟨s,hs,hsrun⟩ := run_call_to_restore M
    (TrackedBankedCall.initialFrame M (callBase M base offset extent c) sigma
      (newOffsets M offset extent) x y) q chalt
  change (machine M).step^[s] _ = liftRestore M (startRestore M ((TrackedBankedCall.machine M).step^[q] _)) at hsrun
  rw [hqrun] at hsrun
  change (machine M).step^[s] _ = liftRestore M (startRestore M (childFinal M base sigma offset extent c x y T w)) at hsrun
  rw [child_ready M base sigma offset extent c tail x y T w] at hsrun
  have restoration := (TrackedParentRestore.restore_correct M
    (restoreBase M (childFinal M base sigma offset extent c x y T w)) offset extent c unique (fun j => extent j + 1)).1
  have hsp : (machine M).step^[s + p] (initialFrame M base offset extent c) =
      liftRestore M (TrackedParentRestore.initialFrame M
        (restoreBase M (childFinal M base sigma offset extent c x y T w)) offset extent c (fun j => extent j + 1)) := by
    rw [Function.iterate_add_apply,hprun,hsrun]
  have hrb := TrackedBankReservation.reentrant_reservation_workspace_bound M extent c.head
  have hpb := TrackedParentRestore.reentrant_restoration_workspace_bound M extent
  refine ⟨(span M (fun j => extent j + 1) + 1) + (s + p),by omega,?_⟩
  rw [Function.iterate_add_apply,hsp,lift_restore_iterate,restoration]
  rfl

private theorem complete_work_ge (M : MultitapeTM) (j : Fin M.k) :
    2 ≤ (workTape M j).val := by simp [workTape]

private theorem complete_inner_work (M : MultitapeTM) (j : Fin M.k) (h : 2 ≤ (workTape M j).val) :
    BankedSimulation.innerTape M (workTape M j) h = j := by
  apply Fin.ext
  simp [workTape,BankedSimulation.innerTape]

private theorem final_parent_cells (M : MultitapeTM) (base : (machine M).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank)
    (x y : List Bool) (T : ℕ) (w : List Bool) (j : Fin M.k) :
    (finalFrame M base sigma offset extent c x y T w).cells (workTape M j) =
      (initialFrame M base offset extent c).cells (workTape M j) := by
  have h := congrArg (fun d : (TrackedParentRestore.machine M).Cfg => d.cells (workTape M j))
    (child_ready M base sigma offset extent c tail x y T w)
  change (childFinal M base sigma offset extent c x y T w).cells (workTape M j) =
    (finalFrame M base sigma offset extent c x y T w).cells (workTape M j) at h
  rw [←h,child_preserves_parent M base sigma offset extent c tail x y T w]
  rfl

private theorem final_parent_heads (M : MultitapeTM) (base : (machine M).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (x y : List Bool) (T : ℕ) (w : List Bool) (j : Fin M.k) :
    (finalFrame M base sigma offset extent c x y T w).head (workTape M j) = offset j := by
  simp [finalFrame,liftRestore,TrackedParentRestore.finalFrame,complete_work_ge,complete_inner_work]

/-- Exact child output at the caller's interior boundary, with all parent
work-bank symbols/flags restored and work heads returned to parent markers. -/
private theorem final_buffer (M : MultitapeTM) (base : (machine M).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (x y : List Bool) (T : ℕ) (w : List Bool) :
    (finalFrame M base sigma offset extent c x y T w).cells ⟨1,by change 1 < M.k + 2; omega⟩ =
      TrackedOutputReturn.bufferTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma w ∧
    (finalFrame M base sigma offset extent c x y T w).head ⟨1,by change 1 < M.k + 2; omega⟩ = sigma + w.length + 1 := by
  simp [finalFrame,liftRestore,TrackedParentRestore.finalFrame,TrackedBankedSimulation.embed,
    TrackedParentRestore.parentBase,restoreBase,childFinal,TrackedBankedCall.finalFrame,
    TrackedBankedCall.liftCall,TrackedReturnCall.finalFrame,TrackedReturnCall.liftCleanup,
    TrackedBankCleanup.finalFrame,TrackedReturnCall.cleanupBase,TrackedOutputReturn.finalFrame,
    TrackedOutputReturn.copyFrame,TrackedReturnCall.returnBase,TrackedBankedCall.callBase,
    callBase,TrackedBankReservation.finalFrame,TrackedBankReservation.parentBase,reservationBase]

/-- Complete physical reusable child call with exact parent preservation. -/
private theorem call_correct (M : MultitapeTM) (base : (machine M).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (near : ∀ j, c.head j ≤ extent j + 1)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0)
    (x y : List Bool)
    (source : base.cells ⟨1,by change 1 < M.k + 2; omega⟩ =
      TrackedBankPreparation.sourceTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma (inputWord M x y))
    (source_head : base.head ⟨1,by change 1 < M.k + 2; omega⟩ = sigma)
    (T : ℕ) (halt : (M.step^[T] (M.initCfg x y)).state = M.qHalt)
    (w : List Bool) (out : (M.step^[T] (M.initCfg x y)).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    ∃ t, t ≤ T + 5 * span M (extents M (M.initCfg x y) (initialExtent M x y) T) +
        2 * (inputWord M x y).length + 2 * span M extent + 19 ∧
      (machine M).step^[t] (initialFrame M base offset extent c) =
        finalFrame M base sigma offset extent c x y T w ∧
      (∀ j, ((machine M).step^[t] (initialFrame M base offset extent c)).cells (workTape M j) =
        (initialFrame M base offset extent c).cells (workTape M j)) ∧
      (∀ j, ((machine M).step^[t] (initialFrame M base offset extent c)).head (workTape M j) = offset j) ∧
      ((machine M).step^[t] (initialFrame M base offset extent c)).cells ⟨1,by change 1 < M.k + 2; omega⟩ =
        TrackedOutputReturn.bufferTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma w ∧
      ((machine M).step^[t] (initialFrame M base offset extent c)).head ⟨1,by change 1 < M.k + 2; omega⟩ =
        sigma + w.length + 1 := by
  obtain ⟨t,ht,hr⟩ := run_correct M base sigma offset extent c near tail unique x y source source_head T halt w out
  refine ⟨t,ht,hr,?_,?_,?_,?_⟩
  · rw [hr]
    exact final_parent_cells M base sigma offset extent c tail x y T w
  · rw [hr]
    exact final_parent_heads M base sigma offset extent c x y T w
  · rw [hr]
    exact (final_buffer M base sigma offset extent c x y T w).1
  · rw [hr]
    exact (final_buffer M base sigma offset extent c x y T w).2

end IntMul.TrackedReentrantCall



open IntMul IntMul.TrackedReentrantCall

theorem solution (M : MultitapeTM) (base : (machine M).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (near : ∀ j, c.head j ≤ extent j + 1)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0)
    (x y : List Bool)
    (source : base.cells ⟨1,by change 1 < M.k + 2; omega⟩ =
      TrackedBankPreparation.sourceTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma (inputWord M x y))
    (source_head : base.head ⟨1,by change 1 < M.k + 2; omega⟩ = sigma)
    (T : ℕ) (halt : (M.step^[T] (M.initCfg x y)).state = M.qHalt)
    (w : List Bool) (out : (M.step^[T] (M.initCfg x y)).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    ∃ t, t ≤ T + 5 * span M (extents M (M.initCfg x y) (initialExtent M x y) T) +
        2 * (inputWord M x y).length + 2 * span M extent + 19 ∧
      (machine M).step^[t] (initialFrame M base offset extent c) =
        finalFrame M base sigma offset extent c x y T w ∧
      (∀ j, ((machine M).step^[t] (initialFrame M base offset extent c)).cells (workTape M j) =
        (initialFrame M base offset extent c).cells (workTape M j)) ∧
      (∀ j, ((machine M).step^[t] (initialFrame M base offset extent c)).head (workTape M j) = offset j) ∧
      ((machine M).step^[t] (initialFrame M base offset extent c)).cells ⟨1,by change 1 < M.k + 2; omega⟩ =
        TrackedOutputReturn.bufferTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma w ∧
      ((machine M).step^[t] (initialFrame M base offset extent c)).head ⟨1,by change 1 < M.k + 2; omega⟩ =
        sigma + w.length + 1 :=
  IntMul.TrackedReentrantCall.call_correct M base sigma offset extent c near tail unique x y source source_head T halt w out

#print axioms solution
