-- Prove2me | solution 1 for IntMul.EndParkRecursiveScheduler.body_root_quiet
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T05:33:38.882218+00:00
-- url     : https://prove2.me/submissions/f67e7e13-6fd3-478c-ac1f-b3336078fefc

import Definitions.Def_IntMul_EndParkRecursiveExecution
import Mathlib.Tactic

namespace IntMul.EndParkRecursiveScheduler

private def postBoot {M : MultitapeTM} {n : ℕ} : State M n → Prop
  | .boot _ => False
  | _ => True

private theorem post_boot_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (q : State M n) (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M)
    (after_boot : postBoot q) : postBoot (transition M n request resume q a).1 := by
  classical
  cases q <;> simp only [postBoot] at after_boot
  all_goals try contradiction
  all_goals simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false]
  all_goals repeat' (first | exact True.intro | split_ifs | split)

private theorem root_protect (M : MultitapeTM) (a : TrackedBankedSimulation.Sym M) :
    TrackedBankCleanup.protect M a a Move.stay=(a,Move.stay) := by cases a <;> rfl

private theorem preparation_root (M : MultitapeTM) (s : TrackedBankPreparation.State)
    (a : Fin (M.k+2) → TrackedBankedSimulation.Sym M) :
    (TrackedBankPreparation.transition M s a).2 ⟨0,by omega⟩=(a ⟨0,by omega⟩,Move.stay) := by
  classical
  cases s
  all_goals simp only [TrackedBankPreparation.transition,TrackedBankPreparation.rawTransition]
  all_goals try split_ifs
  all_goals try simp only [root_protect]
  all_goals try rfl
  all_goals simp_all [root_protect,BankedSimulation.workTape,MultitapeTM.outTape,TrackedChildInputBridge.bufferTape,TrackedChildInputBridge.packetTape,TrackedParentOutputBridge.bufferTape,TrackedParentOutputBridge.targetTape,TrackedWordInputBridge.bufferTape,TrackedWordInputBridge.packetTape,Fin.ext_iff]

private theorem input_root (M : MultitapeTM) (s : TrackedChildInputBridge.State)
    (a : Fin (M.k+2) → TrackedBankedSimulation.Sym M) :
    (TrackedChildInputBridge.transition M s a).2 ⟨0,by omega⟩=(a ⟨0,by omega⟩,Move.stay) := by
  classical
  cases s
  all_goals simp only [TrackedChildInputBridge.transition,TrackedChildInputBridge.rawTransition]
  all_goals try split_ifs
  all_goals try simp only [root_protect]
  all_goals try rfl
  all_goals simp_all [root_protect,BankedSimulation.workTape,MultitapeTM.outTape,TrackedChildInputBridge.bufferTape,TrackedChildInputBridge.packetTape,TrackedParentOutputBridge.bufferTape,TrackedParentOutputBridge.targetTape,TrackedWordInputBridge.bufferTape,TrackedWordInputBridge.packetTape,Fin.ext_iff]

private theorem cleanup_root (M : MultitapeTM) (s : TrackedBankCleanup.State)
    (a : Fin (M.k+2) → TrackedBankedSimulation.Sym M) :
    (TrackedBankCleanup.transition M s a).2 ⟨0,by omega⟩=(a ⟨0,by omega⟩,Move.stay) := by
  classical
  cases s
  all_goals simp only [TrackedBankCleanup.transition,TrackedBankCleanup.rawTransition]
  all_goals try split_ifs
  all_goals try simp only [root_protect]
  all_goals try rfl
  all_goals simp_all [root_protect,BankedSimulation.workTape,MultitapeTM.outTape,TrackedChildInputBridge.bufferTape,TrackedChildInputBridge.packetTape,TrackedParentOutputBridge.bufferTape,TrackedParentOutputBridge.targetTape,TrackedWordInputBridge.bufferTape,TrackedWordInputBridge.packetTape,Fin.ext_iff]

private theorem parent_restore_root (M : MultitapeTM) (s : TrackedParentRestore.State)
    (a : Fin (M.k+2) → TrackedBankedSimulation.Sym M) :
    (TrackedParentRestore.transition M s a).2 ⟨0,by omega⟩=(a ⟨0,by omega⟩,Move.stay) := by
  classical
  cases s
  all_goals simp only [TrackedParentRestore.transition,TrackedParentRestore.rawTransition]
  all_goals try split_ifs
  all_goals try simp only [root_protect]
  all_goals try rfl
  all_goals simp_all [root_protect,BankedSimulation.workTape,MultitapeTM.outTape,TrackedChildInputBridge.bufferTape,TrackedChildInputBridge.packetTape,TrackedParentOutputBridge.bufferTape,TrackedParentOutputBridge.targetTape,TrackedWordInputBridge.bufferTape,TrackedWordInputBridge.packetTape,Fin.ext_iff]

private theorem output_root (M : MultitapeTM) (s : TrackedParentOutputBridge.State)
    (a : Fin (M.k+2) → TrackedBankedSimulation.Sym M) :
    (TrackedParentOutputBridge.transition M s a).2 ⟨0,by omega⟩=(a ⟨0,by omega⟩,Move.stay) := by
  classical
  cases s
  all_goals simp only [TrackedParentOutputBridge.transition,TrackedParentOutputBridge.rawTransition]
  all_goals try split_ifs
  all_goals try simp only [root_protect]
  all_goals try rfl
  all_goals simp_all [root_protect,BankedSimulation.workTape,MultitapeTM.outTape,TrackedChildInputBridge.bufferTape,TrackedChildInputBridge.packetTape,TrackedParentOutputBridge.bufferTape,TrackedParentOutputBridge.targetTape,TrackedWordInputBridge.bufferTape,TrackedWordInputBridge.packetTape,Fin.ext_iff]

private theorem finish_root (M : MultitapeTM) (s : TrackedOutputShift.State)
    (a : Fin (M.k+2) → TrackedBankedSimulation.Sym M) :
    (TrackedOutputShift.transition M s a).2 ⟨0,by omega⟩=(a ⟨0,by omega⟩,Move.stay) := by
  classical
  cases s
  all_goals simp only [TrackedOutputShift.transition,TrackedOutputShift.rawTransition]
  all_goals try split_ifs
  all_goals try simp only [root_protect]
  all_goals try rfl
  all_goals simp_all [root_protect,BankedSimulation.workTape,MultitapeTM.outTape,TrackedChildInputBridge.bufferTape,TrackedChildInputBridge.packetTape,TrackedParentOutputBridge.bufferTape,TrackedParentOutputBridge.targetTape,TrackedWordInputBridge.bufferTape,TrackedWordInputBridge.packetTape,Fin.ext_iff]

private theorem word_root (M : MultitapeTM) (s : TrackedWordInputBridge.State)
    (a : Fin (M.k+2) → TrackedBankedSimulation.Sym M) :
    (TrackedWordInputBridge.transition M s a).2 ⟨0,by omega⟩=(a ⟨0,by omega⟩,Move.stay) := by
  classical
  cases s
  all_goals simp only [TrackedWordInputBridge.transition,TrackedWordInputBridge.rawTransition]
  all_goals try split_ifs
  all_goals try simp only [root_protect]
  all_goals try rfl
  all_goals simp_all [root_protect,BankedSimulation.workTape,MultitapeTM.outTape,TrackedChildInputBridge.bufferTape,TrackedChildInputBridge.packetTape,TrackedParentOutputBridge.bufferTape,TrackedParentOutputBridge.targetTape,TrackedWordInputBridge.bufferTape,TrackedWordInputBridge.packetTape,Fin.ext_iff]

private theorem reservation_root (M : MultitapeTM) (s : TrackedBankReservation.State)
    (a : Fin (M.k+2) → TrackedBankedSimulation.Sym M) :
    (TrackedBankReservation.transition M s a).2 ⟨0,by omega⟩=(a ⟨0,by omega⟩,Move.stay) := by
  classical
  cases s
  all_goals simp only [TrackedBankReservation.transition]
  all_goals try split_ifs
  all_goals try simp only [root_protect]
  all_goals try rfl
  all_goals simp_all [root_protect,BankedSimulation.workTape,MultitapeTM.outTape,TrackedChildInputBridge.bufferTape,TrackedChildInputBridge.packetTape,TrackedParentOutputBridge.bufferTape,TrackedParentOutputBridge.targetTape,TrackedWordInputBridge.bufferTape,TrackedWordInputBridge.packetTape,Fin.ext_iff]

private theorem body_root (M : MultitapeTM) (q : M.K)
    (a : Fin (M.k+2) → TrackedBankedSimulation.Sym M) :
    (TrackedBankedSimulation.transition M q a).2 ⟨0,by omega⟩=(a ⟨0,by omega⟩,Move.stay) := by
  classical
  by_cases hq : q=M.qHalt <;> simp [TrackedBankedSimulation.transition,hq]

private theorem stack_root (M : MultitapeTM) (n : ℕ) (q : FiniteContinuationStack.State n)
    (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M) :
    (FiniteContinuationStack.transition M n q a).2 ⟨0,by omega⟩=(a ⟨0,by omega⟩,Move.stay) := by
  classical
  cases q
  all_goals simp only [FiniteContinuationStack.transition,FiniteContinuationStack.rawTransition]
  all_goals try split_ifs
  all_goals simp_all [root_protect,FiniteContinuationStack.stackTape,Fin.ext_iff]

private theorem selective_root (M : MultitapeTM) (active : Fin M.k → Bool)
    (q : TrackedSelectiveParentRestore.State) (a : Fin (M.k+2) → TrackedBankedSimulation.Sym M) :
    (TrackedSelectiveParentRestore.transition M active q a).2 ⟨0,by omega⟩=(a ⟨0,by omega⟩,Move.stay) := by
  classical
  cases q
  all_goals simp only [TrackedSelectiveParentRestore.transition,TrackedSelectiveParentRestore.rawTransition]
  all_goals try split_ifs
  all_goals simp_all [root_protect]

private theorem return_root (M : MultitapeTM) (q : TrackedReturnReplacement.State)
    (a : Fin (M.k+2) → TrackedBankedSimulation.Sym M) :
    (TrackedReturnReplacement.transition M q a).2 ⟨0,by omega⟩=(a ⟨0,by omega⟩,Move.stay) := by
  classical
  cases q with
  | inl q =>
    simp only [TrackedReturnReplacement.transition]
    split_ifs
    all_goals try (exact word_root M q a)
    all_goals simp_all [word_root,TrackedReturnReplacement.sealActions,
      TrackedReturnReplacement.bufferTape,TrackedWordInputBridge.bufferTape,root_protect,Fin.ext_iff]
  | inr b =>
    cases b <;> simp only [TrackedReturnReplacement.transition]
    all_goals try split_ifs
    all_goals simp_all [TrackedReturnReplacement.seekActions,
      TrackedReturnReplacement.bufferTape,TrackedWordInputBridge.bufferTape,root_protect,Fin.ext_iff]

private theorem padded_root (N : MultitapeTM)
    (fixed : ∀ q a, (N.δ q a).2 N.inTape=(a N.inTape,Move.stay))
    (q : N.K) (a : Fin (N.k+1) → N.Sym) :
    (FixedTapeExtension.transition N q a).2 ⟨0,by omega⟩=(a ⟨0,by omega⟩,Move.stay) := by
  have h0 : (0:ℕ)< N.k := by have := N.two_le_k; omega
  simp only [FixedTapeExtension.transition,dif_pos h0,FixedTapeExtension.innerTape]
  exact fixed q _

private theorem preparation_padded_root (M : MultitapeTM) (q : (TrackedBankPreparation.machine M).K)
    (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M) :
    (FixedTapeExtension.transition (TrackedBankPreparation.machine M) q a).2 ⟨0,by change 0< M.k+3; omega⟩=(a ⟨0,by change 0< M.k+3; omega⟩,Move.stay) := by
  apply padded_root (TrackedBankPreparation.machine M)
  intro q a
  exact preparation_root M q a

private theorem input_padded_root (M : MultitapeTM) (q : (TrackedChildInputBridge.machine M).K)
    (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M) :
    (FixedTapeExtension.transition (TrackedChildInputBridge.machine M) q a).2 ⟨0,by change 0< M.k+3; omega⟩=(a ⟨0,by change 0< M.k+3; omega⟩,Move.stay) := by
  apply padded_root (TrackedChildInputBridge.machine M)
  intro q a
  exact input_root M q a

private theorem cleanup_padded_root (M : MultitapeTM) (q : (TrackedBankCleanup.machine M).K)
    (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M) :
    (FixedTapeExtension.transition (TrackedBankCleanup.machine M) q a).2 ⟨0,by change 0< M.k+3; omega⟩=(a ⟨0,by change 0< M.k+3; omega⟩,Move.stay) := by
  apply padded_root (TrackedBankCleanup.machine M)
  intro q a
  exact cleanup_root M q a

private theorem parent_restore_padded_root (M : MultitapeTM) (q : (TrackedParentRestore.machine M).K)
    (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M) :
    (FixedTapeExtension.transition (TrackedParentRestore.machine M) q a).2 ⟨0,by change 0< M.k+3; omega⟩=(a ⟨0,by change 0< M.k+3; omega⟩,Move.stay) := by
  apply padded_root (TrackedParentRestore.machine M)
  intro q a
  exact parent_restore_root M q a

private theorem output_padded_root (M : MultitapeTM) (q : (TrackedParentOutputBridge.machine M).K)
    (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M) :
    (FixedTapeExtension.transition (TrackedParentOutputBridge.machine M) q a).2 ⟨0,by change 0< M.k+3; omega⟩=(a ⟨0,by change 0< M.k+3; omega⟩,Move.stay) := by
  apply padded_root (TrackedParentOutputBridge.machine M)
  intro q a
  exact output_root M q a

private theorem finish_padded_root (M : MultitapeTM) (q : (TrackedOutputShift.machine M).K)
    (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M) :
    (FixedTapeExtension.transition (TrackedOutputShift.machine M) q a).2 ⟨0,by change 0< M.k+3; omega⟩=(a ⟨0,by change 0< M.k+3; omega⟩,Move.stay) := by
  apply padded_root (TrackedOutputShift.machine M)
  intro q a
  exact finish_root M q a

private theorem reservation_padded_root (M : MultitapeTM) (q : (TrackedBankReservation.machine M).K)
    (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M) :
    (FixedTapeExtension.transition (TrackedBankReservation.machine M) q a).2 ⟨0,by change 0< M.k+3; omega⟩=(a ⟨0,by change 0< M.k+3; omega⟩,Move.stay) := by
  apply padded_root (TrackedBankReservation.machine M)
  intro q a
  exact reservation_root M q a

private theorem body_padded_root (M : MultitapeTM) (q : (TrackedBankedSimulation.machine M).K)
    (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M) :
    (FixedTapeExtension.transition (TrackedBankedSimulation.machine M) q a).2 ⟨0,by change 0< M.k+3; omega⟩=(a ⟨0,by change 0< M.k+3; omega⟩,Move.stay) := by
  apply padded_root (TrackedBankedSimulation.machine M)
  intro q a
  exact body_root M q a

private theorem return_padded_root (M : MultitapeTM) (q : (TrackedReturnReplacement.machine M).K)
    (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M) :
    (FixedTapeExtension.transition (TrackedReturnReplacement.machine M) q a).2 ⟨0,by change 0< M.k+3; omega⟩=(a ⟨0,by change 0< M.k+3; omega⟩,Move.stay) := by
  apply padded_root (TrackedReturnReplacement.machine M)
  intro q a
  exact return_root M q a

private theorem selective_padded_root (M : MultitapeTM) (q : TrackedSelectiveParentRestore.State)
    (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M) :
    (FixedTapeExtension.transition (TrackedSelectiveParentRestore.machine M (EndParkResume.active M)) q a).2 ⟨0,by change 0< M.k+3; omega⟩=(a ⟨0,by change 0< M.k+3; omega⟩,Move.stay) := by
  apply padded_root (TrackedSelectiveParentRestore.machine M (EndParkResume.active M))
  intro q a
  exact selective_root M _ q a

private theorem buffer_move_root (M : MultitapeTM) (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M)
    (move : Move) :
    (FlatRecursiveScheduler.moveActions M a (FlatRecursiveScheduler.bufferTape M) move) ⟨0,by omega⟩=
      (a ⟨0,by omega⟩,Move.stay) := by
  simp [FlatRecursiveScheduler.moveActions,FlatRecursiveScheduler.bufferTape,root_protect,Fin.ext_iff]

private theorem stack_move_root (M : MultitapeTM) (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M)
    (move : Move) :
    (FlatRecursiveScheduler.moveActions M a (FlatRecursiveScheduler.stackTape M) move) ⟨0,by omega⟩=
      (a ⟨0,by omega⟩,Move.stay) := by
  simp [FlatRecursiveScheduler.moveActions,FlatRecursiveScheduler.stackTape,
    FiniteContinuationStack.stackTape,root_protect,Fin.ext_iff]

private theorem post_boot_root_action (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (q : State M n) (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M)
    (after_boot : postBoot q) :
    (transition M n request resume q a).2 ⟨0,by omega⟩=(a ⟨0,by omega⟩,Move.stay) := by
  classical
  cases q <;> simp only [postBoot] at after_boot
  all_goals try contradiction
  all_goals simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false]
  all_goals try split_ifs
  all_goals try simp only [preparation_padded_root,input_padded_root,cleanup_padded_root,
    parent_restore_padded_root,output_padded_root,finish_padded_root,reservation_padded_root,
    body_padded_root,return_padded_root,selective_padded_root,stack_root,buffer_move_root,stack_move_root]
  all_goals repeat' (first | rfl | (simp only [preparation_padded_root,input_padded_root,cleanup_padded_root,parent_restore_padded_root,output_padded_root,finish_padded_root,reservation_padded_root,body_padded_root,return_padded_root,selective_padded_root,stack_root,buffer_move_root,stack_move_root]; done) | split_ifs | split)

private theorem post_boot_run (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (initial : postBoot c.state) (t : ℕ) :
    postBoot ((machine M n request resume).step^[t] c).state := by
  induction t with
  | zero => exact initial
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact post_boot_step M n request resume _ _ ih

/-- Every actual transition after body entry freezes the outer input head. -/
private theorem body_root_quiet (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) (t : ℕ) :
    let d := (machine M n request resume).step^[t]
      (bodyFrame M n request resume base rho sigma offset extent c v)
    (((machine M n request resume).δ d.state (fun i => d.cells i (d.head i))).2
      (machine M n request resume).inTape).2=Move.stay := by
  change ((transition M n request resume _ _).2 ⟨0,by omega⟩).2=Move.stay
  exact congrArg Prod.snd (post_boot_root_action M n request resume _ _
    (post_boot_run M n request resume _ (by exact True.intro) t))

end IntMul.EndParkRecursiveScheduler


open IntMul IntMul.EndParkRecursiveScheduler

theorem solution (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) (t : ℕ) :
    let d := (machine M n request resume).step^[t]
      (bodyFrame M n request resume base rho sigma offset extent c v)
    (((machine M n request resume).δ d.state (fun i => d.cells i (d.head i))).2
      (machine M n request resume).inTape).2=Move.stay :=
  IntMul.EndParkRecursiveScheduler.body_root_quiet M n request resume base rho sigma offset extent c v t

#print axioms solution
