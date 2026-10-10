-- Prove2me | solution 1 for IntMul.EndParkRecursiveScheduler.resume_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T03:56:49.63637+00:00
-- url     : https://prove2.me/submissions/39503b3e-27d0-47d8-936c-bb15b5bde6c6

import Definitions.Def_IntMul_EndParkRecursiveScheduler
import Theorems.Thm_IntMul_EndParkResume_resume_correct
import Mathlib.Tactic

namespace IntMul.EndParkRecursiveScheduler

private theorem end_park_recursive_internal_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem end_park_recursive_internal_fixed_iterate (N : MultitapeTM) (c : N.Cfg) (fixed : N.step c=c) (T : ℕ) :
    N.step^[T] c=c := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,fixed]

private theorem end_park_recursive_internal_halted_step (N : MultitapeTM) (c : N.Cfg) (halt : c.state=N.qHalt) : N.step c=c := by
  apply end_park_recursive_internal_cfg_ext
  · simp [MultitapeTM.step,halt,N.halt_fixed]
  · funext i
    simp only [MultitapeTM.step,halt,N.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,N.halt_fixed]

/-- First entry to any family of quiescent service exits preserves the exact
complete supplied terminal configuration, including all tape heads. -/
private theorem end_park_recursive_internal_first_exit (N : MultitapeTM) (P : N.K → Prop)
    (fixed : ∀ d : N.Cfg, P d.state → N.step d=d) (c : N.Cfg) (T : ℕ)
    (exit : P (N.step^[T] c).state) :
    ∃ t, t≤ T ∧ N.step^[t] c=N.step^[T] c ∧ ∀ s, s< t → ¬P (N.step^[s] c).state := by
  classical
  have hex : ∃ t, P (N.step^[t] c).state := ⟨T,exit⟩
  let t := Nat.find hex
  have ht : t≤ T := Nat.find_min' hex exit
  have hp : P (N.step^[t] c).state := Nat.find_spec hex
  refine ⟨t,ht,?_,?_⟩
  · rw [show T=(T-t)+t by omega,Function.iterate_add_apply,end_park_recursive_internal_fixed_iterate N _ (fixed _ hp)]
  · intro s hs
    exact Nat.find_min hex hs

/-- Every actual return-service transition is the corresponding transition
of the complete scheduler, until its recovered body continuation is entered. -/
private theorem end_park_recursive_internal_resume_transition (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (q : EndParkResume.State n) (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M)
    (live : ∀ label, q≠.ready label) :
    transition M n request resume (resumeControl M n resume q) a =
      (resumeControl M n resume (EndParkResume.transition M n q a).1,
        (EndParkResume.transition M n q a).2) := by
  classical
  cases q with
  | restore s =>
    cases s <;> simp only [transition,resumeControl,restoreControl,
      EndParkResume.transition,FlatRecursiveScheduler.transition,
      FlatRecursiveScheduler.State.restore.injEq,reduceCtorEq,if_true,if_false]
    all_goals rfl
  | pop s =>
    cases s <;> simp only [transition,resumeControl,EndParkResume.transition,
      FlatRecursiveScheduler.transition,reduceCtorEq,if_false]
    all_goals rfl
  | output label s =>
    simp only [transition,resumeControl,reduceCtorEq,if_false,
      EndParkResume.transition,FlatRecursiveScheduler.transition]
    by_cases h : s=(EndParkResume.outputMachine M).qHalt
    · simp only [h,if_true,resumeControl]
    · simp only [if_neg h]
  | ready label => exact False.elim (live label rfl)
  | halt =>
    simp only [transition,resumeControl,EndParkResume.transition,
      FlatRecursiveScheduler.transition,reduceCtorEq,if_false]

private theorem end_park_recursive_internal_resume_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (EndParkResume.machine M n).Cfg) (live : ∀ label, c.state≠.ready label) :
    (machine M n request resume).step (liftResume M n request resume c)=
      liftResume M n request resume ((EndParkResume.machine M n).step c) := by
  have ht := end_park_recursive_internal_resume_transition M n request resume c.state (fun i => c.cells i (c.head i)) live
  apply end_park_recursive_internal_cfg_ext
  · simp only [MultitapeTM.step,liftResume,ht]
  · simp only [MultitapeTM.step,liftResume,ht]
  · simp only [MultitapeTM.step,liftResume,ht]

private theorem end_park_recursive_internal_resume_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (EndParkResume.machine M n).Cfg) (T : ℕ)
    (live : ∀ s, s< T → ∀ label, ((EndParkResume.machine M n).step^[s] c).state≠.ready label) :
    (machine M n request resume).step^[T] (liftResume M n request resume c)=
      liftResume M n request resume ((EndParkResume.machine M n).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      end_park_recursive_internal_resume_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem end_park_recursive_internal_ready_fixed (M : MultitapeTM) (n : ℕ)
    (c : (EndParkResume.machine M n).Cfg) (label : Fin n) (ready : c.state=.ready label) :
    (EndParkResume.machine M n).step c=c := by
  apply end_park_recursive_internal_cfg_ext
  · simp [MultitapeTM.step,ready,EndParkResume.transition]
  · funext i
    simp only [MultitapeTM.step,ready,EndParkResume.transition]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,ready,EndParkResume.transition]

/-- The complete recursive table physically restores only the result head,
recovers its finite continuation, erases the stack record and places the
child result. It then executes the real body resume control. Untouched work
heads stay at their retained bank ends and do not contribute to this clock. -/
private theorem resume_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (EndParkResume.machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ p, extent M.outTape < p → c.cells M.outTape p=M.blank) :
    ∃ t, t≤ extent M.outTape+n+w.length+2*max w.length (extent M.outTape)+12 ∧
      (machine M n request resume).step^[t]
        (initialFrame M n request resume base rho sigma offset extent c label w)=
        finalFrame M n request resume base rho sigma offset extent c label w ∧
      (finalFrame M n request resume base rho sigma offset extent c label w).state=.body (resume label) ∧
      (∀ j, (finalFrame M n request resume base rho sigma offset extent c label w).head
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (BankedSimulation.workTape M j))=
        offset j+(if j=M.outTape then 0 else extent j+1)) ∧
      (∀ p, (finalFrame M n request resume base rho sigma offset extent c label w).cells
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (BankedSimulation.workTape M M.outTape))
        (offset M.outTape+p)=some (M.tapeOf (w.map M.bitSym) p,decide (p≤ w.length))) ∧
      (finalFrame M n request resume base rho sigma offset extent c label w).cells (FiniteContinuationStack.stackTape M)=
        FiniteContinuationStack.freshTape M (base.cells (FiniteContinuationStack.stackTape M)) rho ∧
      (finalFrame M n request resume base rho sigma offset extent c label w).head (FiniteContinuationStack.stackTape M)=rho := by
  obtain ⟨T,hT,hRun,hState,hHeads,hCells,hStack,hStackHead⟩ :=
    EndParkResume.resume_correct M n base rho sigma offset extent c label w unique tail
  let start := EndParkResume.initialFrame M n base rho sigma offset extent c label w
  have hReady : ∃ q, ((EndParkResume.machine M n).step^[T] start).state=.ready q := by
    rw [hRun]
    exact ⟨label,hState⟩
  obtain ⟨t,ht,he,hlive⟩ := end_park_recursive_internal_first_exit (EndParkResume.machine M n)
    (fun q => ∃ label, q=.ready label)
    (by intro d hd; obtain ⟨label,hl⟩ := hd; exact end_park_recursive_internal_ready_fixed M n d label hl) start T hReady
  refine ⟨t,by omega,?_,?_,hHeads,hCells,hStack,hStackHead⟩
  · change (machine M n request resume).step^[t] (liftResume M n request resume start)=_
    rw [end_park_recursive_internal_resume_iterate M n request resume start t (by
      intro s hs label heq
      exact hlive s hs ⟨label,heq⟩),he,hRun]
    rfl
  · change resumeControl M n resume (EndParkResume.finalFrame M n base rho sigma offset extent c label w).state=_
    rw [hState]
    rfl

end IntMul.EndParkRecursiveScheduler


open IntMul IntMul.EndParkRecursiveScheduler

theorem solution (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (EndParkResume.machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ p, extent M.outTape < p → c.cells M.outTape p=M.blank) :
    ∃ t, t≤ extent M.outTape+n+w.length+2*max w.length (extent M.outTape)+12 ∧
      (machine M n request resume).step^[t]
        (initialFrame M n request resume base rho sigma offset extent c label w)=
        finalFrame M n request resume base rho sigma offset extent c label w ∧
      (finalFrame M n request resume base rho sigma offset extent c label w).state=.body (resume label) ∧
      (∀ j, (finalFrame M n request resume base rho sigma offset extent c label w).head
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (BankedSimulation.workTape M j))=
        offset j+(if j=M.outTape then 0 else extent j+1)) ∧
      (∀ p, (finalFrame M n request resume base rho sigma offset extent c label w).cells
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (BankedSimulation.workTape M M.outTape))
        (offset M.outTape+p)=some (M.tapeOf (w.map M.bitSym) p,decide (p≤ w.length))) ∧
      (finalFrame M n request resume base rho sigma offset extent c label w).cells (FiniteContinuationStack.stackTape M)=
        FiniteContinuationStack.freshTape M (base.cells (FiniteContinuationStack.stackTape M)) rho ∧
      (finalFrame M n request resume base rho sigma offset extent c label w).head (FiniteContinuationStack.stackTape M)=rho :=
  IntMul.EndParkRecursiveScheduler.resume_correct M n request resume base rho sigma offset extent c label w unique tail

#print axioms solution
