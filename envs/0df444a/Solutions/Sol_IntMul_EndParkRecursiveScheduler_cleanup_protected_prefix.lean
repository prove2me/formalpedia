-- Prove2me | solution 1 for IntMul.EndParkRecursiveScheduler.cleanup_protected_prefix
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T06:47:25.379226+00:00
-- url     : https://prove2.me/submissions/b0b09522-466b-453a-951a-5d27e662a3ed

import Definitions.Def_IntMul_EndParkRecursiveExecution
import Theorems.Thm_IntMul_TrackedBankCleanup_cleanup_correct
import Theorems.Thm_IntMul_TrackedBankCleanup_cleanup_window_safe
import Theorems.Thm_IntMul_TrackedBankCleanup_cleanup_nonwork_fixed
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Mathlib.Tactic

namespace IntMul.EndParkRecursiveScheduler

private theorem cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem fixed_iterate (N : MultitapeTM) (c : N.Cfg) (fixed : N.step c=c) (T : ℕ) :
    N.step^[T] c=c := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,fixed]

private theorem halted_step (N : MultitapeTM) (c : N.Cfg) (halt : c.state=N.qHalt) : N.step c=c := by
  apply cfg_ext
  · simp [MultitapeTM.step,halt,N.halt_fixed]
  · funext i
    simp only [MultitapeTM.step,halt,N.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,N.halt_fixed]

/-- First entry to any family of quiescent service exits preserves the exact
complete supplied terminal configuration, including all tape heads. -/
private theorem first_exit (N : MultitapeTM) (P : N.K → Prop)
    (fixed : ∀ d : N.Cfg, P d.state → N.step d=d) (c : N.Cfg) (T : ℕ)
    (exit : P (N.step^[T] c).state) :
    ∃ t, t≤ T ∧ N.step^[t] c=N.step^[T] c ∧ ∀ s, s< t → ¬P (N.step^[s] c).state := by
  classical
  have hex : ∃ t, P (N.step^[t] c).state := ⟨T,exit⟩
  let t := Nat.find hex
  have ht : t≤ T := Nat.find_min' hex exit
  have hp : P (N.step^[t] c).state := Nat.find_spec hex
  refine ⟨t,ht,?_,?_⟩
  · rw [show T=(T-t)+t by omega,Function.iterate_add_apply,fixed_iterate N _ (fixed _ hp)]
  · intro s hs
    exact Nat.find_min hex hs

private theorem cleanup_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (live : c.state≠(cleanupMachine M).qHalt) :
    (machine M n request resume).step (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step c) := by
  have ht : transition M n request resume (.cleanup c.state) (fun i => c.cells i (c.head i))=
      (let r := (cleanupMachine M).δ c.state (fun i => c.cells i (c.head i)); (.cleanup r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply cfg_ext
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


end IntMul.EndParkRecursiveScheduler

namespace IntMul.EndParkRecursiveScheduler

private theorem padded_cleanup_heads (M : MultitapeTM)
    (padBase : (cleanupMachine M).Cfg) (callerBase : (TrackedBankCleanup.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (pos : Fin M.k → ℕ)
    (positive : ∀ j, 1 ≤ offset j)
    (bufferPositive : 1 ≤ callerBase.head (TrackedBankCleanup.machine M).outTape)
    (stackPositive : 1 ≤ padBase.head (FixedTapeExtension.extraTape (TrackedBankCleanup.machine M)))
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank)
    (t : ℕ) (i : Fin (M.k+3)) (noninput : i ≠ (cleanupMachine M).inTape) :
    1 ≤ ((cleanupMachine M).step^[t]
      (FixedTapeExtension.embed (TrackedBankCleanup.machine M) padBase
        (TrackedBankCleanup.rewindFrame M callerBase offset extent c pos))).head i := by
  rw [(FixedTapeExtension.simulate_run (TrackedBankCleanup.machine M) padBase
    (TrackedBankCleanup.rewindFrame M callerBase offset extent c pos) t).1]
  simp only [FixedTapeExtension.embed]
  have hzero : i.val ≠ 0 := by
    intro h
    exact noninput (Fin.ext h)
  by_cases hi : i.val < M.k+2
  · simp only [dif_pos hi]
    let j : Fin (M.k+2) := FixedTapeExtension.innerTape (TrackedBankCleanup.machine M) i hi
    change 1 ≤ ((TrackedBankCleanup.machine M).step^[t]
      (TrackedBankCleanup.rewindFrame M callerBase offset extent c pos)).head j
    by_cases hw : 2 ≤ j.val
    · let k := BankedSimulation.innerTape M j hw
      have hj : BankedSimulation.workTape M k=j := by
        apply Fin.ext
        dsimp only [k,BankedSimulation.innerTape,BankedSimulation.workTape]
        omega
      rw [←hj]
      exact le_trans (positive k)
        (TrackedBankCleanup.cleanup_window_safe M callerBase offset extent c pos unique tail t k)
    · have hj : j=(TrackedBankCleanup.machine M).outTape := by
        apply Fin.ext
        change j.val=1
        have hjv : j.val=i.val := rfl
        omega
      rw [hj,(TrackedBankCleanup.cleanup_nonwork_fixed M callerBase offset extent c pos
        t (TrackedBankCleanup.machine M).outTape (by change (1:ℕ)< 2; omega)).1]
      exact bufferPositive
  · simp only [dif_neg hi]
    have heq : i=FixedTapeExtension.extraTape (TrackedBankCleanup.machine M) := by
      apply Fin.ext
      change i.val=M.k+2
      have := i.isLt
      omega
    rw [heq]
    exact stackPositive

/-- The complete cleanup service runs inside the actual scheduler, reaches
its exact terminal frame in bounded time, and protects every noninput window
at every intermediate physical time, including the service exit. -/
private theorem cleanup_protected_prefix (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (padBase : (cleanupMachine M).Cfg) (callerBase : (TrackedBankCleanup.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (pos : Fin M.k → ℕ)
    (positive : ∀ j, 1 ≤ offset j)
    (bufferPositive : 1 ≤ callerBase.head (TrackedBankCleanup.machine M).outTape)
    (stackPositive : 1 ≤ padBase.head (FixedTapeExtension.extraTape (TrackedBankCleanup.machine M)))
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∃ t, t ≤ TrackedBankCleanup.span M pos+2*TrackedBankCleanup.span M extent+3 ∧
      (machine M n request resume).step^[t]
        (liftCleanup M n request resume (FixedTapeExtension.embed (TrackedBankCleanup.machine M)
          padBase (TrackedBankCleanup.rewindFrame M callerBase offset extent c pos)))=
        liftCleanup M n request resume (FixedTapeExtension.embed (TrackedBankCleanup.machine M)
          padBase (TrackedBankCleanup.finalFrame M callerBase offset)) ∧
      ∀ s, s ≤ t → ∀ i, i ≠ (machine M n request resume).inTape →
        1 ≤ ((machine M n request resume).step^[s]
          (liftCleanup M n request resume (FixedTapeExtension.embed (TrackedBankCleanup.machine M)
            padBase (TrackedBankCleanup.rewindFrame M callerBase offset extent c pos)))).head i := by
  let C := TrackedBankCleanup.span M pos+2*TrackedBankCleanup.span M extent+3
  let start := FixedTapeExtension.embed (TrackedBankCleanup.machine M) padBase
    (TrackedBankCleanup.rewindFrame M callerBase offset extent c pos)
  have hrun : (cleanupMachine M).step^[C] start=
      FixedTapeExtension.embed (TrackedBankCleanup.machine M) padBase
        (TrackedBankCleanup.finalFrame M callerBase offset) := by
    rw [(FixedTapeExtension.simulate_run (TrackedBankCleanup.machine M) padBase
      (TrackedBankCleanup.rewindFrame M callerBase offset extent c pos) C).1]
    rw [(TrackedBankCleanup.cleanup_correct M callerBase offset extent positive c pos unique tail).1]
  have halt : ((cleanupMachine M).step^[C] start).state=(cleanupMachine M).qHalt := by
    rw [hrun]
    rfl
  obtain ⟨t,ht,heq,live⟩ := first_exit (cleanupMachine M)
    (fun q => q=(cleanupMachine M).qHalt) (by intro d hd; exact halted_step _ d hd) start C halt
  refine ⟨t,ht,?_,?_⟩
  · rw [cleanup_iterate M n request resume start t live,heq,hrun]
  · intro s hs i hi
    rw [cleanup_iterate M n request resume start s (by intro r hr; exact live r (by omega))]
    exact padded_cleanup_heads M padBase callerBase offset extent c pos positive bufferPositive
      stackPositive unique tail s i hi

end IntMul.EndParkRecursiveScheduler


open IntMul IntMul.EndParkRecursiveScheduler

theorem solution (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (padBase : (cleanupMachine M).Cfg) (callerBase : (TrackedBankCleanup.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (pos : Fin M.k → ℕ)
    (positive : ∀ j, 1 ≤ offset j)
    (bufferPositive : 1 ≤ callerBase.head (TrackedBankCleanup.machine M).outTape)
    (stackPositive : 1 ≤ padBase.head (FixedTapeExtension.extraTape (TrackedBankCleanup.machine M)))
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∃ t, t ≤ TrackedBankCleanup.span M pos+2*TrackedBankCleanup.span M extent+3 ∧
      (machine M n request resume).step^[t]
        (liftCleanup M n request resume (FixedTapeExtension.embed (TrackedBankCleanup.machine M)
          padBase (TrackedBankCleanup.rewindFrame M callerBase offset extent c pos)))=
        liftCleanup M n request resume (FixedTapeExtension.embed (TrackedBankCleanup.machine M)
          padBase (TrackedBankCleanup.finalFrame M callerBase offset)) ∧
      ∀ s, s ≤ t → ∀ i, i ≠ (machine M n request resume).inTape →
        1 ≤ ((machine M n request resume).step^[s]
          (liftCleanup M n request resume (FixedTapeExtension.embed (TrackedBankCleanup.machine M)
            padBase (TrackedBankCleanup.rewindFrame M callerBase offset extent c pos)))).head i :=
  IntMul.EndParkRecursiveScheduler.cleanup_protected_prefix M n request resume padBase callerBase offset extent c pos positive bufferPositive stackPositive unique tail

#print axioms solution
