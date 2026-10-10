-- Prove2me | solution 1 for IntMul.TrackedMarshalledCall.call_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T01:23:32.960154+00:00
-- url     : https://prove2.me/submissions/73b053cc-61e6-4604-942f-36a487790694

import Definitions.Def_IntMul_TrackedMarshalledCall
import Theorems.Thm_IntMul_TrackedChildInputBridge_input_correct
import Theorems.Thm_IntMul_TrackedParentOutputBridge_output_correct
import Theorems.Thm_IntMul_SavedContinuationCall_call_correct
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Mathlib.Tactic


namespace IntMul.TrackedMarshalledCall

private theorem program_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem program_fixed_iterate (N : MultitapeTM) (c : N.Cfg) (fixed : N.step c=c) (T : ℕ) :
    N.step^[T] c=c := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,fixed]

private theorem program_halted_step (N : MultitapeTM) (c : N.Cfg) (halt : c.state=N.qHalt) : N.step c=c := by
  apply program_cfg_ext
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
  · rw [show T=(T-t)+t by omega,Function.iterate_add_apply,program_fixed_iterate N _ (fixed _ hp)]
  · intro s hs
    exact Nat.find_min hex hs

private theorem resumeLabel_some_iff (M : MultitapeTM) (n : ℕ) (s : SavedContinuationCall.State M n) (q : Fin n) :
    resumeLabel M n s=some q ↔ s=.inr (.inr (.resume q)) := by
  cases s with
  | inl s => simp [resumeLabel]
  | inr s =>
    cases s with
    | inl s => simp [resumeLabel]
    | inr s => cases s <;> simp [resumeLabel]

private theorem saved_resume_fixed (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (c : (SavedContinuationCall.machine M n initial).Cfg) (q : Fin n)
    (exit : resumeLabel M n c.state=some q) : (SavedContinuationCall.machine M n initial).step c=c := by
  have hs := (resumeLabel_some_iff M n c.state q).mp exit
  have ht : ∀ a, SavedContinuationCall.transition M n (.inr (.inr (.resume q))) a =
      (.inr (.inr (.resume q)),fun i => (a i,.stay)) := by
    intro a
    simp only [SavedContinuationCall.transition,FiniteContinuationStack.transition,FiniteContinuationStack.rawTransition]
    congr 1
    funext i
    cases a i <;> rfl
  apply program_cfg_ext
  · simp only [MultitapeTM.step,hs,ht]
  · funext i
    simp only [MultitapeTM.step,hs,ht]
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,hs,ht]

noncomputable def startSaved (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (c : (inputMachine M).Cfg) : (SavedContinuationCall.machine M n initial).Cfg where
  state := .inl (.pushStart q)
  cells := c.cells
  head := c.head

noncomputable def startOutput (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (c : (SavedContinuationCall.machine M n initial).Cfg) : (outputMachine M).Cfg where
  state := (outputMachine M).qStart
  cells := c.cells
  head := c.head

private theorem lift_input_step (M : MultitapeTM) (n : ℕ) (initial q : Fin n) (c : (inputMachine M).Cfg)
    (live : c.state≠(inputMachine M).qHalt) :
    (machine M n initial).step (liftInput M n initial q c)=liftInput M n initial q ((inputMachine M).step c) := by
  classical
  apply program_cfg_ext <;> simp [MultitapeTM.step,liftInput,transition,live]

private theorem lift_saved_step (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (c : (SavedContinuationCall.machine M n initial).Cfg) (live : resumeLabel M n c.state=none) :
    (machine M n initial).step (liftSaved M n initial c)=
      liftSaved M n initial ((SavedContinuationCall.machine M n initial).step c) := by
  apply program_cfg_ext <;> simp [MultitapeTM.step,liftSaved,transition,live]

private theorem lift_output_step (M : MultitapeTM) (n : ℕ) (initial q : Fin n) (c : (outputMachine M).Cfg)
    (live : c.state≠(outputMachine M).qHalt) :
    (machine M n initial).step (liftOutput M n initial q c)=liftOutput M n initial q ((outputMachine M).step c) := by
  classical
  apply program_cfg_ext <;> simp [MultitapeTM.step,liftOutput,transition,live]

private theorem lift_input_iterate (M : MultitapeTM) (n : ℕ) (initial q : Fin n) (c : (inputMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s< T → ((inputMachine M).step^[s] c).state≠(inputMachine M).qHalt) :
    (machine M n initial).step^[T] (liftInput M n initial q c)=liftInput M n initial q ((inputMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      lift_input_step M n initial q _ (live T (by omega)),Function.iterate_succ_apply']

private theorem lift_saved_iterate (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (c : (SavedContinuationCall.machine M n initial).Cfg) (T : ℕ)
    (live : ∀ s, s< T → resumeLabel M n ((SavedContinuationCall.machine M n initial).step^[s] c).state=none) :
    (machine M n initial).step^[T] (liftSaved M n initial c)=
      liftSaved M n initial ((SavedContinuationCall.machine M n initial).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      lift_saved_step M n initial _ (live T (by omega)),Function.iterate_succ_apply']

private theorem lift_output_iterate (M : MultitapeTM) (n : ℕ) (initial q : Fin n) (c : (outputMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s< T → ((outputMachine M).step^[s] c).state≠(outputMachine M).qHalt) :
    (machine M n initial).step^[T] (liftOutput M n initial q c)=liftOutput M n initial q ((outputMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      lift_output_step M n initial q _ (live T (by omega)),Function.iterate_succ_apply']

private theorem input_dispatch (M : MultitapeTM) (n : ℕ) (initial q : Fin n) (c : (inputMachine M).Cfg)
    (halt : c.state=(inputMachine M).qHalt) :
    (machine M n initial).step (liftInput M n initial q c)=liftSaved M n initial (startSaved M n initial q c) := by
  classical
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftInput,liftSaved,startSaved,transition,halt]
  · funext i
    simp only [MultitapeTM.step,liftInput,liftSaved,startSaved,transition,if_pos halt]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,liftInput,liftSaved,startSaved,transition,halt]

private theorem saved_dispatch (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (c : (SavedContinuationCall.machine M n initial).Cfg) (exit : resumeLabel M n c.state=some q) :
    (machine M n initial).step (liftSaved M n initial c)=liftOutput M n initial q (startOutput M n initial c) := by
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftSaved,liftOutput,startOutput,transition,exit]
  · funext i
    simp only [MultitapeTM.step,liftSaved,liftOutput,startOutput,transition,exit]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,liftSaved,liftOutput,startOutput,transition,exit]

private theorem output_dispatch (M : MultitapeTM) (n : ℕ) (initial q : Fin n) (c : (outputMachine M).Cfg)
    (halt : c.state=(outputMachine M).qHalt) :
    (machine M n initial).step (liftOutput M n initial q c)=resumeFrame M n initial q c := by
  classical
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftOutput,resumeFrame,transition,halt]
  · funext i
    simp only [MultitapeTM.step,liftOutput,resumeFrame,transition,if_pos halt]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,liftOutput,resumeFrame,transition,halt]

private theorem run_input_to_saved (M : MultitapeTM) (n : ℕ) (initial q : Fin n) (c : (inputMachine M).Cfg) (T : ℕ)
    (halt : ((inputMachine M).step^[T] c).state=(inputMachine M).qHalt) :
    ∃ t, t≤ T+1 ∧ (machine M n initial).step^[t] (liftInput M n initial q c)=
      liftSaved M n initial (startSaved M n initial q ((inputMachine M).step^[T] c)) := by
  obtain ⟨t,ht,he,hn⟩ := first_exit (inputMachine M) (fun s => s=(inputMachine M).qHalt)
    (fun d h => program_halted_step _ d h) c T halt
  refine ⟨t+1,by omega,?_⟩
  rw [Function.iterate_succ_apply',lift_input_iterate M n initial q c t hn,he,input_dispatch M n initial q _ halt]

private theorem run_saved_to_output (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (c : (SavedContinuationCall.machine M n initial).Cfg) (T : ℕ)
    (exit : resumeLabel M n ((SavedContinuationCall.machine M n initial).step^[T] c).state=some q) :
    ∃ t, t≤ T+1 ∧ (machine M n initial).step^[t] (liftSaved M n initial c)=
      liftOutput M n initial q (startOutput M n initial ((SavedContinuationCall.machine M n initial).step^[T] c)) := by
  obtain ⟨t,ht,he,hn⟩ := first_exit (SavedContinuationCall.machine M n initial)
    (fun s => ∃ q, resumeLabel M n s=some q)
    (by intro d h; rcases h with ⟨q,h⟩; exact saved_resume_fixed M n initial d q h) c T ⟨q,exit⟩
  have hl : ∀ s, s< t → resumeLabel M n ((SavedContinuationCall.machine M n initial).step^[s] c).state=none := by
    intro s hs
    cases h : resumeLabel M n ((SavedContinuationCall.machine M n initial).step^[s] c).state with
    | none => rfl
    | some q => exact False.elim (hn s hs ⟨q,h⟩)
  refine ⟨t+1,by omega,?_⟩
  rw [Function.iterate_succ_apply',lift_saved_iterate M n initial c t hl,he,saved_dispatch M n initial q _ exit]

private theorem run_output_to_resume (M : MultitapeTM) (n : ℕ) (initial q : Fin n) (c : (outputMachine M).Cfg) (T : ℕ)
    (halt : ((outputMachine M).step^[T] c).state=(outputMachine M).qHalt) :
    ∃ t, t≤ T+1 ∧ (machine M n initial).step^[t] (liftOutput M n initial q c)=
      resumeFrame M n initial q ((outputMachine M).step^[T] c) := by
  obtain ⟨t,ht,he,hn⟩ := first_exit (outputMachine M) (fun s => s=(outputMachine M).qHalt)
    (fun d h => program_halted_step _ d h) c T halt
  refine ⟨t+1,by omega,?_⟩
  rw [Function.iterate_succ_apply',lift_output_iterate M n initial q c t hn,he,output_dispatch M n initial q _ halt]

end IntMul.TrackedMarshalledCall



namespace IntMul.TrackedMarshalledCall

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

private theorem call_parent_cells (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) (j : Fin M.k) (p : ℕ) :
    (callParent M n initial base sigma offset extent c v x y).cells (workTape M j) (offset j+p)=
      some ((parentAfterInput M c).cells j p,decide (p≤ extent j)) := by
  change (TrackedChildInputBridge.finalFrame M (inputParent M n initial base) sigma offset extent c v x y).cells
    (workTape M j) (offset j+p)=_
  simp only [TrackedChildInputBridge.finalFrame,if_neg (work_ne_buffer M j),TrackedChildInputBridge.initialCells,
    parentAfterInput]
  exact embed_work M _ offset extent c j p

private theorem call_parent_heads (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) (j : Fin M.k) :
    (callParent M n initial base sigma offset extent c v x y).head (workTape M j)=
      offset j+(parentAfterInput M c).head j := by
  change (TrackedChildInputBridge.finalFrame M (inputParent M n initial base) sigma offset extent c v x y).head
    (workTape M j)=_
  simp only [TrackedChildInputBridge.finalFrame,if_neg (work_ne_buffer M j),parentAfterInput,
]
  by_cases hj : j=M.outTape
  · subst j
    simp only [TrackedChildInputBridge.packetTape,eq_self,if_true,Nat.add_zero]
  · have hn : workTape M j≠TrackedChildInputBridge.packetTape M := by intro h; exact hj (work_injective M h)
    rw [if_neg hn]
    simp only [if_neg hj,TrackedChildInputBridge.initialHeads]
    exact embed_work_head M _ offset extent c j

private theorem parent_after_near (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ)
    (near : ∀ j, c.head j≤ extent j+1) : ∀ j, (parentAfterInput M c).head j≤ extent j+1 := by
  intro j
  simp only [parentAfterInput]
  split
  · omega
  · exact near j

noncomputable def trackedParentView (M : MultitapeTM) (parent : (TrackedReentrantCall.machine M).Cfg) :
    (TrackedBankedSimulation.machine M).Cfg where
  state := M.qStart
  cells := parent.cells
  head := parent.head

private theorem reentrant_initial_cells (M : MultitapeTM) (parent : (TrackedReentrantCall.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (canonical : ∀ j p, parent.cells (workTape M j) (offset j+p)=some (c.cells j p,decide (p≤ extent j))) :
    (TrackedReentrantCall.initialFrame M parent offset extent c).cells=parent.cells := by
  change (TrackedBankedSimulation.embed M (trackedParentView M parent) offset extent c).cells=parent.cells
  exact embed_cells_ready M (trackedParentView M parent) offset extent c canonical

private theorem reentrant_initial_heads (M : MultitapeTM) (parent : (TrackedReentrantCall.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (heads : ∀ j, parent.head (workTape M j)=offset j+c.head j) :
    (TrackedReentrantCall.initialFrame M parent offset extent c).head=parent.head := by
  change (fun i => if h : 2 ≤ i.val then
    offset (innerTape M i h)+c.head (innerTape M i h)+min 0 (TrackedBankReservation.distance M extent c.head (innerTape M i h))
      else parent.head i)=parent.head
  simp only [Nat.zero_min,Nat.add_zero]
  exact embed_heads_ready M (trackedParentView M parent) offset extent c heads

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

private theorem fresh_stack_idempotent (M : MultitapeTM) (base : ℕ → Sym M) (rho : ℕ) :
    FiniteContinuationStack.freshTape M (FiniteContinuationStack.freshTape M base rho) rho=
      FiniteContinuationStack.freshTape M base rho := by
  funext p
  by_cases hp : p< rho
  · simp [FiniteContinuationStack.freshTape,hp]
  · simp [FiniteContinuationStack.freshTape,hp]

end IntMul.TrackedMarshalledCall



namespace IntMul.TrackedMarshalledCall

open IntMul.TrackedBankedSimulation (Sym)

private theorem input_frame_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem input_finish_old_cells (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) (j : Fin (M.k+2)) :
    (inputFinish M n initial base rho sigma offset extent c v x y).cells
      (FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) j)=
        (callParent M n initial base sigma offset extent c v x y).cells j := by
  exact extension_old_cells (TrackedChildInputBridge.machine M) _ _ j

private theorem input_finish_old_heads (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) (j : Fin (M.k+2)) :
    (inputFinish M n initial base rho sigma offset extent c v x y).head
      (FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) j)=
        (callParent M n initial base sigma offset extent c v x y).head j := by
  exact extension_old_heads (TrackedChildInputBridge.machine M) _ _ j

private theorem input_finish_stack_cells (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) :
    (inputFinish M n initial base rho sigma offset extent c v x y).cells (FiniteContinuationStack.stackTape M)=
      FiniteContinuationStack.freshTape M (base.cells (FiniteContinuationStack.stackTape M)) rho := by
  have he : FiniteContinuationStack.stackTape M=FixedTapeExtension.extraTape (TrackedChildInputBridge.machine M) := by
    apply Fin.ext
    rfl
  simp only [inputFinish,he,extension_extra_cells,freshInputBase]
  have he' : FixedTapeExtension.extraTape (TrackedChildInputBridge.machine M)=FiniteContinuationStack.stackTape M := he.symm
  rw [he']
  simp only [eq_self,if_true]

private theorem input_finish_stack_head (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) :
    (inputFinish M n initial base rho sigma offset extent c v x y).head (FiniteContinuationStack.stackTape M)=rho := by
  have he : FiniteContinuationStack.stackTape M=FixedTapeExtension.extraTape (TrackedChildInputBridge.machine M) := by
    apply Fin.ext
    rfl
  simp only [inputFinish,he,extension_extra_heads,freshInputBase]
  rw [he.symm]
  simp only [eq_self,if_true]

private theorem call_parent_reentrant_cells (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) :
    (TrackedReentrantCall.initialFrame M (callParent M n initial base sigma offset extent c v x y)
      offset extent (parentAfterInput M c)).cells=(callParent M n initial base sigma offset extent c v x y).cells := by
  exact reentrant_initial_cells M _ offset extent _ (call_parent_cells M n initial base sigma offset extent c v x y)

private theorem call_parent_reentrant_heads (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) :
    (TrackedReentrantCall.initialFrame M (callParent M n initial base sigma offset extent c v x y)
      offset extent (parentAfterInput M c)).head=(callParent M n initial base sigma offset extent c v x y).head := by
  exact reentrant_initial_heads M _ offset extent _ (call_parent_heads M n initial base sigma offset extent c v x y)

end IntMul.TrackedMarshalledCall



namespace IntMul.TrackedMarshalledCall

private theorem input_ready_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem saved_start_cells (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) :
    (savedStart M n initial q base rho sigma offset extent c v x y).cells=
      (inputFinish M n initial base rho sigma offset extent c v x y).cells := by
  funext i
  by_cases hi : i.val < M.k+2
  · let j : Fin (M.k+2) := ⟨i.val,hi⟩
    have hs : i≠FiniteContinuationStack.stackTape M := by
      intro h
      have h := congrArg Fin.val h
      simp only [FiniteContinuationStack.stackTape] at h
      omega
    simp only [savedStart,SavedContinuationCall.callInitialFrame,SavedContinuationCall.initialFrame,
      SavedContinuationCall.liftPush,FiniteContinuationStack.pushStartFrame,if_neg hs,SavedContinuationCall.stackBase]
    have he1 : i=FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) j := by apply Fin.ext; rfl
    rw [he1,extension_old_cells,call_parent_reentrant_cells]
    have he2 : FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) j=
        FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) j := by apply Fin.ext; rfl
    rw [he2]
    exact (input_finish_old_cells M n initial base rho sigma offset extent c v x y j).symm
  · have hs : i=FiniteContinuationStack.stackTape M := by
      apply Fin.ext
      have hi' := i.isLt
      change i.val=M.k+2
      change i.val < M.k+3 at hi'
      omega
    rw [hs]
    simp only [savedStart,SavedContinuationCall.callInitialFrame,SavedContinuationCall.initialFrame,
      SavedContinuationCall.liftPush,FiniteContinuationStack.pushStartFrame,eq_self,if_true,SavedContinuationCall.stackBase]
    have he : FiniteContinuationStack.stackTape M=FixedTapeExtension.extraTape (TrackedReentrantCall.machine M) := by
      apply Fin.ext
      rfl
    rw [he,extension_extra_cells]
    simp only [SavedContinuationCall.childBase]
    rw [←he]
    simp only [callBase]
    rw [input_finish_stack_cells,fresh_stack_idempotent]

private theorem saved_start_heads (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) :
    (savedStart M n initial q base rho sigma offset extent c v x y).head=
      (inputFinish M n initial base rho sigma offset extent c v x y).head := by
  funext i
  by_cases hi : i.val < M.k+2
  · let j : Fin (M.k+2) := ⟨i.val,hi⟩
    have hs : i≠FiniteContinuationStack.stackTape M := by
      intro h
      have h := congrArg Fin.val h
      simp only [FiniteContinuationStack.stackTape] at h
      omega
    simp only [savedStart,SavedContinuationCall.callInitialFrame,SavedContinuationCall.initialFrame,
      SavedContinuationCall.liftPush,FiniteContinuationStack.pushStartFrame,if_neg hs,SavedContinuationCall.stackBase]
    have he1 : i=FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) j := by apply Fin.ext; rfl
    rw [he1,extension_old_heads,call_parent_reentrant_heads]
    have he2 : FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) j=
        FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) j := by apply Fin.ext; rfl
    rw [he2]
    exact (input_finish_old_heads M n initial base rho sigma offset extent c v x y j).symm
  · have hs : i=FiniteContinuationStack.stackTape M := by
      apply Fin.ext
      have hi' := i.isLt
      change i.val=M.k+2
      change i.val < M.k+3 at hi'
      omega
    rw [hs]
    simp only [savedStart,SavedContinuationCall.callInitialFrame,SavedContinuationCall.initialFrame,
      SavedContinuationCall.liftPush,FiniteContinuationStack.pushStartFrame,eq_self,if_true]
    exact (input_finish_stack_head M n initial base rho sigma offset extent c v x y).symm

/-- The actual charged input dispatch changes only finite control. Its entire
configuration already equals the saved child's starting frame. -/
private theorem input_ready (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) :
    startSaved M n initial q (inputFinish M n initial base rho sigma offset extent c v x y)=
      savedStart M n initial q base rho sigma offset extent c v x y := by
  apply input_ready_cfg_ext
  · rfl
  · exact (saved_start_cells M n initial q base rho sigma offset extent c v x y).symm
  · exact (saved_start_heads M n initial q base rho sigma offset extent c v x y).symm

private theorem call_parent_source (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) :
    (callParent M n initial base sigma offset extent c v x y).cells (TrackedChildInputBridge.bufferTape M)=
      TrackedBankPreparation.sourceTape M
        ((callParent M n initial base sigma offset extent c v x y).cells (TrackedChildInputBridge.bufferTape M))
        sigma (TrackedBankPreparation.inputWord M x y) := by
  simp only [callParent,TrackedChildInputBridge.finalFrame,eq_self,if_true]
  funext p
  by_cases hp : p< sigma
  · simp [TrackedBankPreparation.sourceTape,hp]
  · by_cases hm : p=sigma
    · simp [TrackedBankPreparation.sourceTape,hm]
    · simp [TrackedBankPreparation.sourceTape,hp,hm]

private theorem call_parent_source_head (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) :
    (callParent M n initial base sigma offset extent c v x y).head (TrackedChildInputBridge.bufferTape M)=sigma := by
  simp only [callParent,TrackedChildInputBridge.finalFrame,eq_self,if_true]

end IntMul.TrackedMarshalledCall



namespace IntMul.TrackedMarshalledCall

open IntMul.BankedSimulation (workTape)

private theorem returned_buffer_idempotent (M : MultitapeTM) (base : ℕ → TrackedBankedSimulation.Sym M)
    (sigma : ℕ) (w : List Bool) :
    TrackedOutputReturn.bufferTape M (TrackedOutputReturn.bufferTape M base sigma w) sigma w=
      TrackedOutputReturn.bufferTape M base sigma w := by
  funext p
  by_cases hp : p< sigma
  · simp [TrackedOutputReturn.bufferTape,hp]
  · by_cases hm : p=sigma
    · simp [TrackedOutputReturn.bufferTape,hm]
    · simp [TrackedOutputReturn.bufferTape,hp,hm]

private theorem output_parent_base_cells (M : MultitapeTM) (parent : (TrackedParentOutputBridge.machine M).Cfg)
    (sigma : ℕ) (w : List Bool)
    (buffer : parent.cells (TrackedParentOutputBridge.bufferTape M)=
      TrackedOutputReturn.bufferTape M (parent.cells (TrackedParentOutputBridge.bufferTape M)) sigma w) :
    (TrackedParentOutputBridge.parentBase M parent sigma w).cells=parent.cells := by
  funext i
  simp only [TrackedParentOutputBridge.parentBase]
  by_cases hi : i=TrackedParentOutputBridge.bufferTape M
  · subst i
    simp only [eq_self,if_true]
    exact buffer.symm
  · simp only [if_neg hi]

private theorem output_parent_base_heads (M : MultitapeTM) (parent : (TrackedParentOutputBridge.machine M).Cfg)
    (sigma : ℕ) (w : List Bool)
    (buffer : parent.head (TrackedParentOutputBridge.bufferTape M)=sigma+w.length+1) :
    (TrackedParentOutputBridge.parentBase M parent sigma w).head=parent.head := by
  funext i
  simp only [TrackedParentOutputBridge.parentBase]
  by_cases hi : i=TrackedParentOutputBridge.bufferTape M
  · subst i
    simp only [eq_self,if_true]
    exact buffer.symm
  · simp only [if_neg hi]

private theorem output_initial_cells (M : MultitapeTM) (parent : (TrackedParentOutputBridge.machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (canonical : ∀ j p, parent.cells (workTape M j) (offset j+p)=some (c.cells j p,decide (p≤ extent j)))
    (buffer : parent.cells (TrackedParentOutputBridge.bufferTape M)=
      TrackedOutputReturn.bufferTape M (parent.cells (TrackedParentOutputBridge.bufferTape M)) sigma w) :
    (TrackedParentOutputBridge.initialFrame M parent sigma offset extent (parentZero M c) w).cells=parent.cells := by
  change (TrackedBankedSimulation.embed M (TrackedParentOutputBridge.parentBase M parent sigma w)
    offset extent (parentZero M c)).cells=parent.cells
  have hb := output_parent_base_cells M parent sigma w buffer
  have hc : ∀ j p, (TrackedParentOutputBridge.parentBase M parent sigma w).cells (workTape M j) (offset j+p)=
      some ((parentZero M c).cells j p,decide (p≤ extent j)) := by
    rw [hb]
    exact canonical
  rw [embed_cells_ready M _ offset extent _ hc,hb]

private theorem output_initial_heads (M : MultitapeTM) (parent : (TrackedParentOutputBridge.machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (heads : ∀ j, parent.head (workTape M j)=offset j)
    (buffer : parent.head (TrackedParentOutputBridge.bufferTape M)=sigma+w.length+1) :
    (TrackedParentOutputBridge.initialFrame M parent sigma offset extent (parentZero M c) w).head=parent.head := by
  have hb := output_parent_base_heads M parent sigma w buffer
  have hh : ∀ j, (TrackedParentOutputBridge.parentBase M parent sigma w).head (workTape M j)=
      offset j+(parentZero M c).head j := by
    rw [hb]
    intro j
    simpa only [parentZero,Nat.add_zero] using heads j
  have he := embed_heads_ready M (TrackedParentOutputBridge.parentBase M parent sigma w) offset extent (parentZero M c) hh
  funext i
  simp only [TrackedParentOutputBridge.initialFrame,TrackedParentOutputBridge.beforeFrame,Nat.sub_zero,
    TrackedParentOutputBridge.initialHeads,he,hb]
  by_cases hi : i=TrackedParentOutputBridge.bufferTape M
  · subst i
    simp only [eq_self,if_true]
    simpa only [Nat.add_assoc] using buffer.symm
  · rw [if_neg hi]
    by_cases ht : i=TrackedParentOutputBridge.targetTape M
    · subst i
      simp only [eq_self,if_true]
      exact (heads M.outTape).symm
    · simp only [if_neg ht]

end IntMul.TrackedMarshalledCall



namespace IntMul.TrackedMarshalledCall

open IntMul.BankedSimulation (workTape)

private theorem output_ready_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem extension_cells_ready (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg)
    (old : ∀ j, c.cells j=base.cells (FixedTapeExtension.oldTape N j)) :
    (FixedTapeExtension.embed N base c).cells=base.cells := by
  funext i
  change (if h : i.val < N.k then c.cells (FixedTapeExtension.innerTape N i h) else base.cells i)=base.cells i
  by_cases hi : i.val < N.k
  · rw [dif_pos hi,old]
    have h : FixedTapeExtension.oldTape N (FixedTapeExtension.innerTape N i hi)=i := by apply Fin.ext; rfl
    rw [h]
  · simp only [dif_neg hi]

private theorem extension_heads_ready (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg)
    (old : ∀ j, c.head j=base.head (FixedTapeExtension.oldTape N j)) :
    (FixedTapeExtension.embed N base c).head=base.head := by
  funext i
  change (if h : i.val < N.k then c.head (FixedTapeExtension.innerTape N i h) else base.head i)=base.head i
  by_cases hi : i.val < N.k
  · rw [dif_pos hi,old]
    have h : FixedTapeExtension.oldTape N (FixedTapeExtension.innerTape N i hi)=i := by apply Fin.ext; rfl
    rw [h]
  · simp only [dif_neg hi]

private theorem output_ready (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) (T : ℕ) (w : List Bool)
    (canonical : ∀ j p,
      (outputParent M n initial q base rho sigma offset extent c v x y T w).cells (workTape M j) (offset j+p)=
        some (c.cells j p,decide (p≤ extent j)))
    (heads : ∀ j, (outputParent M n initial q base rho sigma offset extent c v x y T w).head (workTape M j)=offset j)
    (buffer : (outputParent M n initial q base rho sigma offset extent c v x y T w).cells (TrackedParentOutputBridge.bufferTape M)=
      TrackedOutputReturn.bufferTape M
        ((outputParent M n initial q base rho sigma offset extent c v x y T w).cells (TrackedParentOutputBridge.bufferTape M)) sigma w)
    (buffer_head : (outputParent M n initial q base rho sigma offset extent c v x y T w).head (TrackedParentOutputBridge.bufferTape M)=
      sigma+w.length+1) :
    startOutput M n initial (savedFinish M n initial q base rho sigma offset extent c v x y T w)=
      outputStart M n initial q base rho sigma offset extent c v x y T w := by
  have hc := output_initial_cells M (outputParent M n initial q base rho sigma offset extent c v x y T w)
    sigma offset extent c w canonical buffer
  have hh := output_initial_heads M (outputParent M n initial q base rho sigma offset extent c v x y T w)
    sigma offset extent c w heads buffer_head
  apply output_ready_cfg_ext
  · rfl
  · have ho : ∀ j,
        (TrackedParentOutputBridge.initialFrame M (outputParent M n initial q base rho sigma offset extent c v x y T w)
          sigma offset extent (parentZero M c) w).cells j=
        (outputBase M n initial q base rho sigma offset extent c v x y T w).cells
          (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) j) := by
      intro j
      rw [hc]
      rfl
    exact (extension_cells_ready (TrackedParentOutputBridge.machine M) _ _ ho).symm
  · have ho : ∀ j,
        (TrackedParentOutputBridge.initialFrame M (outputParent M n initial q base rho sigma offset extent c v x y T w)
          sigma offset extent (parentZero M c) w).head j=
        (outputBase M n initial q base rho sigma offset extent c v x y T w).head
          (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) j) := by
      intro j
      rw [hh]
      rfl
    exact (extension_heads_ready (TrackedParentOutputBridge.machine M) _ _ ho).symm

private theorem output_ready_from_saved (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) (T : ℕ) (w : List Bool)
    (banks : ∀ j, (savedFinish M n initial q base rho sigma offset extent c v x y T w).cells
      (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) (workTape M j))=
      (TrackedReentrantCall.initialFrame M (callParent M n initial base sigma offset extent c v x y)
        offset extent (parentAfterInput M c)).cells (workTape M j))
    (heads : ∀ j, (savedFinish M n initial q base rho sigma offset extent c v x y T w).head
      (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) (workTape M j))=offset j)
    (buffer : (savedFinish M n initial q base rho sigma offset extent c v x y T w).cells
      (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) (TrackedChildInputBridge.bufferTape M))=
      TrackedOutputReturn.bufferTape M
        ((callParent M n initial base sigma offset extent c v x y).cells (TrackedChildInputBridge.bufferTape M)) sigma w)
    (buffer_head : (savedFinish M n initial q base rho sigma offset extent c v x y T w).head
      (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) (TrackedChildInputBridge.bufferTape M))=sigma+w.length+1) :
    startOutput M n initial (savedFinish M n initial q base rho sigma offset extent c v x y T w)=
      outputStart M n initial q base rho sigma offset extent c v x y T w := by
  apply output_ready
  · intro j p
    change (savedFinish M n initial q base rho sigma offset extent c v x y T w).cells
      (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) (workTape M j)) (offset j+p)=_
    rw [banks j,call_parent_reentrant_cells]
    exact call_parent_cells M n initial base sigma offset extent c v x y j p
  · intro j
    exact heads j
  · change (savedFinish M n initial q base rho sigma offset extent c v x y T w).cells
        (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) (TrackedChildInputBridge.bufferTape M))=
      TrackedOutputReturn.bufferTape M
        ((savedFinish M n initial q base rho sigma offset extent c v x y T w).cells
          (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) (TrackedChildInputBridge.bufferTape M))) sigma w
    rw [buffer]
    exact (returned_buffer_idempotent M _ sigma w).symm
  · exact buffer_head

end IntMul.TrackedMarshalledCall



namespace IntMul.TrackedMarshalledCall

open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

private theorem recovered_saved (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool)
    (near : ∀ j, c.head j ≤ extent j+1)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (T : ℕ) (halt : (M.step^[T] (M.initCfg x y)).state=M.qHalt)
    (w : List Bool) (out : (M.step^[T] (M.initCfg x y)).cells M.outTape=M.tapeOf (w.map M.bitSym)) :
    ∃ s, s ≤ T+5*span M (extents M (M.initCfg x y) (initialExtent M x y) T)+
        2*(inputWord M x y).length+2*span M extent+2*n+24 ∧
      (SavedContinuationCall.machine M n initial).step^[s]
        (savedStart M n initial q base rho sigma offset extent c v x y)=
          savedFinish M n initial q base rho sigma offset extent c v x y T w ∧
      (savedFinish M n initial q base rho sigma offset extent c v x y T w).state=.inr (.inr (.resume q)) ∧
      (savedFinish M n initial q base rho sigma offset extent c v x y T w).cells (FiniteContinuationStack.stackTape M)=
        FiniteContinuationStack.freshTape M
          ((callBase M n initial q base rho sigma offset extent c v x y).cells (FiniteContinuationStack.stackTape M)) rho ∧
      (savedFinish M n initial q base rho sigma offset extent c v x y T w).head (FiniteContinuationStack.stackTape M)=rho ∧
      (∀ j, (savedFinish M n initial q base rho sigma offset extent c v x y T w).cells
        (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) (BankedSimulation.workTape M j))=
        (TrackedReentrantCall.initialFrame M (callParent M n initial base sigma offset extent c v x y)
          offset extent (parentAfterInput M c)).cells (BankedSimulation.workTape M j)) ∧
      (∀ j, (savedFinish M n initial q base rho sigma offset extent c v x y T w).head
        (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) (BankedSimulation.workTape M j))=offset j) ∧
      (savedFinish M n initial q base rho sigma offset extent c v x y T w).cells
        (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) (TrackedChildInputBridge.bufferTape M))=
        TrackedOutputReturn.bufferTape M
          ((callParent M n initial base sigma offset extent c v x y).cells (TrackedChildInputBridge.bufferTape M)) sigma w ∧
      (savedFinish M n initial q base rho sigma offset extent c v x y T w).head
        (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) (TrackedChildInputBridge.bufferTape M))=sigma+w.length+1 := by
  obtain ⟨s,hs,he,hstate,hstack,hstackhead,hbanks,hheads,hbuffer,hbufferhead⟩ :=
    SavedContinuationCall.call_correct M n initial (callBase M n initial q base rho sigma offset extent c v x y)
      rho q (callParent M n initial base sigma offset extent c v x y) sigma offset extent (parentAfterInput M c)
      (parent_after_near M c extent near) tail unique x y
      (call_parent_source M n initial base sigma offset extent c v x y)
      (call_parent_source_head M n initial base sigma offset extent c v x y) T halt w out
  rw [he] at hstate hstack hstackhead hbanks hheads hbuffer hbufferhead
  exact ⟨s,hs,he,hstate,hstack,hstackhead,hbanks,hheads,hbuffer,hbufferhead⟩

end IntMul.TrackedMarshalledCall



namespace IntMul.TrackedMarshalledCall

open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

private theorem run_correct (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool)
    (near : ∀ j, c.head j ≤ extent j+1)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (packet : c.cells M.outTape=M.tapeOf (inputWord M x y))
    (T : ℕ) (halt : (M.step^[T] (M.initCfg x y)).state=M.qHalt)
    (w : List Bool) (out : (M.step^[T] (M.initCfg x y)).cells M.outTape=M.tapeOf (w.map M.bitSym)) :
    ∃ t, t ≤ T+5*span M (extents M (M.initCfg x y) (initialExtent M x y) T)+
        2*(inputWord M x y).length+2*span M extent+2*n+
        max (c.head M.outTape) (v.length+1)+2*max (inputWord M x y).length v.length+
        w.length+2*max w.length (extent M.outTape)+36 ∧
      (machine M n initial).step^[t] (initialFrame M n initial q base rho sigma offset extent c v)=
        finalFrame M n initial q base rho sigma offset extent c v x y T w := by
  let I := max (c.head M.outTape) (v.length+1)+2*max (inputWord M x y).length v.length+4
  have hOldInput := (TrackedChildInputBridge.input_correct M (inputParent M n initial base) sigma offset extent c v x y packet).1
  change (TrackedChildInputBridge.machine M).step^[I]
    (TrackedChildInputBridge.initialFrame M (inputParent M n initial base) sigma offset extent c v)=
      TrackedChildInputBridge.finalFrame M (inputParent M n initial base) sigma offset extent c v x y at hOldInput
  have hInput := (FixedTapeExtension.simulate_run (TrackedChildInputBridge.machine M)
    (freshInputBase M n initial base rho)
    (TrackedChildInputBridge.initialFrame M (inputParent M n initial base) sigma offset extent c v) I).1
  rw [hOldInput] at hInput
  change (inputMachine M).step^[I] (inputStart M n initial base rho sigma offset extent c v)=
    inputFinish M n initial base rho sigma offset extent c v x y at hInput
  have hInputHalt : ((inputMachine M).step^[I] (inputStart M n initial base rho sigma offset extent c v)).state=
      (inputMachine M).qHalt := by rw [hInput]; rfl
  obtain ⟨i,hi,hiRun⟩ := run_input_to_saved M n initial q
    (inputStart M n initial base rho sigma offset extent c v) I hInputHalt
  rw [hInput,input_ready] at hiRun
  change (machine M n initial).step^[i] (initialFrame M n initial q base rho sigma offset extent c v)=
    liftSaved M n initial (savedStart M n initial q base rho sigma offset extent c v x y) at hiRun
  obtain ⟨s,hs,hsRun,hstate,hstack,hstackhead,hbanks,hheads,hbuffer,hbufferhead⟩ :=
    recovered_saved M n initial q base rho sigma offset extent c v x y near tail unique T halt w out
  have hExit : resumeLabel M n
      ((SavedContinuationCall.machine M n initial).step^[s] (savedStart M n initial q base rho sigma offset extent c v x y)).state=
        some q := by rw [hsRun,hstate]; rfl
  obtain ⟨sCall,hsCall,hsCallRun⟩ := run_saved_to_output M n initial q
    (savedStart M n initial q base rho sigma offset extent c v x y) s hExit
  rw [hsRun,output_ready_from_saved M n initial q base rho sigma offset extent c v x y T w
    hbanks hheads hbuffer hbufferhead] at hsCallRun
  let O := w.length+2*max w.length (extent M.outTape)+5
  have hOldOutput := (TrackedParentOutputBridge.output_correct M
    (outputParent M n initial q base rho sigma offset extent c v x y T w) sigma offset extent (parentZero M c) w
    ((unique M.outTape 0).mpr rfl) (tail M.outTape)).1
  change (TrackedParentOutputBridge.machine M).step^[O]
    (TrackedParentOutputBridge.initialFrame M (outputParent M n initial q base rho sigma offset extent c v x y T w)
      sigma offset extent (parentZero M c) w)=
      TrackedParentOutputBridge.finalFrame M (outputParent M n initial q base rho sigma offset extent c v x y T w)
        sigma offset extent (parentZero M c) w at hOldOutput
  have hOutput := (FixedTapeExtension.simulate_run (TrackedParentOutputBridge.machine M)
    (outputBase M n initial q base rho sigma offset extent c v x y T w)
    (TrackedParentOutputBridge.initialFrame M (outputParent M n initial q base rho sigma offset extent c v x y T w)
      sigma offset extent (parentZero M c) w) O).1
  rw [hOldOutput] at hOutput
  change (outputMachine M).step^[O] (outputStart M n initial q base rho sigma offset extent c v x y T w)=
    outputFinish M n initial q base rho sigma offset extent c v x y T w at hOutput
  have hOutputHalt : ((outputMachine M).step^[O] (outputStart M n initial q base rho sigma offset extent c v x y T w)).state=
      (outputMachine M).qHalt := by rw [hOutput]; rfl
  obtain ⟨o,ho,hoRun⟩ := run_output_to_resume M n initial q
    (outputStart M n initial q base rho sigma offset extent c v x y T w) O hOutputHalt
  rw [hOutput] at hoRun
  change (machine M n initial).step^[o] (liftOutput M n initial q (outputStart M n initial q base rho sigma offset extent c v x y T w))=
    finalFrame M n initial q base rho sigma offset extent c v x y T w at hoRun
  have hsi : (machine M n initial).step^[sCall+i] (initialFrame M n initial q base rho sigma offset extent c v)=
      liftOutput M n initial q (outputStart M n initial q base rho sigma offset extent c v x y T w) := by
    rw [Function.iterate_add_apply,hiRun,hsCallRun]
  refine ⟨o+(sCall+i),?_,?_⟩
  · dsimp only [I,O] at hi ho
    omega
  · rw [Function.iterate_add_apply,hsi,hoRun]

end IntMul.TrackedMarshalledCall



namespace IntMul.TrackedMarshalledCall

open IntMul.BankedSimulation (workTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem initial_old_cells (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v : List Bool) (j : Fin (M.k+2)) :
    (initialFrame M n initial q base rho sigma offset extent c v).cells
      (FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) j)=
      (TrackedChildInputBridge.initialFrame M (inputParent M n initial base) sigma offset extent c v).cells j := by
  exact extension_old_cells (TrackedChildInputBridge.machine M) _ _ j

private theorem final_old_cells (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) (T : ℕ) (w : List Bool) (j : Fin (M.k+2)) :
    (finalFrame M n initial q base rho sigma offset extent c v x y T w).cells
      (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) j)=
      (TrackedParentOutputBridge.finalFrame M
        (outputParent M n initial q base rho sigma offset extent c v x y T w)
        sigma offset extent (parentZero M c) w).cells j := by
  exact extension_old_cells (TrackedParentOutputBridge.machine M) _ _ j

private theorem final_old_heads (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) (T : ℕ) (w : List Bool) (j : Fin (M.k+2)) :
    (finalFrame M n initial q base rho sigma offset extent c v x y T w).head
      (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) j)=
      (TrackedParentOutputBridge.finalFrame M
        (outputParent M n initial q base rho sigma offset extent c v x y T w)
        sigma offset extent (parentZero M c) w).head j := by
  exact extension_old_heads (TrackedParentOutputBridge.machine M) _ _ j

private theorem final_stack_cells (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) (T : ℕ) (w : List Bool) :
    (finalFrame M n initial q base rho sigma offset extent c v x y T w).cells (FiniteContinuationStack.stackTape M)=
      (savedFinish M n initial q base rho sigma offset extent c v x y T w).cells (FiniteContinuationStack.stackTape M) := by
  have he : FiniteContinuationStack.stackTape M=FixedTapeExtension.extraTape (TrackedParentOutputBridge.machine M) := by
    apply Fin.ext
    rfl
  change (outputFinish M n initial q base rho sigma offset extent c v x y T w).cells _=_
  simp only [outputFinish,he,extension_extra_cells,outputBase]

private theorem final_stack_head (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) (T : ℕ) (w : List Bool) :
    (finalFrame M n initial q base rho sigma offset extent c v x y T w).head (FiniteContinuationStack.stackTape M)=
      (savedFinish M n initial q base rho sigma offset extent c v x y T w).head (FiniteContinuationStack.stackTape M) := by
  have he : FiniteContinuationStack.stackTape M=FixedTapeExtension.extraTape (TrackedParentOutputBridge.machine M) := by
    apply Fin.ext
    rfl
  change (outputFinish M n initial q base rho sigma offset extent c v x y T w).head _=_
  simp only [outputFinish,he,extension_extra_heads,outputBase]

private theorem return_over_source (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ)
    (packet : List M.Sym) (w : List Bool) :
    TrackedOutputReturn.bufferTape M (TrackedBankPreparation.sourceTape M base sigma packet) sigma w=
      TrackedOutputReturn.bufferTape M base sigma w := by
  funext p
  by_cases hp : p < sigma
  · simp [TrackedOutputReturn.bufferTape,TrackedBankPreparation.sourceTape,hp]
  · by_cases hm : p=sigma
    · simp [TrackedOutputReturn.bufferTape,hm]
    · simp [TrackedOutputReturn.bufferTape,hp,hm]

end IntMul.TrackedMarshalledCall



namespace IntMul.TrackedMarshalledCall

open IntMul.BankedSimulation (workTape)
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

/-- One actual physically marshalled saved child call, including every dispatch,
the restored continuation stack, all retained parent banks and physically
placed return word. The caller never assumes a pre-copied child-input buffer. -/
private theorem call_correct (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool)
    (near : ∀ j, c.head j ≤ extent j+1)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (packet : c.cells M.outTape=M.tapeOf (inputWord M x y))
    (T : ℕ) (halt : (M.step^[T] (M.initCfg x y)).state=M.qHalt)
    (w : List Bool) (out : (M.step^[T] (M.initCfg x y)).cells M.outTape=M.tapeOf (w.map M.bitSym)) :
    ∃ t, t ≤ T+5*span M (extents M (M.initCfg x y) (initialExtent M x y) T)+
        2*(inputWord M x y).length+2*span M extent+2*n+
        max (c.head M.outTape) (v.length+1)+2*max (inputWord M x y).length v.length+
        w.length+2*max w.length (extent M.outTape)+36 ∧
      (machine M n initial).step^[t] (initialFrame M n initial q base rho sigma offset extent c v)=
        finalFrame M n initial q base rho sigma offset extent c v x y T w ∧
      (finalFrame M n initial q base rho sigma offset extent c v x y T w).state=.inr (.inr (.inr (.inl q))) ∧
      (finalFrame M n initial q base rho sigma offset extent c v x y T w).cells (FiniteContinuationStack.stackTape M)=
        FiniteContinuationStack.freshTape M (base.cells (FiniteContinuationStack.stackTape M)) rho ∧
      (finalFrame M n initial q base rho sigma offset extent c v x y T w).head (FiniteContinuationStack.stackTape M)=rho ∧
      (finalFrame M n initial q base rho sigma offset extent c v x y T w).cells
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M M.outTape))=
        TrackedBankPreparation.bankTape M
          ((initialFrame M n initial q base rho sigma offset extent c v).cells
            (FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) (workTape M M.outTape)))
          (offset M.outTape) (w.map M.bitSym) ∧
      (∀ p, (finalFrame M n initial q base rho sigma offset extent c v x y T w).cells
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M M.outTape)) (offset M.outTape+p)=
          some (M.tapeOf (w.map M.bitSym) p,decide (p ≤ w.length))) ∧
      (∀ j, (finalFrame M n initial q base rho sigma offset extent c v x y T w).head
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M j))=offset j) ∧
      (finalFrame M n initial q base rho sigma offset extent c v x y T w).cells
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (TrackedChildInputBridge.bufferTape M))=
        TrackedOutputReturn.bufferTape M
          (base.cells (FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) (TrackedChildInputBridge.bufferTape M))) sigma w ∧
      (finalFrame M n initial q base rho sigma offset extent c v x y T w).head
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (TrackedChildInputBridge.bufferTape M))=sigma+w.length+1 ∧
      (∀ j, j ≠ M.outTape → (finalFrame M n initial q base rho sigma offset extent c v x y T w).cells
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M j))=
        (initialFrame M n initial q base rho sigma offset extent c v).cells
          (FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) (workTape M j))) := by
  obtain ⟨t,ht,hRun⟩ := run_correct M n initial q base rho sigma offset extent c v x y
    near tail unique packet T halt w out
  obtain ⟨s,hs,hsRun,hstate,hstack,hstackhead,hbanks,hheads,hbuffer,hbufferhead⟩ :=
    recovered_saved M n initial q base rho sigma offset extent c v x y near tail unique T halt w out
  have hReady := output_ready_from_saved M n initial q base rho sigma offset extent c v x y T w
    hbanks hheads hbuffer hbufferhead
  have hReadyCells := congrArg (fun z => z.cells) hReady
  have hReadyHeads := congrArg (fun z => z.head) hReady
  change (savedFinish M n initial q base rho sigma offset extent c v x y T w).cells=
    (outputStart M n initial q base rho sigma offset extent c v x y T w).cells at hReadyCells
  change (savedFinish M n initial q base rho sigma offset extent c v x y T w).head=
    (outputStart M n initial q base rho sigma offset extent c v x y T w).head at hReadyHeads
  have hIcells (j : Fin (M.k+2)) :
      (TrackedParentOutputBridge.initialFrame M (outputParent M n initial q base rho sigma offset extent c v x y T w)
        sigma offset extent (parentZero M c) w).cells j=
        (outputParent M n initial q base rho sigma offset extent c v x y T w).cells j := by
    have h := congrFun hReadyCells (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) j)
    simp only [outputStart,extension_old_cells] at h
    exact h.symm
  have hIheads (j : Fin (M.k+2)) :
      (TrackedParentOutputBridge.initialFrame M (outputParent M n initial q base rho sigma offset extent c v x y T w)
        sigma offset extent (parentZero M c) w).head j=
        (outputParent M n initial q base rho sigma offset extent c v x y T w).head j := by
    have h := congrFun hReadyHeads (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) j)
    simp only [outputStart,extension_old_heads] at h
    exact h.symm
  have hInput := TrackedChildInputBridge.input_correct M (inputParent M n initial base) sigma offset extent c v x y packet
  have hParent (j : Fin M.k) :
      (outputParent M n initial q base rho sigma offset extent c v x y T w).cells (workTape M j)=
        (initialFrame M n initial q base rho sigma offset extent c v).cells
          (FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) (workTape M j)) := by
    change (savedFinish M n initial q base rho sigma offset extent c v x y T w).cells
      (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) (workTape M j))=_
    rw [hbanks j,call_parent_reentrant_cells,initial_old_cells]
    exact hInput.2.2.2.2.2.1 j
  rcases TrackedParentOutputBridge.output_correct M
    (outputParent M n initial q base rho sigma offset extent c v x y T w) sigma offset extent (parentZero M c) w
    ((unique M.outTape 0).mpr rfl) (tail M.outTape) with
    ⟨hORun,hOHalt,hTarget,hRelative,hTargetHead,hBuf,hBufHead,hOther,hOtherHead⟩
  simp only [TrackedParentOutputBridge.targetTape] at hTarget hRelative hTargetHead hOther hOtherHead
  change (TrackedParentOutputBridge.finalFrame M
    (outputParent M n initial q base rho sigma offset extent c v x y T w)
    sigma offset extent (parentZero M c) w).cells (TrackedChildInputBridge.bufferTape M)=
      TrackedOutputReturn.bufferTape M
        ((outputParent M n initial q base rho sigma offset extent c v x y T w).cells
          (TrackedChildInputBridge.bufferTape M)) sigma w at hBuf
  refine ⟨t,ht,hRun,rfl,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [final_stack_cells,hstack]
    change FiniteContinuationStack.freshTape M
      ((inputFinish M n initial base rho sigma offset extent c v x y).cells (FiniteContinuationStack.stackTape M)) rho=_
    rw [input_finish_stack_cells,fresh_stack_idempotent]
  · rw [final_stack_head,hstackhead]
  · rw [final_old_cells,hTarget,hParent M.outTape]
  · intro p
    rw [final_old_cells]
    exact hRelative p
  · intro j
    rw [final_old_heads]
    by_cases hj : j=M.outTape
    · subst j
      exact hTargetHead
    · have hn : workTape M j ≠ TrackedParentOutputBridge.targetTape M := by
        intro h
        exact hj (work_injective M h)
      rw [hOtherHead _ hn,hIheads]
      exact hheads j
  · rw [final_old_cells,hBuf]
    change TrackedOutputReturn.bufferTape M
      ((savedFinish M n initial q base rho sigma offset extent c v x y T w).cells
        (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) (TrackedChildInputBridge.bufferTape M))) sigma w=_
    rw [hbuffer,returned_buffer_idempotent]
    change TrackedOutputReturn.bufferTape M
      (TrackedBankPreparation.sourceTape M
        ((inputParent M n initial base).cells (TrackedChildInputBridge.bufferTape M)) sigma (inputWord M x y)) sigma w=_
    rw [return_over_source]
    rfl
  · rw [final_old_heads]
    exact hBufHead
  · intro j hj
    rw [final_old_cells]
    have hn : workTape M j ≠ TrackedParentOutputBridge.targetTape M := by
      intro h
      exact hj (work_injective M h)
    rw [hOther _ hn,hIcells,hParent]

end IntMul.TrackedMarshalledCall


open IntMul IntMul.TrackedMarshalledCall
open IntMul.BankedSimulation (workTape)
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

theorem solution (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool)
    (near : ∀ j, c.head j ≤ extent j+1)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (packet : c.cells M.outTape=M.tapeOf (inputWord M x y))
    (T : ℕ) (halt : (M.step^[T] (M.initCfg x y)).state=M.qHalt)
    (w : List Bool) (out : (M.step^[T] (M.initCfg x y)).cells M.outTape=M.tapeOf (w.map M.bitSym)) :
    ∃ t, t ≤ T+5*span M (extents M (M.initCfg x y) (initialExtent M x y) T)+
        2*(inputWord M x y).length+2*span M extent+2*n+
        max (c.head M.outTape) (v.length+1)+2*max (inputWord M x y).length v.length+
        w.length+2*max w.length (extent M.outTape)+36 ∧
      (machine M n initial).step^[t] (initialFrame M n initial q base rho sigma offset extent c v)=
        finalFrame M n initial q base rho sigma offset extent c v x y T w ∧
      (finalFrame M n initial q base rho sigma offset extent c v x y T w).state=.inr (.inr (.inr (.inl q))) ∧
      (finalFrame M n initial q base rho sigma offset extent c v x y T w).cells (FiniteContinuationStack.stackTape M)=
        FiniteContinuationStack.freshTape M (base.cells (FiniteContinuationStack.stackTape M)) rho ∧
      (finalFrame M n initial q base rho sigma offset extent c v x y T w).head (FiniteContinuationStack.stackTape M)=rho ∧
      (finalFrame M n initial q base rho sigma offset extent c v x y T w).cells
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M M.outTape))=
        TrackedBankPreparation.bankTape M
          ((initialFrame M n initial q base rho sigma offset extent c v).cells
            (FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) (workTape M M.outTape)))
          (offset M.outTape) (w.map M.bitSym) ∧
      (∀ p, (finalFrame M n initial q base rho sigma offset extent c v x y T w).cells
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M M.outTape)) (offset M.outTape+p)=
          some (M.tapeOf (w.map M.bitSym) p,decide (p ≤ w.length))) ∧
      (∀ j, (finalFrame M n initial q base rho sigma offset extent c v x y T w).head
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M j))=offset j) ∧
      (finalFrame M n initial q base rho sigma offset extent c v x y T w).cells
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (TrackedChildInputBridge.bufferTape M))=
        TrackedOutputReturn.bufferTape M
          (base.cells (FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) (TrackedChildInputBridge.bufferTape M))) sigma w ∧
      (finalFrame M n initial q base rho sigma offset extent c v x y T w).head
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (TrackedChildInputBridge.bufferTape M))=sigma+w.length+1 ∧
      (∀ j, j ≠ M.outTape → (finalFrame M n initial q base rho sigma offset extent c v x y T w).cells
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M j))=
        (initialFrame M n initial q base rho sigma offset extent c v).cells
          (FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) (workTape M j))) :=
  IntMul.TrackedMarshalledCall.call_correct M n initial q base rho sigma offset extent c v x y
    near tail unique packet T halt w out

#print axioms solution
