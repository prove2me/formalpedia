-- Prove2me | solution 1 for IntMul.FlatRecursiveResume.resume_parent_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T03:04:34.761195+00:00
-- url     : https://prove2.me/submissions/89def995-83c9-44dd-b295-56b30249a472

import Definitions.Def_IntMul_FlatRecursiveResume
import Theorems.Thm_IntMul_TrackedParentRestore_restore_correct
import Theorems.Thm_IntMul_TrackedParentOutputBridge_output_correct
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Mathlib.Data.List.GetD
import Mathlib.Tactic


namespace IntMul.FlatRecursiveScheduler

private theorem resume_internal_flatrecursiveschedulerpadding_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem resume_internal_extension_old_cells (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) (j : Fin N.k) :
    (FixedTapeExtension.embed N base c).cells (FixedTapeExtension.oldTape N j)=c.cells j := by
  simp only [FixedTapeExtension.embed,FixedTapeExtension.oldTape,dif_pos j.isLt]
  have h : FixedTapeExtension.innerTape N ⟨j.val,by have := j.isLt; omega⟩ j.isLt=j := by apply Fin.ext; rfl
  rw [h]

private theorem resume_internal_extension_old_heads (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) (j : Fin N.k) :
    (FixedTapeExtension.embed N base c).head (FixedTapeExtension.oldTape N j)=c.head j := by
  simp only [FixedTapeExtension.embed,FixedTapeExtension.oldTape,dif_pos j.isLt]
  have h : FixedTapeExtension.innerTape N ⟨j.val,by have := j.isLt; omega⟩ j.isLt=j := by apply Fin.ext; rfl
  rw [h]

private theorem resume_internal_extension_extra_cells (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) :
    (FixedTapeExtension.embed N base c).cells (FixedTapeExtension.extraTape N)=base.cells (FixedTapeExtension.extraTape N) := by
  simp [FixedTapeExtension.embed,FixedTapeExtension.extraTape]

private theorem resume_internal_extension_extra_heads (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) :
    (FixedTapeExtension.embed N base c).head (FixedTapeExtension.extraTape N)=base.head (FixedTapeExtension.extraTape N) := by
  simp [FixedTapeExtension.embed,FixedTapeExtension.extraTape]

private theorem resume_internal_extension_cells_ready (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg)
    (old : ∀ j, base.cells (FixedTapeExtension.oldTape N j)=c.cells j) :
    (FixedTapeExtension.embed N base c).cells=base.cells := by
  funext i
  by_cases hi : i.val < N.k
  · simp only [FixedTapeExtension.embed,dif_pos hi]
    have h := old (FixedTapeExtension.innerTape N i hi)
    have he : FixedTapeExtension.oldTape N (FixedTapeExtension.innerTape N i hi)=i := by apply Fin.ext; rfl
    rw [he] at h
    exact h.symm
  · simp only [FixedTapeExtension.embed,dif_neg hi]

private theorem resume_internal_extension_heads_ready (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg)
    (old : ∀ j, base.head (FixedTapeExtension.oldTape N j)=c.head j) :
    (FixedTapeExtension.embed N base c).head=base.head := by
  funext i
  by_cases hi : i.val < N.k
  · simp only [FixedTapeExtension.embed,dif_pos hi]
    have h := old (FixedTapeExtension.innerTape N i hi)
    have he : FixedTapeExtension.oldTape N (FixedTapeExtension.innerTape N i hi)=i := by apply Fin.ext; rfl
    rw [he] at h
    exact h.symm
  · simp only [FixedTapeExtension.embed,dif_neg hi]

private theorem resume_internal_padded_init (N : MultitapeTM) (x y : List Bool) :
    (FixedTapeExtension.machine N).initCfg x y =
      FixedTapeExtension.embed N ((FixedTapeExtension.machine N).initCfg x y) (N.initCfg x y) := by
  apply resume_internal_flatrecursiveschedulerpadding_cfg_ext
  · rfl
  · apply (resume_internal_extension_cells_ready N _ _ ?_).symm
    intro j
    have hzero : FixedTapeExtension.oldTape N j=(FixedTapeExtension.machine N).inTape ↔ j=N.inTape := by
      constructor
      · intro h; apply Fin.ext
        have hv := congrArg (fun i : Fin (N.k+1) => i.val) h
        exact hv
      · intro h; subst j; rfl
    simp only [MultitapeTM.initCfg,hzero]
    split <;> rfl
  · apply (resume_internal_extension_heads_ready N _ _ ?_).symm
    intro j
    rfl

end IntMul.FlatRecursiveScheduler



namespace IntMul.FlatRecursiveScheduler

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem resume_internal_work_inner (M : MultitapeTM) (i : Fin (M.k+2)) (h : 2≤ i.val) :
    workTape M (innerTape M i h)=i := by
  apply Fin.ext
  simp only [workTape,innerTape]
  omega

private theorem resume_internal_work_injective (M : MultitapeTM) : Function.Injective (workTape M) := by
  intro i j h
  apply Fin.ext
  have h := congrArg Fin.val h
  simp only [workTape] at h
  omega

private theorem resume_internal_work_ne_buffer (M : MultitapeTM) (j : Fin M.k) :
    workTape M j≠TrackedChildInputBridge.bufferTape M := by
  intro h
  have h := congrArg Fin.val h
  simp only [workTape,TrackedChildInputBridge.bufferTape] at h
  omega

private theorem resume_internal_embed_work (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) (p : ℕ) :
    (TrackedBankedSimulation.embed M base offset extent c).cells (workTape M j) (offset j+p)=
      some (c.cells j p,decide (p≤ extent j)) := by
  simp only [TrackedBankedSimulation.embed,workTape]
  rw [dif_pos (by omega)]
  have hi : innerTape M ⟨j.val+2,by omega⟩ (by change 2≤ j.val+2; omega)=j := by
    apply Fin.ext
    simp [innerTape]
  simp only [hi,if_neg (by omega : ¬offset j+p< offset j),show offset j+p-offset j=p by omega]

private theorem resume_internal_embed_work_head (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) :
    (TrackedBankedSimulation.embed M base offset extent c).head (workTape M j)=offset j+c.head j := by
  simp only [TrackedBankedSimulation.embed,workTape]
  rw [dif_pos (by omega)]
  have hi : innerTape M ⟨j.val+2,by omega⟩ (by change 2≤ j.val+2; omega)=j := by
    apply Fin.ext
    simp [innerTape]
  rw [hi]

private theorem resume_internal_embed_cells_ready (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
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
      have hw : workTape M j=i := resume_internal_work_inner M i hi
      rw [hw,show offset j+(p-offset j)=p by omega] at h
      exact h.symm
  · simp only [dif_neg hi]

private theorem resume_internal_embed_heads_ready (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (heads : ∀ j, base.head (workTape M j)=offset j+c.head j) :
    (TrackedBankedSimulation.embed M base offset extent c).head=base.head := by
  funext i
  dsimp only [TrackedBankedSimulation.embed]
  by_cases hi : 2≤ i.val
  · rw [dif_pos hi]
    have h := heads (innerTape M i hi)
    rw [resume_internal_work_inner M i hi] at h
    exact h.symm
  · simp only [dif_neg hi]


end IntMul.FlatRecursiveScheduler



namespace IntMul.FlatRecursiveScheduler

private theorem resume_internal_flatrecursiveschedulerprograms_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem resume_internal_flatrecursiveschedulerprograms_fixed_iterate (N : MultitapeTM) (c : N.Cfg) (fixed : N.step c=c) (T : ℕ) :
    N.step^[T] c=c := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,fixed]

private theorem resume_internal_flatrecursiveschedulerprograms_halted_step (N : MultitapeTM) (c : N.Cfg) (halt : c.state=N.qHalt) : N.step c=c := by
  apply resume_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp [MultitapeTM.step,halt,N.halt_fixed]
  · funext i
    simp only [MultitapeTM.step,halt,N.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,N.halt_fixed]

/-- First entry to any family of quiescent service exits preserves the exact
complete supplied terminal configuration, including all tape heads. -/
private theorem resume_internal_flatrecursiveschedulerprograms_first_exit (N : MultitapeTM) (P : N.K → Prop)
    (fixed : ∀ d : N.Cfg, P d.state → N.step d=d) (c : N.Cfg) (T : ℕ)
    (exit : P (N.step^[T] c).state) :
    ∃ t, t≤ T ∧ N.step^[t] c=N.step^[T] c ∧ ∀ s, s< t → ¬P (N.step^[s] c).state := by
  classical
  have hex : ∃ t, P (N.step^[t] c).state := ⟨T,exit⟩
  let t := Nat.find hex
  have ht : t≤ T := Nat.find_min' hex exit
  have hp : P (N.step^[t] c).state := Nat.find_spec hex
  refine ⟨t,ht,?_,?_⟩
  · rw [show T=(T-t)+t by omega,Function.iterate_add_apply,resume_internal_flatrecursiveschedulerprograms_fixed_iterate N _ (fixed _ hp)]
  · intro s hs
    exact Nat.find_min hex hs

private theorem resume_internal_boot_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (live : c.state≠(bootMachine M).qHalt) :
    (machine M n request resume).step (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step c) := by
  have ht : transition M n request resume (.boot c.state) (fun i => c.cells i (c.head i))=
      (let r := (bootMachine M).δ c.state (fun i => c.cells i (c.head i)); (.boot r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply resume_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftBoot,ht]
  · simp only [MultitapeTM.step,liftBoot,ht]
  · simp only [MultitapeTM.step,liftBoot,ht]

private theorem resume_internal_boot_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((bootMachine M).step^[s] c).state≠(bootMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      resume_internal_boot_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem resume_internal_boot_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (T : ℕ)
    (exit : ((bootMachine M).step^[T] c).state=(bootMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := resume_internal_flatrecursiveschedulerprograms_first_exit (bootMachine M)
    (fun q => q=(bootMachine M).qHalt) (by intro d hd; exact resume_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [resume_internal_boot_iterate M n request resume c s hlive,he]

private theorem resume_internal_preparation_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (live : c.state≠(preparationMachine M).qHalt) :
    (machine M n request resume).step (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step c) := by
  have ht : transition M n request resume (.preparation c.state) (fun i => c.cells i (c.head i))=
      (let r := (preparationMachine M).δ c.state (fun i => c.cells i (c.head i)); (.preparation r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply resume_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftPreparation,ht]
  · simp only [MultitapeTM.step,liftPreparation,ht]
  · simp only [MultitapeTM.step,liftPreparation,ht]

private theorem resume_internal_preparation_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((preparationMachine M).step^[s] c).state≠(preparationMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      resume_internal_preparation_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem resume_internal_preparation_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (T : ℕ)
    (exit : ((preparationMachine M).step^[T] c).state=(preparationMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := resume_internal_flatrecursiveschedulerprograms_first_exit (preparationMachine M)
    (fun q => q=(preparationMachine M).qHalt) (by intro d hd; exact resume_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [resume_internal_preparation_iterate M n request resume c s hlive,he]

private theorem resume_internal_body_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (live : c.state≠(bodyMachine M).qHalt)
    (no_request : request c.state=none) :
    (machine M n request resume).step (liftBody M n request resume c)=
      liftBody M n request resume ((bodyMachine M).step c) := by
  have ht : transition M n request resume (.body c.state) (fun i => c.cells i (c.head i))=
      (let r := (bodyMachine M).δ c.state (fun i => c.cells i (c.head i)); (.body r.1,r.2)) := by
    simp only [transition,if_neg live,no_request]
  apply resume_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftBody,ht]
  · simp only [MultitapeTM.step,liftBody,ht]
  · simp only [MultitapeTM.step,liftBody,ht]

private theorem resume_internal_body_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((bodyMachine M).step^[s] c).state≠(bodyMachine M).qHalt)
    (no_request : ∀ s, s < T → request (((bodyMachine M).step^[s] c).state)=none) :
    (machine M n request resume).step^[T] (liftBody M n request resume c)=
      liftBody M n request resume ((bodyMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)) (by intro s hs; exact no_request s (by omega)),
      resume_internal_body_step M n request resume _ (live T (by omega)) (no_request T (by omega)),Function.iterate_succ_apply']

private theorem resume_internal_body_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (T : ℕ)
    (exit : ((bodyMachine M).step^[T] c).state=(bodyMachine M).qHalt)
    (no_request : ∀ s, s < T → request (((bodyMachine M).step^[s] c).state)=none) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftBody M n request resume c)=
      liftBody M n request resume ((bodyMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := resume_internal_flatrecursiveschedulerprograms_first_exit (bodyMachine M)
    (fun q => q=(bodyMachine M).qHalt) (by intro d hd; exact resume_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [resume_internal_body_iterate M n request resume c s hlive (by intro r hr; exact no_request r (by omega)),he]

private theorem resume_internal_input_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (live : c.state≠(inputMachine M).qHalt) :
    (machine M n request resume).step (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step c) := by
  have ht : transition M n request resume (.input label c.state) (fun i => c.cells i (c.head i))=
      (let r := (inputMachine M).δ c.state (fun i => c.cells i (c.head i)); (.input label r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply resume_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftInput,ht]
  · simp only [MultitapeTM.step,liftInput,ht]
  · simp only [MultitapeTM.step,liftInput,ht]

private theorem resume_internal_input_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((inputMachine M).step^[s] c).state≠(inputMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      resume_internal_input_step M n request resume label _ (live T (by omega)),Function.iterate_succ_apply']

private theorem resume_internal_input_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (T : ℕ)
    (exit : ((inputMachine M).step^[T] c).state=(inputMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := resume_internal_flatrecursiveschedulerprograms_first_exit (inputMachine M)
    (fun q => q=(inputMachine M).qHalt) (by intro d hd; exact resume_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [resume_internal_input_iterate M n request resume label c s hlive,he]

private theorem resume_internal_reservation_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (live : c.state≠(reservationMachine M).qHalt) :
    (machine M n request resume).step (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step c) := by
  have ht : transition M n request resume (.reservation c.state) (fun i => c.cells i (c.head i))=
      (let r := (reservationMachine M).δ c.state (fun i => c.cells i (c.head i)); (.reservation r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply resume_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftReservation,ht]
  · simp only [MultitapeTM.step,liftReservation,ht]
  · simp only [MultitapeTM.step,liftReservation,ht]

private theorem resume_internal_reservation_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((reservationMachine M).step^[s] c).state≠(reservationMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      resume_internal_reservation_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem resume_internal_reservation_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (T : ℕ)
    (exit : ((reservationMachine M).step^[T] c).state=(reservationMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := resume_internal_flatrecursiveschedulerprograms_first_exit (reservationMachine M)
    (fun q => q=(reservationMachine M).qHalt) (by intro d hd; exact resume_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [resume_internal_reservation_iterate M n request resume c s hlive,he]

private theorem resume_internal_return_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (live : c.state≠(returnMachine M).qHalt) :
    (machine M n request resume).step (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step c) := by
  have ht : transition M n request resume (.returning c.state) (fun i => c.cells i (c.head i))=
      (let r := (returnMachine M).δ c.state (fun i => c.cells i (c.head i)); (.returning r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply resume_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftReturn,ht]
  · simp only [MultitapeTM.step,liftReturn,ht]
  · simp only [MultitapeTM.step,liftReturn,ht]

private theorem resume_internal_return_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((returnMachine M).step^[s] c).state≠(returnMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      resume_internal_return_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem resume_internal_return_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (T : ℕ)
    (exit : ((returnMachine M).step^[T] c).state=(returnMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := resume_internal_flatrecursiveschedulerprograms_first_exit (returnMachine M)
    (fun q => q=(returnMachine M).qHalt) (by intro d hd; exact resume_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [resume_internal_return_iterate M n request resume c s hlive,he]

private theorem resume_internal_cleanup_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (live : c.state≠(cleanupMachine M).qHalt) :
    (machine M n request resume).step (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step c) := by
  have ht : transition M n request resume (.cleanup c.state) (fun i => c.cells i (c.head i))=
      (let r := (cleanupMachine M).δ c.state (fun i => c.cells i (c.head i)); (.cleanup r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply resume_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftCleanup,ht]
  · simp only [MultitapeTM.step,liftCleanup,ht]
  · simp only [MultitapeTM.step,liftCleanup,ht]

private theorem resume_internal_cleanup_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((cleanupMachine M).step^[s] c).state≠(cleanupMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      resume_internal_cleanup_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem resume_internal_cleanup_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (T : ℕ)
    (exit : ((cleanupMachine M).step^[T] c).state=(cleanupMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := resume_internal_flatrecursiveschedulerprograms_first_exit (cleanupMachine M)
    (fun q => q=(cleanupMachine M).qHalt) (by intro d hd; exact resume_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [resume_internal_cleanup_iterate M n request resume c s hlive,he]

private theorem resume_internal_restore_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (restoreMachine M).Cfg) (live : c.state≠(restoreMachine M).qHalt) :
    (machine M n request resume).step (liftRestore M n request resume c)=
      liftRestore M n request resume ((restoreMachine M).step c) := by
  have ht : transition M n request resume (.restore c.state) (fun i => c.cells i (c.head i))=
      (let r := (restoreMachine M).δ c.state (fun i => c.cells i (c.head i)); (.restore r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply resume_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftRestore,ht]
  · simp only [MultitapeTM.step,liftRestore,ht]
  · simp only [MultitapeTM.step,liftRestore,ht]

private theorem resume_internal_restore_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (restoreMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((restoreMachine M).step^[s] c).state≠(restoreMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftRestore M n request resume c)=
      liftRestore M n request resume ((restoreMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      resume_internal_restore_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem resume_internal_restore_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (restoreMachine M).Cfg) (T : ℕ)
    (exit : ((restoreMachine M).step^[T] c).state=(restoreMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftRestore M n request resume c)=
      liftRestore M n request resume ((restoreMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := resume_internal_flatrecursiveschedulerprograms_first_exit (restoreMachine M)
    (fun q => q=(restoreMachine M).qHalt) (by intro d hd; exact resume_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [resume_internal_restore_iterate M n request resume c s hlive,he]

private theorem resume_internal_output_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (live : c.state≠(outputMachine M).qHalt) :
    (machine M n request resume).step (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step c) := by
  have ht : transition M n request resume (.output label c.state) (fun i => c.cells i (c.head i))=
      (let r := (outputMachine M).δ c.state (fun i => c.cells i (c.head i)); (.output label r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply resume_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftOutput,ht]
  · simp only [MultitapeTM.step,liftOutput,ht]
  · simp only [MultitapeTM.step,liftOutput,ht]

private theorem resume_internal_output_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((outputMachine M).step^[s] c).state≠(outputMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      resume_internal_output_step M n request resume label _ (live T (by omega)),Function.iterate_succ_apply']

private theorem resume_internal_output_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (T : ℕ)
    (exit : ((outputMachine M).step^[T] c).state=(outputMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := resume_internal_flatrecursiveschedulerprograms_first_exit (outputMachine M)
    (fun q => q=(outputMachine M).qHalt) (by intro d hd; exact resume_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [resume_internal_output_iterate M n request resume label c s hlive,he]

private theorem resume_internal_finish_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (live : c.state≠(finishMachine M).qHalt) :
    (machine M n request resume).step (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step c) := by
  have ht : transition M n request resume (.finish c.state) (fun i => c.cells i (c.head i))=
      (let r := (finishMachine M).δ c.state (fun i => c.cells i (c.head i)); (.finish r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply resume_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftFinish,ht]
  · simp only [MultitapeTM.step,liftFinish,ht]
  · simp only [MultitapeTM.step,liftFinish,ht]

private theorem resume_internal_finish_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((finishMachine M).step^[s] c).state≠(finishMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      resume_internal_finish_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem resume_internal_finish_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (T : ℕ)
    (exit : ((finishMachine M).step^[T] c).state=(finishMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := resume_internal_flatrecursiveschedulerprograms_first_exit (finishMachine M)
    (fun q => q=(finishMachine M).qHalt) (by intro d hd; exact resume_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [resume_internal_finish_iterate M n request resume c s hlive,he]

end IntMul.FlatRecursiveScheduler



namespace IntMul.FlatRecursiveScheduler

private theorem resume_internal_flatrecursiveschedulerdispatch_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem resume_internal_flatrecursiveschedulerdispatch_right_actions (M : MultitapeTM) (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M)
    (tape : Fin (M.k+3)) : moveActions M a tape .right=
      fun i => (a i,if i=tape then .right else .stay) := by
  classical
  funext i
  simp only [moveActions]
  split_ifs <;> cases a i <;> rfl

private theorem resume_internal_flatrecursiveschedulerdispatch_left_actions (M : MultitapeTM) (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M)
    (tape : Fin (M.k+3)) (present : a tape≠none) : moveActions M a tape .left=
      fun i => (a i,if i=tape then .left else .stay) := by
  classical
  funext i
  simp only [moveActions]
  by_cases hi : i=tape
  · subst i
    simp only [eq_self,if_true]
    cases h : a tape with
    | none => exact False.elim (present h)
    | some s => rfl
  · simp only [if_neg hi]
    cases a i <;> rfl

private theorem resume_internal_stay_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (q : State M n)
    (ht : transition M n request resume c.state (fun i => c.cells i (c.head i))=
      (q,fun i => (c.cells i (c.head i),.stay))) :
    (machine M n request resume).step c=relabel M n request resume q c := by
  apply resume_internal_flatrecursiveschedulerdispatch_cfg_ext
  · simp only [MultitapeTM.step,ht,relabel]
  · simp only [MultitapeTM.step,ht,relabel]
    funext i
    rw [Function.update_eq_self]
  · simp only [MultitapeTM.step,ht,relabel]

private theorem resume_internal_right_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (q : State M n) (tape : Fin (M.k+3))
    (ht : transition M n request resume c.state (fun i => c.cells i (c.head i))=
      (q,moveActions M (fun i => c.cells i (c.head i)) tape .right)) :
    (machine M n request resume).step c=headFrame M n request resume q c tape (c.head tape+1) := by
  classical
  rw [resume_internal_flatrecursiveschedulerdispatch_right_actions] at ht
  apply resume_internal_flatrecursiveschedulerdispatch_cfg_ext
  · simp only [MultitapeTM.step,ht,headFrame]
  · simp only [MultitapeTM.step,ht,headFrame]
    funext i
    rw [Function.update_eq_self]
  · simp only [MultitapeTM.step,ht,headFrame]
    funext i
    by_cases hi : i=tape
    · subst i
      simp
    · simp [hi]

private theorem resume_internal_left_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (q : State M n) (tape : Fin (M.k+3))
    (present : c.cells tape (c.head tape)≠none)
    (ht : transition M n request resume c.state (fun i => c.cells i (c.head i))=
      (q,moveActions M (fun i => c.cells i (c.head i)) tape .left)) :
    (machine M n request resume).step c=headFrame M n request resume q c tape (c.head tape-1) := by
  classical
  rw [resume_internal_flatrecursiveschedulerdispatch_left_actions M _ tape present] at ht
  apply resume_internal_flatrecursiveschedulerdispatch_cfg_ext
  · simp only [MultitapeTM.step,ht,headFrame]
  · simp only [MultitapeTM.step,ht,headFrame]
    funext i
    rw [Function.update_eq_self]
  · simp only [MultitapeTM.step,ht,headFrame]
    funext i
    by_cases hi : i=tape
    · subst i
      simp
    · simp [hi]

private theorem resume_internal_boot_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (exit : c.state=(bootMachine M).qHalt) :
    (machine M n request resume).step (liftBoot M n request resume c)=headFrame M n request resume (.preparation .mark) (liftBoot M n request resume c) (stackTape M) (c.head (stackTape M)+1) := by
  apply resume_internal_right_step
  change transition M n request resume (.boot c.state) _=_
  simp only [transition,if_pos exit]

private theorem resume_internal_preparation_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (exit : c.state=(preparationMachine M).qHalt) :
    (machine M n request resume).step (liftPreparation M n request resume c)=relabel M n request resume (.resetBuffer) (liftPreparation M n request resume c) := by
  apply resume_internal_stay_step
  change transition M n request resume (.preparation c.state) _=_
  simp only [transition,if_pos exit]

private theorem resume_internal_input_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (exit : c.state=(inputMachine M).qHalt) :
    (machine M n request resume).step (liftInput M n request resume label c)=relabel M n request resume (.push (.pushStart label)) (liftInput M n request resume label c) := by
  apply resume_internal_stay_step
  change transition M n request resume (.input label c.state) _=_
  simp only [transition,if_pos exit]

private theorem resume_internal_reservation_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (exit : c.state=(reservationMachine M).qHalt) :
    (machine M n request resume).step (liftReservation M n request resume c)=relabel M n request resume (.preparation .mark) (liftReservation M n request resume c) := by
  apply resume_internal_stay_step
  change transition M n request resume (.reservation c.state) _=_
  simp only [transition,if_pos exit]

private theorem resume_internal_return_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (exit : c.state=(returnMachine M).qHalt) :
    (machine M n request resume).step (liftReturn M n request resume c)=relabel M n request resume (.cleanup .rewind) (liftReturn M n request resume c) := by
  apply resume_internal_stay_step
  change transition M n request resume (.returning c.state) _=_
  simp only [transition,if_pos exit]

private theorem resume_internal_cleanup_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (exit : c.state=(cleanupMachine M).qHalt)
    (present : c.cells (stackTape M) (c.head (stackTape M))≠none) :
    (machine M n request resume).step (liftCleanup M n request resume c)=headFrame M n request resume (.inspectStack) (liftCleanup M n request resume c) (stackTape M) (c.head (stackTape M)-1) := by
  apply resume_internal_left_step M n request resume _ _ _ present
  change transition M n request resume (.cleanup c.state) _=_
  simp only [transition,if_pos exit]

private theorem resume_internal_restore_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (restoreMachine M).Cfg) (exit : c.state=(restoreMachine M).qHalt) :
    (machine M n request resume).step (liftRestore M n request resume c)=relabel M n request resume (.pop .popStart) (liftRestore M n request resume c) := by
  apply resume_internal_stay_step
  change transition M n request resume (.restore c.state) _=_
  simp only [transition,if_pos exit]

private theorem resume_internal_output_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (exit : c.state=(outputMachine M).qHalt) :
    (machine M n request resume).step (liftOutput M n request resume label c)=relabel M n request resume (.body (resume label)) (liftOutput M n request resume label c) := by
  apply resume_internal_stay_step
  change transition M n request resume (.output label c.state) _=_
  simp only [transition,if_pos exit]

private theorem resume_internal_finish_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (exit : c.state=(finishMachine M).qHalt) :
    (machine M n request resume).step (liftFinish M n request resume c)=relabel M n request resume (.halt) (liftFinish M n request resume c) := by
  apply resume_internal_stay_step
  change transition M n request resume (.finish c.state) _=_
  simp only [transition,if_pos exit]

private theorem resume_internal_body_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (exit : c.state=(bodyMachine M).qHalt) :
    (machine M n request resume).step (liftBody M n request resume c)=relabel M n request resume ( .returning (returnMachine M).qStart) (liftBody M n request resume c) := by
  apply resume_internal_stay_step
  change transition M n request resume (.body c.state) _=_
  simp only [transition,if_pos exit]

private theorem resume_internal_body_request_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (label : Fin n) (live : c.state≠M.qHalt)
    (call : request c.state=some label) :
    (machine M n request resume).step (liftBody M n request resume c)=
      relabel M n request resume (.input label .before) (liftBody M n request resume c) := by
  apply resume_internal_stay_step
  change transition M n request resume (.body c.state) _=_
  simp only [transition,if_neg live,call]

private theorem resume_internal_push_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (exit : c.state=.pushDone) :
    (machine M n request resume).step (liftPush M n request resume c)=
      relabel M n request resume (.reservation .seek) (liftPush M n request resume c) := by
  apply resume_internal_stay_step
  change transition M n request resume (.push c.state) _=_
  simp only [transition,if_pos exit]

private theorem resume_internal_pop_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (label : Fin n) (exit : c.state=.resume label) :
    (machine M n request resume).step (liftPop M n request resume c)=
      relabel M n request resume (.output label .before) (liftPop M n request resume c) := by
  apply resume_internal_stay_step
  change transition M n request resume (.pop c.state) _=_
  simp only [transition,exit]

private theorem resume_internal_inspect_root_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.inspectStack)
    (root : c.cells (stackTape M) (c.head (stackTape M))=none) :
    (machine M n request resume).step c=relabel M n request resume (.finish .rewind) c := by
  apply resume_internal_stay_step
  simp only [phase,transition,if_pos root]

private theorem resume_internal_inspect_parent_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.inspectStack)
    (parent : c.cells (stackTape M) (c.head (stackTape M))≠none) :
    (machine M n request resume).step c=
      headFrame M n request resume (.restore .rewind) c (stackTape M) (c.head (stackTape M)+1) := by
  apply resume_internal_right_step
  simp only [phase,transition,if_neg parent]

private theorem resume_internal_reset_marker_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.resetBuffer)
    (marker : c.cells (bufferTape M) (c.head (bufferTape M))=some (M.startSym,true)) :
    (machine M n request resume).step c=
      headFrame M n request resume (.body M.qStart) c (bufferTape M) (c.head (bufferTape M)+1) := by
  apply resume_internal_right_step
  simp only [phase,transition,if_pos marker]

private theorem resume_internal_reset_live_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.resetBuffer)
    (marker : c.cells (bufferTape M) (c.head (bufferTape M))≠some (M.startSym,true))
    (present : c.cells (bufferTape M) (c.head (bufferTape M))≠none) :
    (machine M n request resume).step c=
      headFrame M n request resume .resetBuffer c (bufferTape M) (c.head (bufferTape M)-1) := by
  apply resume_internal_left_step M n request resume _ _ _ present
  simp only [phase,transition,if_neg marker]

end IntMul.FlatRecursiveScheduler



namespace IntMul.FiniteContinuationStack

open IntMul.TrackedBankedSimulation (Sym)

private theorem resume_internal_finitecontinuationstacktape_zero_ne_one (M : MultitapeTM) : M.zero ≠ M.one := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,and_true] at hd
  tauto

private theorem resume_internal_decode_onehot (M : MultitapeTM) (n : ℕ) (q : Fin n) (j : ℕ) :
    TrackedBankedSimulation.decode M (some (M.bitSym (decide (j = q.val)),true)) = M.one ↔ j = q.val := by
  by_cases hj : j = q.val
  · simp [hj,MultitapeTM.bitSym,TrackedBankedSimulation.decode]
  · simp [hj,MultitapeTM.bitSym,TrackedBankedSimulation.decode,resume_internal_finitecontinuationstacktape_zero_ne_one M]

private theorem resume_internal_record_bit (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n)
    (j : ℕ) (r : ℕ) (hr : r < j) :
    recordTape M n base rho q j (rho + r + 1) = some (M.bitSym (decide (r = q.val)),true) := by
  simp [recordTape,show ¬rho + r + 1 < rho by omega,
    show rho + r + 1 ≠ rho by omega,show rho + r + 1 < rho + j + 1 by omega,
    show rho + r + 1 - rho - 1 = r by omega]

private theorem resume_internal_record_marker (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n) (j : ℕ) :
    recordTape M n base rho q j rho = some (M.sep,true) := by simp [recordTape]

private theorem resume_internal_fresh_at (M : MultitapeTM) (base : ℕ → Sym M) (rho p : ℕ) (hp : rho ≤ p) :
    freshTape M base rho p = some (M.blank,false) := by simp [freshTape,show ¬p < rho by omega]

private theorem resume_internal_marker_write (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n) :
    Function.update (freshTape M base rho) rho (some (M.sep,true)) = recordTape M n base rho q 0 := by
  funext p
  by_cases he : p = rho
  · subst p
    simp [recordTape]
  · rw [Function.update_of_ne he]
    by_cases hp : p < rho
    · simp [freshTape,recordTape,hp]
    · simp [freshTape,recordTape,hp,he,show ¬p < rho + 0 + 1 by omega]

private theorem resume_internal_bit_write (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n) (j : ℕ) :
    Function.update (recordTape M n base rho q j) (rho + j + 1)
      (some (M.bitSym (decide (j = q.val)),true)) = recordTape M n base rho q (j + 1) := by
  funext p
  by_cases he : p = rho + j + 1
  · subst p
    simp [recordTape,show ¬rho + j + 1 < rho by omega,show rho + j + 1 ≠ rho by omega,show rho + j + 1 - rho - 1 = j by omega]
  · rw [Function.update_of_ne he]
    by_cases hp : p < rho
    · simp [recordTape,hp]
    · by_cases hm : p = rho
      · simp [recordTape,hp,hm]
      · by_cases hj : p < rho + j + 1
        · simp [recordTape,hp,hm,hj,show p < rho + (j + 1) + 1 by omega]
        · simp [recordTape,hp,hm,hj,show ¬p < rho + (j + 1) + 1 by omega]

private theorem resume_internal_bit_erase (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n)
    (j : ℕ) (hj : j < n) :
    Function.update (recordTape M n base rho q (n - j)) (rho + (n - j)) (some (M.blank,false)) =
      recordTape M n base rho q (n - (j + 1)) := by
  funext p
  by_cases he : p = rho + (n - j)
  · subst p
    simp [recordTape,show ¬rho + (n - j) < rho by omega,show rho + (n - j) ≠ rho by omega,
      show ¬rho + (n - j) < rho + (n - (j + 1)) + 1 by omega,show n - j ≠ 0 by omega]
  · rw [Function.update_of_ne he]
    by_cases hp : p < rho
    · simp [recordTape,hp]
    · by_cases hm : p = rho
      · simp [recordTape,hp,hm]
      · by_cases hbit : p < rho + (n - (j + 1)) + 1
        · simp [recordTape,hp,hm,hbit,show p < rho + (n - j) + 1 by omega]
        · simp [recordTape,hp,hm,hbit,show ¬p < rho + (n - j) + 1 by omega]

private theorem resume_internal_marker_erase (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n) :
    Function.update (recordTape M n base rho q 0) rho (some (M.blank,false)) = freshTape M base rho := by
  funext p
  by_cases he : p = rho
  · subst p
    simp [freshTape]
  · rw [Function.update_of_ne he]
    by_cases hp : p < rho
    · simp [recordTape,freshTape,hp]
    · simp [recordTape,freshTape,hp,he,show ¬p < rho + 0 + 1 by omega]

/-- A correctly read one-hot bit updates a finite control register only.
No host memory stores the continuation. -/
private theorem resume_internal_recovered_step (n : ℕ) (q : Fin n) (j : ℕ) (hj : j < n) :
    (if n - 1 - j = q.val then some (⟨n - 1 - j,by omega⟩ : Fin n) else recovered n q j) =
      recovered n q (j + 1) := by
  unfold recovered
  by_cases he : n - 1 - j = q.val
  · rw [if_pos he,if_pos (by have := q.isLt; omega : n - q.val ≤ j + 1)]
    congr 1
    exact Fin.ext he
  · rw [if_neg he]
    by_cases hp : n - q.val ≤ j
    · rw [if_pos hp,if_pos (by omega : n - q.val ≤ j + 1)]
    · rw [if_neg hp,if_neg (by have := q.isLt; omega : ¬n - q.val ≤ j + 1)]

private theorem resume_internal_pop_scan (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ)
    (q : Fin n) (j : ℕ) (hj : j < n) :
    (popFrame M n base rho q j).cells (stackTape M) ((popFrame M n base rho q j).head (stackTape M)) =
      some (M.bitSym (decide (n - 1 - j = q.val)),true) := by
  simp only [popFrame,ite_true]
  have he : rho + (n - j) = rho + (n - 1 - j) + 1 := by omega
  rw [he,resume_internal_record_bit M n _ rho q (n - j) (n - 1 - j) (by omega)]

end IntMul.FiniteContinuationStack



namespace IntMul.FiniteContinuationStack

open IntMul.TrackedBankedSimulation (Sym)

private theorem resume_internal_finitecontinuationstacksteps_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem resume_internal_finitecontinuationstacksteps_raw_other (M : MultitapeTM) (n : ℕ) (q : State n)
    (a : Fin (M.k + 3) → Sym M) (i : Fin (M.k + 3)) (hi : i ≠ stackTape M) :
    (rawTransition M n q a).2 i = (a i,.stay) := by
  classical
  cases q <;> dsimp only [rawTransition] <;> split_ifs <;> simp_all

private theorem resume_internal_finitecontinuationstacksteps_protect_same_stay (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .stay = (a,.stay) := by cases a <;> rfl

/-- A tagged scan and tagged write make the physical protection wrapper
transparent; every non-stack tape remains exact and its head stays. -/
private theorem resume_internal_finitecontinuationstacksteps_physical_transition (M : MultitapeTM) (n : ℕ) (q : State n)
    (a : Fin (M.k + 3) → Sym M) (target : State n) (old write : M.Sym × Bool) (d : Move)
    (hs : a (stackTape M) = some old) (hstate : (rawTransition M n q a).1 = target)
    (hstack : (rawTransition M n q a).2 (stackTape M) = (some write,d)) :
    transition M n q a = (target,fun i => if i = stackTape M then (some write,d) else (a i,.stay)) := by
  classical
  apply Prod.ext
  · exact hstate
  · funext i
    change TrackedBankCleanup.protect M (a i) ((rawTransition M n q a).2 i).1
      ((rawTransition M n q a).2 i).2 = _
    by_cases hi : i = stackTape M
    · subst i
      rw [hstack,hs]
      simp only [TrackedBankCleanup.protect,ite_true]
    · rw [resume_internal_finitecontinuationstacksteps_raw_other M n q a i hi,resume_internal_finitecontinuationstacksteps_protect_same_stay]
      simp only [if_neg hi]

private theorem resume_internal_push_marker_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step (pushStartFrame M n base rho q) = pushFrame M n base rho q 0 := by
  let a := fun i => (pushStartFrame M n base rho q).cells i ((pushStartFrame M n base rho q).head i)
  have hs : a (stackTape M) = some (M.blank,false) := by
    simp [a,pushStartFrame,freshTape]
  have ht := resume_internal_finitecontinuationstacksteps_physical_transition M n (.pushStart q) a (pushFrame M n base rho q 0).state
    (M.blank,false) (M.sep,true) .right hs
    (by simp [rawTransition,pushFrame,show 0 < n by have := q.isLt; omega]) (by simp [rawTransition])
  dsimp only [a] at ht
  change transition M n (pushStartFrame M n base rho q).state _ = _ at ht
  apply resume_internal_finitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,pushStartFrame,pushFrame,ite_true]
      exact resume_internal_marker_write M n _ rho q
    · simp only [if_neg hi,pushStartFrame,pushFrame,if_neg hi]
      exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,pushStartFrame,pushFrame,ite_true,Nat.add_zero]
    · simp only [if_neg hi,pushStartFrame,pushFrame,if_neg hi]

private theorem resume_internal_push_bit_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ)
    (q : Fin n) (j : ℕ) (hj : j < n) :
    (machine M n).step (pushFrame M n base rho q j) = pushFrame M n base rho q (j + 1) := by
  let a := fun i => (pushFrame M n base rho q j).cells i ((pushFrame M n base rho q j).head i)
  have hs : a (stackTape M) = some (M.blank,false) := by
    simp [a,pushFrame,recordTape,show ¬rho + j + 1 < rho by omega,show rho + j + 1 ≠ rho by omega]
  have ht := resume_internal_finitecontinuationstacksteps_physical_transition M n (pushFrame M n base rho q j).state a
    (pushFrame M n base rho q (j + 1)).state (M.blank,false) (M.bitSym (decide (j = q.val)),true) .right hs
    (by simp only [pushFrame,dif_pos hj,rawTransition])
    (by simp only [pushFrame,dif_pos hj,rawTransition]; split_ifs <;> simp)
  dsimp only [a] at ht
  apply resume_internal_finitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,pushFrame,ite_true]
      exact resume_internal_bit_write M n _ rho q j
    · simp only [if_neg hi,pushFrame,if_neg hi]
      exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,pushFrame,ite_true]
      omega
    · simp only [if_neg hi,pushFrame,if_neg hi]

/-- One real transition switches from completed push to the pop routine.
A caller compiler can instead intercept pushDone to run its child. -/
private theorem resume_internal_push_dispatch (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step (pushFrame M n base rho q n) = popStartFrame M n base rho q := by
  have ht : transition M n (pushFrame M n base rho q n).state
      (fun i => (pushFrame M n base rho q n).cells i ((pushFrame M n base rho q n).head i)) =
      (.popStart,fun i => ((pushFrame M n base rho q n).cells i ((pushFrame M n base rho q n).head i),.stay)) := by
    simp only [pushFrame,dif_neg (by omega : ¬n < n),transition,rawTransition,resume_internal_finitecontinuationstacksteps_protect_same_stay]
  apply resume_internal_finitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    rfl

private theorem resume_internal_pop_start_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step (popStartFrame M n base rho q) = popFrame M n base rho q 0 := by
  let a := fun i => (popStartFrame M n base rho q).cells i ((popStartFrame M n base rho q).head i)
  have hs : a (stackTape M) = some (M.blank,false) := by
    simp [a,popStartFrame,pushFrame,recordTape,show ¬rho + n + 1 < rho by omega,
      show rho + n + 1 ≠ rho by omega]
  have hf : recovered n q 0 = none := by
    simp [recovered,show ¬n - q.val ≤ 0 by have := q.isLt; omega]
  have ht := resume_internal_finitecontinuationstacksteps_physical_transition M n .popStart a (popFrame M n base rho q 0).state
    (M.blank,false) (M.blank,false) .left hs
    (by simp only [rawTransition,if_pos (by have := q.isLt; omega : 0 < n),popFrame,
      dif_pos (by have := q.isLt; omega : 0 < n),hf])
    (by simp [rawTransition,show 0 < n by have := q.isLt; omega,hs])
  dsimp only [a] at ht
  change transition M n (popStartFrame M n base rho q).state _ = _ at ht
  apply resume_internal_finitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,popStartFrame,pushFrame,popFrame,ite_true,Nat.sub_zero]
      have hscan : recordTape M n (base.cells (stackTape M)) rho q n (rho + n + 1) = some (M.blank,false) := by
        simpa only [a,popStartFrame,pushFrame,ite_true] using hs
      rw [←hscan,Function.update_eq_self]
    · simp only [if_neg hi,popStartFrame,pushFrame,popFrame,if_neg hi]
      exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,popStartFrame,pushFrame,popFrame,ite_true,Nat.sub_zero]
      omega
    · simp only [if_neg hi,popStartFrame,pushFrame,popFrame,if_neg hi]

private theorem resume_internal_pop_bit_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ)
    (q : Fin n) (j : ℕ) (hj : j < n) :
    (machine M n).step (popFrame M n base rho q j) = popFrame M n base rho q (j + 1) := by
  classical
  let a := fun i => (popFrame M n base rho q j).cells i ((popFrame M n base rho q j).head i)
  have hs : a (stackTape M) = some (M.bitSym (decide (n - 1 - j = q.val)),true) :=
    resume_internal_pop_scan M n base rho q j hj
  have hpred : TrackedBankedSimulation.decode M (a (stackTape M)) = M.one ↔ n - 1 - j = q.val := by
    rw [hs]
    exact resume_internal_decode_onehot M n q (n - 1 - j)
  have hf : (if TrackedBankedSimulation.decode M (a (stackTape M)) = M.one then
      some (⟨n - 1 - j,by omega⟩ : Fin n) else recovered n q j) = recovered n q (j + 1) := by
    simpa only [hpred] using resume_internal_recovered_step n q j hj
  have ht := resume_internal_finitecontinuationstacksteps_physical_transition M n (popFrame M n base rho q j).state a
    (popFrame M n base rho q (j + 1)).state
    (M.bitSym (decide (n - 1 - j = q.val)),true) (M.blank,false) .left hs
    (by simp only [popFrame,dif_pos hj,rawTransition]; rw [hf])
    (by simp only [popFrame,dif_pos hj,rawTransition]; split_ifs <;> simp)
  dsimp only [a] at ht
  apply resume_internal_finitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,popFrame,ite_true]
      exact resume_internal_bit_erase M n _ rho q j hj
    · simp only [if_neg hi,popFrame,if_neg hi]
      exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,popFrame,ite_true]
      omega
    · simp only [if_neg hi,popFrame,if_neg hi]

/-- The last physical pop transition erases the separator and enters the
finite resume state containing the recovered label, retaining older records. -/
private theorem resume_internal_pop_marker_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step (popFrame M n base rho q n) = finalFrame M n base rho q := by
  let a := fun i => (popFrame M n base rho q n).cells i ((popFrame M n base rho q n).head i)
  have hs : a (stackTape M) = some (M.sep,true) := by
    simp [a,popFrame,recordTape]
  have hf : recovered n q n = some q := by simp [recovered]
  have ht := resume_internal_finitecontinuationstacksteps_physical_transition M n (popFrame M n base rho q n).state a (.resume q)
    (M.sep,true) (M.blank,false) .stay hs
    (by simp only [popFrame,dif_neg (by omega : ¬n < n),hf,rawTransition,if_pos hs])
    (by simp [popFrame,hf,rawTransition])
  dsimp only [a] at ht
  apply resume_internal_finitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,popFrame,finalFrame,pushStartFrame,ite_true,Nat.sub_self,Nat.add_zero]
      exact resume_internal_marker_erase M n _ rho q
    · simp only [if_neg hi,popFrame,finalFrame,pushStartFrame,if_neg hi]
      exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,popFrame,finalFrame,pushStartFrame,ite_true,Nat.sub_self,Nat.add_zero]
    · simp only [if_neg hi,popFrame,finalFrame,pushStartFrame,if_neg hi]

end IntMul.FiniteContinuationStack




namespace IntMul.FlatRecursiveStack

open IntMul.FlatRecursiveScheduler

private theorem resume_internal_flatrecursivestack_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem resume_internal_push_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (live : c.state≠.pushDone) :
    (machine M n request resume).step (liftPush M n request resume c)=
      liftPush M n request resume ((FiniteContinuationStack.machine M n).step c) := by
  have ht : transition M n request resume (.push c.state) (fun i => c.cells i (c.head i))=
      (let r := FiniteContinuationStack.transition M n c.state (fun i => c.cells i (c.head i)); (.push r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply resume_internal_flatrecursivestack_cfg_ext
  · simp only [MultitapeTM.step,liftPush,ht]
  · simp only [MultitapeTM.step,liftPush,ht]
  · simp only [MultitapeTM.step,liftPush,ht]

private theorem resume_internal_push_run (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (FiniteContinuationStack.machine M n).Cfg) (rho : ℕ) (label : Fin n) (j : ℕ) (hj : j ≤ n) :
    (machine M n request resume).step^[j]
      (liftPush M n request resume (FiniteContinuationStack.pushFrame M n base rho label 0))=
      liftPush M n request resume (FiniteContinuationStack.pushFrame M n base rho label j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hlive : (FiniteContinuationStack.pushFrame M n base rho label j).state≠.pushDone := by
      simp only [FiniteContinuationStack.pushFrame,dif_pos (by omega : j < n)]
      simp
    rw [Function.iterate_succ_apply',ih (by omega),resume_internal_push_step M n request resume _ hlive,
      FiniteContinuationStack.resume_internal_push_bit_step M n base rho label j (by omega)]

private theorem resume_internal_push_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (FiniteContinuationStack.machine M n).Cfg) (rho : ℕ) (label : Fin n) :
    (machine M n request resume).step^[n+1]
      (liftPush M n request resume (FiniteContinuationStack.pushStartFrame M n base rho label))=
      liftPush M n request resume (FiniteContinuationStack.pushFrame M n base rho label n) := by
  have hlive : (FiniteContinuationStack.pushStartFrame M n base rho label).state≠.pushDone := by simp [FiniteContinuationStack.pushStartFrame]
  rw [Function.iterate_add_apply,Function.iterate_one,resume_internal_push_step M n request resume _ hlive,
    FiniteContinuationStack.resume_internal_push_marker_step,resume_internal_push_run M n request resume base rho label n le_rfl]

private theorem resume_internal_pop_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (live : ∀ label, c.state≠.resume label) :
    (machine M n request resume).step (liftPop M n request resume c)=
      liftPop M n request resume ((FiniteContinuationStack.machine M n).step c) := by
  have ht : transition M n request resume (.pop c.state) (fun i => c.cells i (c.head i))=
      (let r := FiniteContinuationStack.transition M n c.state (fun i => c.cells i (c.head i)); (.pop r.1,r.2)) := by
    cases hs : c.state <;> first | rfl | skip
    rename_i label
    exact False.elim (live label hs)
  apply resume_internal_flatrecursivestack_cfg_ext
  · simp only [MultitapeTM.step,liftPop,ht]
  · simp only [MultitapeTM.step,liftPop,ht]
  · simp only [MultitapeTM.step,liftPop,ht]

private theorem resume_internal_pop_run (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (FiniteContinuationStack.machine M n).Cfg) (rho : ℕ) (label : Fin n) (j : ℕ) (hj : j ≤ n) :
    (machine M n request resume).step^[j]
      (liftPop M n request resume (FiniteContinuationStack.popFrame M n base rho label 0))=
      liftPop M n request resume (FiniteContinuationStack.popFrame M n base rho label j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hlive : ∀ q, (FiniteContinuationStack.popFrame M n base rho label j).state≠.resume q := by
      intro q
      simp only [FiniteContinuationStack.popFrame,dif_pos (by omega : j < n)]
      simp
    rw [Function.iterate_succ_apply',ih (by omega),resume_internal_pop_step M n request resume _ hlive,
      FiniteContinuationStack.resume_internal_pop_bit_step M n base rho label j (by omega)]

private theorem resume_internal_pop_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (FiniteContinuationStack.machine M n).Cfg) (rho : ℕ) (label : Fin n) :
    (machine M n request resume).step^[n+2]
      (liftPop M n request resume (FiniteContinuationStack.popStartFrame M n base rho label))=
      liftPop M n request resume (FiniteContinuationStack.finalFrame M n base rho label) := by
  have hlive : ∀ q, (FiniteContinuationStack.popStartFrame M n base rho label).state≠.resume q := by
    intro q
    simp [FiniteContinuationStack.popStartFrame]
  have hr : (machine M n request resume).step^[n+1]
      (liftPop M n request resume (FiniteContinuationStack.popStartFrame M n base rho label))=
      liftPop M n request resume (FiniteContinuationStack.popFrame M n base rho label n) := by
    rw [Function.iterate_add_apply,Function.iterate_one,resume_internal_pop_step M n request resume _ hlive,
      FiniteContinuationStack.resume_internal_pop_start_step,resume_internal_pop_run M n request resume base rho label n le_rfl]
  have hm : ∀ q, (FiniteContinuationStack.popFrame M n base rho label n).state≠.resume q := by
    intro q
    simp [FiniteContinuationStack.popFrame]
  rw [show n+2=(n+1)+1 by omega,Function.iterate_succ_apply',hr,resume_internal_pop_step M n request resume _ hm,
    FiniteContinuationStack.resume_internal_pop_marker_step]

end IntMul.FlatRecursiveStack



namespace IntMul.FlatRecursiveResume

open IntMul.FlatRecursiveScheduler
open IntMul.FlatRecursiveCall
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)
open IntMul.TrackedBankReservation (newOffsets)

private noncomputable def resume_internal_physicalWork (M : MultitapeTM) (j : Fin M.k) : Fin (M.k+3) :=
  FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) (workTape M j)

private theorem resume_internal_work_not_stack (M : MultitapeTM) (j : Fin M.k) : resume_internal_physicalWork M j≠stackTape M := by
  intro h
  have h := congrArg Fin.val h
  simp only [resume_internal_physicalWork,FixedTapeExtension.oldTape,workTape,stackTape,FiniteContinuationStack.stackTape] at h
  have := j.isLt
  omega

private theorem resume_internal_child_work (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (j : Fin M.k) :
    (childBase M n request resume base rho sigma offset extent c label).cells (resume_internal_physicalWork M j)=
      (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma []) offset extent c).cells
        (workTape M j) := by
  simp only [childBase,if_neg (resume_internal_work_not_stack M j)]
  have hn : (resume_internal_physicalWork M j).val≠1 := by simp only [resume_internal_physicalWork,FixedTapeExtension.oldTape,workTape]; omega
  simp only [if_neg hn,bodyFrame,liftBody]
  simp only [resume_internal_physicalWork,resume_internal_extension_old_cells]

private theorem resume_internal_child_work_fresh (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) (j : Fin M.k) :
    TrackedBankCleanup.freshTape M
      ((childBase M n request resume base rho sigma offset extent c label).cells (resume_internal_physicalWork M j))
      (newOffsets M offset extent j)=
      (childBase M n request resume base rho sigma offset extent c label).cells (resume_internal_physicalWork M j) := by
  funext p
  by_cases hp : p < newOffsets M offset extent j
  · simp only [TrackedBankCleanup.freshTape,if_pos hp]
  · simp only [TrackedBankCleanup.freshTape,if_neg hp]
    have ho : offset j≤ p := by unfold newOffsets at hp; omega
    have he : extent j < p-offset j := by unfold newOffsets at hp; omega
    rw [resume_internal_child_work]
    have h := resume_internal_embed_work M (parentBase M n request resume base sigma []) offset extent c j (p-offset j)
    rw [show offset j+(p-offset j)=p by omega] at h
    rw [h,tail j (p-offset j) he]
    simp only [decide_eq_false_iff_not.mpr (by omega : ¬p-offset j≤ extent j)]

private theorem resume_internal_inspection_work (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) (j : Fin M.k) :
    (childInspection M n request resume base rho sigma offset extent c label w).cells (resume_internal_physicalWork M j)=
      (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma []) offset extent c).cells
        (workTape M j) := by
  simp only [childInspection,FlatRecursiveReturn.inspectionFrame,resume_internal_physicalWork,FixedTapeExtension.oldTape,workTape]
  rw [dif_pos (by have := j.isLt; omega),dif_pos (by omega)]
  have hi : innerTape M ⟨j.val+2,by have := j.isLt; omega⟩ (by change 2≤ j.val+2; omega)=j := by
    apply Fin.ext; simp [innerTape]
  rw [hi]
  change TrackedBankCleanup.freshTape M
    ((childBase M n request resume base rho sigma offset extent c label).cells (resume_internal_physicalWork M j))
    (newOffsets M offset extent j)=_
  rw [resume_internal_child_work_fresh M n request resume base rho sigma offset extent c label tail j,resume_internal_child_work]
  rfl

private theorem resume_internal_inspection_work_head (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) (j : Fin M.k) :
    (childInspection M n request resume base rho sigma offset extent c label w).head (resume_internal_physicalWork M j)=
      newOffsets M offset extent j := by
  simp only [childInspection,FlatRecursiveReturn.inspectionFrame,resume_internal_physicalWork,FixedTapeExtension.oldTape,workTape]
  rw [dif_pos (by have := j.isLt; omega),dif_pos (by omega)]
  congr 1

private theorem resume_internal_inspection_stack (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (childInspection M n request resume base rho sigma offset extent c label w).cells (stackTape M)=
      FiniteContinuationStack.recordTape M n (base.cells (stackTape M)) rho label n ∧
    (childInspection M n request resume base rho sigma offset extent c label w).head (stackTape M)=rho+n := by
  have hi : ¬(stackTape M).val < M.k+2 := by simp [stackTape,FiniteContinuationStack.stackTape]
  have hn : 0 < n := by have := label.isLt; omega
  constructor
  · simp only [childInspection,FlatRecursiveReturn.inspectionFrame,dif_neg hi,childBase,if_true]
    funext p
    by_cases hp : p < rho+n+1
    · simp only [FiniteContinuationStack.freshTape,if_pos hp]
    · simp only [FiniteContinuationStack.freshTape,if_neg hp,FiniteContinuationStack.recordTape,
        if_neg (by omega : ¬p < rho),if_neg (by omega : p≠rho),if_neg hp]
  · simp only [childInspection,FlatRecursiveReturn.inspectionFrame,dif_neg hi]
    omega

private theorem resume_internal_inspection_nonroot (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (childInspection M n request resume base rho sigma offset extent c label w).cells (stackTape M)
      ((childInspection M n request resume base rho sigma offset extent c label w).head (stackTape M))≠none := by
  have h := resume_internal_inspection_stack M n request resume base rho sigma offset extent c label w
  rw [h.1,h.2]
  have hn : 0 < n := by have := label.isLt; omega
  simp [FiniteContinuationStack.recordTape,hn.ne',show ¬rho+n < rho by omega,show rho+n≠rho by omega]

end IntMul.FlatRecursiveResume



namespace IntMul.FlatRecursiveResume

open IntMul.FlatRecursiveScheduler
open IntMul.FlatRecursiveCall
open IntMul.TrackedBankedSimulation (Sym)

private theorem resume_internal_flatrecursiveresumelowframes_buffer_replace (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (v w : List Bool) :
    TrackedOutputReturn.bufferTape M (TrackedOutputReturn.bufferTape M base sigma v) sigma w=
      TrackedOutputReturn.bufferTape M base sigma w := by
  funext p
  by_cases hp : p < sigma <;> simp only [TrackedOutputReturn.bufferTape,hp,if_true,if_false]

private theorem resume_internal_inspection_buffer (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (childInspection M n request resume base rho sigma offset extent c label w).cells (bufferTape M)=
      TrackedOutputReturn.bufferTape M (base.cells (bufferTape M)) sigma w ∧
    (childInspection M n request resume base rho sigma offset extent c label w).head (bufferTape M)=sigma+w.length+1 := by
  have hs : bufferTape M≠stackTape M := by
    intro h; have := congrArg Fin.val h; simp [bufferTape,stackTape,FiniteContinuationStack.stackTape] at this
  constructor
  · simp only [childInspection,FlatRecursiveReturn.inspectionFrame,bufferTape]
    rw [dif_pos (by omega),dif_neg (by omega)]
    simp only [if_true,childBase]
    change (⟨1,by omega⟩ : Fin (M.k+3))≠stackTape M at hs
    rw [if_neg hs]
    exact resume_internal_flatrecursiveresumelowframes_buffer_replace M _ sigma [] w
  · simp [childInspection,FlatRecursiveReturn.inspectionFrame,bufferTape]

private theorem resume_internal_inspection_root (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (childInspection M n request resume base rho sigma offset extent c label w).cells ⟨0,by change 0 < M.k+3; omega⟩=
      base.cells ⟨0,by change 0 < M.k+3; omega⟩ ∧
    (childInspection M n request resume base rho sigma offset extent c label w).head ⟨0,by change 0 < M.k+3; omega⟩=
      base.head ⟨0,by change 0 < M.k+3; omega⟩ := by
  have hs : (⟨0,by omega⟩ : Fin (M.k+3))≠stackTape M := by
    intro h; have := congrArg Fin.val h; simp [stackTape,FiniteContinuationStack.stackTape] at this
  constructor
  · simp only [childInspection,FlatRecursiveReturn.inspectionFrame]
    rw [dif_pos (by omega),dif_neg (by omega)]
    simp only [if_false,childBase,if_neg hs,bodyFrame,liftBody,FixedTapeExtension.embed]
    rw [dif_pos (by omega)]
    simp [TrackedBankedSimulation.embed,parentBase,FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
  · simp only [childInspection,FlatRecursiveReturn.inspectionFrame]
    rw [dif_pos (by omega),dif_neg (by omega)]
    simp only [if_false,childBase,if_neg hs]
    rw [dif_pos (by omega),dif_neg (by omega)]
    simp

end IntMul.FlatRecursiveResume



namespace IntMul.FlatRecursiveResume

open IntMul.FlatRecursiveScheduler
open IntMul.FlatRecursiveCall
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)
open IntMul.TrackedBankReservation (newOffsets)

private theorem resume_internal_flatrecursiveresumerestoreframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def resume_internal_restoreParent (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (TrackedParentRestore.machine M).Cfg where
  state := .rewind
  cells := fun i => (childInspection M n request resume base rho sigma offset extent c label w).cells
    (FixedTapeExtension.oldTape (TrackedParentRestore.machine M) i)
  head := fun i => (childInspection M n request resume base rho sigma offset extent c label w).head
    (FixedTapeExtension.oldTape (TrackedParentRestore.machine M) i)

private noncomputable def resume_internal_restorePadBase (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (restoreMachine M).Cfg where
  state := .rewind
  cells := (childInspection M n request resume base rho sigma offset extent c label w).cells
  head := Function.update
    (childInspection M n request resume base rho sigma offset extent c label w).head (stackTape M) (rho+n+1)

private noncomputable def resume_internal_restoreStart (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (restoreMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedParentRestore.machine M)
    (resume_internal_restorePadBase M n request resume base rho sigma offset extent c label w)
    (TrackedParentRestore.initialFrame M
      (resume_internal_restoreParent M n request resume base rho sigma offset extent c label w)
      offset extent c (fun j => extent j+1))

private noncomputable def resume_internal_restoreFinal (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (restoreMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedParentRestore.machine M)
    (resume_internal_restorePadBase M n request resume base rho sigma offset extent c label w)
    (TrackedParentRestore.finalFrame M
      (resume_internal_restoreParent M n request resume base rho sigma offset extent c label w) offset extent c)

private theorem resume_internal_restore_parent_canonical (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) (j : Fin M.k) (p : ℕ) :
    (resume_internal_restoreParent M n request resume base rho sigma offset extent c label w).cells (workTape M j) (offset j+p)=
      some (c.cells j p,decide (p≤ extent j)) := by
  change (childInspection M n request resume base rho sigma offset extent c label w).cells (resume_internal_physicalWork M j) (offset j+p)=_
  rw [resume_internal_inspection_work M n request resume base rho sigma offset extent c label w tail j]
  exact resume_internal_embed_work M _ offset extent c j p

private theorem resume_internal_restore_parent_head (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) (j : Fin M.k) :
    (resume_internal_restoreParent M n request resume base rho sigma offset extent c label w).head (workTape M j)=
      offset j+(extent j+1) := by
  change (childInspection M n request resume base rho sigma offset extent c label w).head (resume_internal_physicalWork M j)=_
  rw [resume_internal_inspection_work_head,newOffsets]
  omega

private theorem resume_internal_inspection_restore_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    headFrame M n request resume (.restore .rewind)
      (childInspection M n request resume base rho sigma offset extent c label w)
      (stackTape M) (rho+n+1)=
    liftRestore M n request resume (resume_internal_restoreStart M n request resume base rho sigma offset extent c label w) := by
  have hc : (TrackedParentRestore.initialFrame M
      (resume_internal_restoreParent M n request resume base rho sigma offset extent c label w) offset extent c (fun j => extent j+1)).cells=
      (resume_internal_restoreParent M n request resume base rho sigma offset extent c label w).cells := by
    exact resume_internal_embed_cells_ready M _ offset extent c (resume_internal_restore_parent_canonical M n request resume base rho sigma offset extent c label w tail)
  have hh : (TrackedParentRestore.initialFrame M
      (resume_internal_restoreParent M n request resume base rho sigma offset extent c label w) offset extent c (fun j => extent j+1)).head=
      (resume_internal_restoreParent M n request resume base rho sigma offset extent c label w).head := by
    funext i
    simp only [TrackedParentRestore.initialFrame,TrackedParentRestore.rewindFrame,Nat.sub_zero]
    by_cases hw : 2≤ i.val
    · simp only [dif_pos hw]
      have h := resume_internal_restore_parent_head M n request resume base rho sigma offset extent c label w (innerTape M i hw)
      rw [resume_internal_work_inner M i hw] at h
      exact h.symm
    · simp only [dif_neg hw]
  apply resume_internal_flatrecursiveresumerestoreframes_cfg_ext
  · rfl
  · funext i
    simp only [headFrame,liftRestore,resume_internal_restoreStart,FixedTapeExtension.embed]
    rw [hc]
    simp only [resume_internal_restoreParent,resume_internal_restorePadBase]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
    · simp only [dif_neg hi]
  · funext i
    simp only [headFrame,liftRestore,resume_internal_restoreStart,FixedTapeExtension.embed]
    rw [hh]
    simp only [resume_internal_restoreParent,resume_internal_restorePadBase]
    by_cases hi : i.val < M.k+2
    · have hs : i≠stackTape M := by intro h; have := congrArg Fin.val h; simp [stackTape,FiniteContinuationStack.stackTape] at this; omega
      simp only [dif_pos hi,Function.update_of_ne hs,FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
    · simp only [dif_neg hi]

end IntMul.FlatRecursiveResume



namespace IntMul.FlatRecursiveResume

open IntMul.FlatRecursiveScheduler
open IntMul.FlatRecursiveCall
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem resume_internal_flatrecursiveresumestackframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def resume_internal_popParent (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (FiniteContinuationStack.machine M n).Cfg where
  state := .popStart
  cells := (resume_internal_restoreFinal M n request resume base rho sigma offset extent c label w).cells
  head := (resume_internal_restoreFinal M n request resume base rho sigma offset extent c label w).head

private noncomputable def resume_internal_popped (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (FiniteContinuationStack.machine M n).Cfg :=
  FiniteContinuationStack.finalFrame M n
    (resume_internal_popParent M n request resume base rho sigma offset extent c label w) rho label

private theorem resume_internal_restore_stack (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (resume_internal_restoreFinal M n request resume base rho sigma offset extent c label w).cells (stackTape M)=
      FiniteContinuationStack.recordTape M n (base.cells (stackTape M)) rho label n ∧
    (resume_internal_restoreFinal M n request resume base rho sigma offset extent c label w).head (stackTape M)=rho+n+1 := by
  have he : stackTape M=FixedTapeExtension.extraTape (TrackedParentRestore.machine M) := by apply Fin.ext; rfl
  constructor
  · simp only [resume_internal_restoreFinal,he,resume_internal_extension_extra_cells,resume_internal_restorePadBase]
    rw [he.symm]
    exact (resume_internal_inspection_stack M n request resume base rho sigma offset extent c label w).1
  · simp only [resume_internal_restoreFinal,he,resume_internal_extension_extra_heads,resume_internal_restorePadBase]
    rw [he.symm]
    simp only [Function.update_self]

private theorem resume_internal_restore_pop_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    relabel M n request resume (.pop .popStart)
      (liftRestore M n request resume (resume_internal_restoreFinal M n request resume base rho sigma offset extent c label w))=
    liftPop M n request resume (FiniteContinuationStack.popStartFrame M n
      (resume_internal_popParent M n request resume base rho sigma offset extent c label w) rho label) := by
  have hs := resume_internal_restore_stack M n request resume base rho sigma offset extent c label w
  apply resume_internal_flatrecursiveresumestackframes_cfg_ext
  · rfl
  · funext i p
    simp only [relabel,liftRestore,liftPop,FiniteContinuationStack.popStartFrame,
      FiniteContinuationStack.pushFrame,resume_internal_popParent]
    by_cases hi : i=stackTape M
    · subst i
      simp only [if_true,hs.1]
      by_cases hp : p < rho <;> simp only [FiniteContinuationStack.recordTape,hp,if_true,if_false]
    · simp only [if_neg hi]
  · funext i
    simp only [relabel,liftRestore,liftPop,FiniteContinuationStack.popStartFrame,
      FiniteContinuationStack.pushFrame,resume_internal_popParent]
    by_cases hi : i=stackTape M
    · subst i
      simp only [if_true,hs.2]
    · simp only [if_neg hi]

private theorem resume_internal_popped_stack (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (resume_internal_popped M n request resume base rho sigma offset extent c label w).cells (stackTape M)=
      FiniteContinuationStack.freshTape M (base.cells (stackTape M)) rho ∧
    (resume_internal_popped M n request resume base rho sigma offset extent c label w).head (stackTape M)=rho := by
  constructor
  · simp only [resume_internal_popped,FiniteContinuationStack.finalFrame,FiniteContinuationStack.pushStartFrame,if_true,resume_internal_popParent,
      (resume_internal_restore_stack M n request resume base rho sigma offset extent c label w).1]
    funext p
    by_cases hp : p < rho <;> simp only [FiniteContinuationStack.freshTape,FiniteContinuationStack.recordTape,hp,if_true,if_false]
  · simp only [resume_internal_popped,FiniteContinuationStack.finalFrame,FiniteContinuationStack.pushStartFrame,if_true]

end IntMul.FlatRecursiveResume



namespace IntMul.FlatRecursiveResume

open IntMul.FlatRecursiveScheduler
open IntMul.FlatRecursiveCall
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem resume_internal_flatrecursiveresumeoutputframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def resume_internal_parkedParent (M : MultitapeTM) (c : M.Cfg) : M.Cfg where
  state := c.state
  cells := c.cells
  head := fun _ => 0

private noncomputable def resume_internal_outputParent (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (TrackedParentOutputBridge.machine M).Cfg where
  state := .before
  cells := fun i => (resume_internal_popped M n request resume base rho sigma offset extent c label w).cells
    (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) i)
  head := fun i => (resume_internal_popped M n request resume base rho sigma offset extent c label w).head
    (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) i)

private noncomputable def resume_internal_outputPadBase (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (outputMachine M).Cfg where
  state := .before
  cells := (resume_internal_popped M n request resume base rho sigma offset extent c label w).cells
  head := (resume_internal_popped M n request resume base rho sigma offset extent c label w).head

private noncomputable def resume_internal_outputStart (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (outputMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedParentOutputBridge.machine M)
    (resume_internal_outputPadBase M n request resume base rho sigma offset extent c label w)
    (TrackedParentOutputBridge.initialFrame M
      (resume_internal_outputParent M n request resume base rho sigma offset extent c label w)
      sigma offset extent (resume_internal_parkedParent M c) w)

private noncomputable def resume_internal_outputFinal (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (outputMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedParentOutputBridge.machine M)
    (resume_internal_outputPadBase M n request resume base rho sigma offset extent c label w)
    (TrackedParentOutputBridge.finalFrame M
      (resume_internal_outputParent M n request resume base rho sigma offset extent c label w)
      sigma offset extent (resume_internal_parkedParent M c) w)

private theorem resume_internal_old_ne_stack (M : MultitapeTM) (i : Fin (M.k+2)) :
    FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) i≠stackTape M := by
  intro h
  have h := congrArg Fin.val h
  simp only [FixedTapeExtension.oldTape,stackTape,FiniteContinuationStack.stackTape] at h
  have := i.isLt
  omega

private theorem resume_internal_output_parent_cells (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) (i : Fin (M.k+2)) :
    (resume_internal_outputParent M n request resume base rho sigma offset extent c label w).cells i=
      (TrackedParentRestore.finalFrame M
        (resume_internal_restoreParent M n request resume base rho sigma offset extent c label w) offset extent c).cells i := by
  simp only [resume_internal_outputParent,resume_internal_popped,FiniteContinuationStack.finalFrame,FiniteContinuationStack.pushStartFrame,
    if_neg (resume_internal_old_ne_stack M i),resume_internal_popParent]
  rw [show FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) i=
    FixedTapeExtension.oldTape (TrackedParentRestore.machine M) i by rfl]
  exact resume_internal_extension_old_cells (TrackedParentRestore.machine M) _ _ i

private theorem resume_internal_output_parent_heads (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) (i : Fin (M.k+2)) :
    (resume_internal_outputParent M n request resume base rho sigma offset extent c label w).head i=
      (TrackedParentRestore.finalFrame M
        (resume_internal_restoreParent M n request resume base rho sigma offset extent c label w) offset extent c).head i := by
  simp only [resume_internal_outputParent,resume_internal_popped,FiniteContinuationStack.finalFrame,FiniteContinuationStack.pushStartFrame,
    if_neg (resume_internal_old_ne_stack M i),resume_internal_popParent]
  rw [show FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) i=
    FixedTapeExtension.oldTape (TrackedParentRestore.machine M) i by rfl]
  exact resume_internal_extension_old_heads (TrackedParentRestore.machine M) _ _ i

private theorem resume_internal_output_parent_work (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) (j : Fin M.k) (p : ℕ) :
    (resume_internal_outputParent M n request resume base rho sigma offset extent c label w).cells (workTape M j) (offset j+p)=
      some ((resume_internal_parkedParent M c).cells j p,decide (p≤ extent j)) := by
  rw [resume_internal_output_parent_cells]
  exact resume_internal_embed_work M _ offset extent c j p

private theorem resume_internal_output_parent_work_head (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) (j : Fin M.k) :
    (resume_internal_outputParent M n request resume base rho sigma offset extent c label w).head (workTape M j)=offset j := by
  rw [resume_internal_output_parent_heads]
  simp only [TrackedParentRestore.finalFrame,workTape]
  rw [dif_pos (by omega)]
  congr 1

private theorem resume_internal_output_parent_buffer (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (resume_internal_outputParent M n request resume base rho sigma offset extent c label w).cells (TrackedParentOutputBridge.bufferTape M)=
      TrackedOutputReturn.bufferTape M (base.cells (bufferTape M)) sigma w ∧
    (resume_internal_outputParent M n request resume base rho sigma offset extent c label w).head (TrackedParentOutputBridge.bufferTape M)=sigma+w.length+1 := by
  constructor
  · rw [resume_internal_output_parent_cells]
    simp only [TrackedParentRestore.finalFrame,TrackedBankedSimulation.embed,TrackedParentOutputBridge.bufferTape]
    simp only [dif_neg (by omega : ¬2≤ (1:ℕ))]
    change (childInspection M n request resume base rho sigma offset extent c label w).cells (bufferTape M)=_
    exact (resume_internal_inspection_buffer M n request resume base rho sigma offset extent c label w).1
  · rw [resume_internal_output_parent_heads]
    simp only [TrackedParentRestore.finalFrame,TrackedParentOutputBridge.bufferTape]
    simp only [dif_neg (by omega : ¬2≤ (1:ℕ))]
    change (childInspection M n request resume base rho sigma offset extent c label w).head (bufferTape M)=_
    exact (resume_internal_inspection_buffer M n request resume base rho sigma offset extent c label w).2


private theorem resume_internal_flatrecursiveresumeoutputframes_buffer_idem (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List Bool) :
    TrackedOutputReturn.bufferTape M (TrackedOutputReturn.bufferTape M base sigma w) sigma w=
      TrackedOutputReturn.bufferTape M base sigma w := by
  funext p
  by_cases hp : p < sigma <;> simp only [TrackedOutputReturn.bufferTape,hp,if_true,if_false]

private theorem resume_internal_output_initial_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (TrackedParentOutputBridge.initialFrame M
      (resume_internal_outputParent M n request resume base rho sigma offset extent c label w)
      sigma offset extent (resume_internal_parkedParent M c) w).cells=
      (resume_internal_outputParent M n request resume base rho sigma offset extent c label w).cells ∧
    (TrackedParentOutputBridge.initialFrame M
      (resume_internal_outputParent M n request resume base rho sigma offset extent c label w)
      sigma offset extent (resume_internal_parkedParent M c) w).head=
      (resume_internal_outputParent M n request resume base rho sigma offset extent c label w).head := by
  let B := resume_internal_outputParent M n request resume base rho sigma offset extent c label w
  have hbuf := resume_internal_output_parent_buffer M n request resume base rho sigma offset extent c label w
  have hbc : (TrackedParentOutputBridge.parentBase M B sigma w).cells=B.cells := by
    funext i
    simp only [TrackedParentOutputBridge.parentBase]
    by_cases hb : i=TrackedParentOutputBridge.bufferTape M
    · subst i
      simp only [if_true]
      rw [hbuf.1]
      exact resume_internal_flatrecursiveresumeoutputframes_buffer_idem M _ sigma w
    · simp only [if_neg hb]
  have hbh : (TrackedParentOutputBridge.parentBase M B sigma w).head=B.head := by
    funext i
    simp only [TrackedParentOutputBridge.parentBase]
    by_cases hb : i=TrackedParentOutputBridge.bufferTape M
    · subst i
      simp only [if_true]
      exact hbuf.2.symm
    · simp only [if_neg hb]
  have hc : (TrackedBankedSimulation.embed M (TrackedParentOutputBridge.parentBase M B sigma w)
      offset extent (resume_internal_parkedParent M c)).cells=B.cells := by
    have h := resume_internal_embed_cells_ready M (TrackedParentOutputBridge.parentBase M B sigma w) offset extent (resume_internal_parkedParent M c)
      (by rw [hbc]; exact resume_internal_output_parent_work M n request resume base rho sigma offset extent c label w)
    rw [hbc] at h
    exact h
  have hh : (TrackedBankedSimulation.embed M (TrackedParentOutputBridge.parentBase M B sigma w)
      offset extent (resume_internal_parkedParent M c)).head=B.head := by
    have h := resume_internal_embed_heads_ready M (TrackedParentOutputBridge.parentBase M B sigma w) offset extent (resume_internal_parkedParent M c)
      (by intro j; rw [hbh,resume_internal_output_parent_work_head]; rfl)
    rw [hbh] at h
    exact h
  constructor
  · exact hc
  · funext i
    simp only [TrackedParentOutputBridge.initialFrame,TrackedParentOutputBridge.beforeFrame,Nat.sub_zero,
      TrackedParentOutputBridge.initialHeads,hh]
    by_cases hb : i=TrackedParentOutputBridge.bufferTape M
    · subst i
      simp only [if_true]
      exact hbuf.2.symm
    · simp only [if_neg hb]
      by_cases ht : i=TrackedParentOutputBridge.targetTape M
      · subst i
        simp only [if_true]
        exact (resume_internal_output_parent_work_head M n request resume base rho sigma offset extent c label w M.outTape).symm
      · simp only [if_neg ht]
        exact congrFun hh i

private theorem resume_internal_pop_output_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    relabel M n request resume (.output label .before)
      (liftPop M n request resume (resume_internal_popped M n request resume base rho sigma offset extent c label w))=
    liftOutput M n request resume label (resume_internal_outputStart M n request resume base rho sigma offset extent c label w) := by
  have h := resume_internal_output_initial_ready M n request resume base rho sigma offset extent c label w
  apply resume_internal_flatrecursiveresumeoutputframes_cfg_ext
  · rfl
  · funext i
    simp only [relabel,liftPop,liftOutput,resume_internal_outputStart,FixedTapeExtension.embed]
    rw [h.1]
    simp only [resume_internal_outputParent,resume_internal_outputPadBase]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
    · simp only [dif_neg hi]
  · funext i
    simp only [relabel,liftPop,liftOutput,resume_internal_outputStart,FixedTapeExtension.embed]
    rw [h.2]
    simp only [resume_internal_outputParent,resume_internal_outputPadBase]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
    · simp only [dif_neg hi]

end IntMul.FlatRecursiveResume




namespace IntMul.FlatRecursiveResume

open IntMul.FlatRecursiveScheduler
open IntMul.FlatRecursiveCall
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem resume_internal_flatrecursiveresumefinalframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem resume_internal_output_parent_prefix (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) (j : Fin M.k) (p : ℕ) (hp : p < offset j) :
    (resume_internal_outputParent M n request resume base rho sigma offset extent c label w).cells (workTape M j) p=
      base.cells (resume_internal_physicalWork M j) p := by
  rw [resume_internal_output_parent_cells]
  simp only [TrackedParentRestore.finalFrame,TrackedBankedSimulation.embed,workTape]
  rw [dif_pos (by omega)]
  have hi : innerTape M ⟨j.val+2,by have := j.isLt; omega⟩ (by change 2≤ j.val+2; omega)=j := by
    apply Fin.ext; simp [innerTape]
  rw [hi,if_pos hp]
  change (childInspection M n request resume base rho sigma offset extent c label w).cells (resume_internal_physicalWork M j) p=_
  rw [resume_internal_inspection_work M n request resume base rho sigma offset extent c label w tail j]
  simp only [TrackedBankedSimulation.embed,workTape]
  rw [dif_pos (by omega)]
  simp only [hi,if_pos hp,parentBase,if_neg (by omega : j.val+2≠1)]
  rfl

private theorem resume_internal_output_final_work (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) (j : Fin M.k) :
    (resume_internal_outputFinal M n request resume base rho sigma offset extent c label w).cells (resume_internal_physicalWork M j)=
      (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma w) offset
        (parentAfterChildExtent M extent w) (parentAfterChild M n resume label c w)).cells (workTape M j) := by
  change (FixedTapeExtension.embed (TrackedParentOutputBridge.machine M) _
    (TrackedParentOutputBridge.finalFrame M _ sigma offset extent (resume_internal_parkedParent M c) w)).cells
    (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M j))=_
  rw [resume_internal_extension_old_cells]
  funext p
  by_cases hj : j=M.outTape
  · subst j
    simp only [TrackedParentOutputBridge.finalFrame,
      if_pos (show workTape M M.outTape=TrackedParentOutputBridge.targetTape M by rfl)]
    simp only [TrackedBankPreparation.bankTape]
    by_cases hp : p < offset M.outTape
    · rw [if_pos hp,resume_internal_output_parent_prefix M n request resume base rho sigma offset extent c label w tail M.outTape p hp]
      simp only [TrackedBankedSimulation.embed,workTape]
      rw [dif_pos (by omega)]
      have hi : innerTape M ⟨M.outTape.val+2,by have := M.outTape.isLt; omega⟩ (by change 2≤ M.outTape.val+2; omega)=M.outTape := by apply Fin.ext; simp [innerTape]
      simp only [hi,if_pos hp,parentBase,if_neg (by omega : M.outTape.val+2≠1)]
      rfl
    · simp only [if_neg hp,List.length_map,TrackedBankedSimulation.embed,workTape]
      rw [dif_pos (by omega)]
      have hi : innerTape M ⟨M.outTape.val+2,by have := M.outTape.isLt; omega⟩ (by change 2≤ M.outTape.val+2; omega)=M.outTape := by apply Fin.ext; simp [innerTape]
      simp only [hi,if_neg hp,parentAfterChild,parentAfterChildExtent,if_true]
  · have ht : workTape M j≠TrackedParentOutputBridge.targetTape M := by
      intro h; exact hj (resume_internal_work_injective M h)
    have h := (resume_internal_output_initial_ready M n request resume base rho sigma offset extent c label w).1
    simp only [TrackedParentOutputBridge.finalFrame,if_neg ht]
    change (TrackedParentOutputBridge.initialFrame M
      (resume_internal_outputParent M n request resume base rho sigma offset extent c label w)
      sigma offset extent (resume_internal_parkedParent M c) w).cells (workTape M j) p=_
    rw [h]
    by_cases hp : p < offset j
    · rw [resume_internal_output_parent_prefix M n request resume base rho sigma offset extent c label w tail j p hp]
      simp only [TrackedBankedSimulation.embed,workTape]
      rw [dif_pos (by omega)]
      have hi : innerTape M ⟨j.val+2,by have := j.isLt; omega⟩ (by change 2≤ j.val+2; omega)=j := by apply Fin.ext; simp [innerTape]
      simp only [hi,if_pos hp,parentBase,if_neg (by omega : j.val+2≠1)]
      rfl
    · have ho : offset j≤ p := by omega
      have hc := resume_internal_output_parent_work M n request resume base rho sigma offset extent c label w j (p-offset j)
      rw [show offset j+(p-offset j)=p by omega] at hc
      rw [hc]
      simp only [TrackedBankedSimulation.embed,workTape]
      rw [dif_pos (by omega)]
      have hi : innerTape M ⟨j.val+2,by have := j.isLt; omega⟩ (by change 2≤ j.val+2; omega)=j := by apply Fin.ext; simp [innerTape]
      simp only [hi,if_neg hp,parentAfterChild,parentAfterChildExtent,if_neg hj,resume_internal_parkedParent]


private theorem resume_internal_output_final_work_head (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) (j : Fin M.k) :
    (resume_internal_outputFinal M n request resume base rho sigma offset extent c label w).head (resume_internal_physicalWork M j)=offset j := by
  change (FixedTapeExtension.embed (TrackedParentOutputBridge.machine M) _
    (TrackedParentOutputBridge.finalFrame M _ sigma offset extent (resume_internal_parkedParent M c) w)).head
    (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M j))=_
  rw [resume_internal_extension_old_heads]
  by_cases hj : j=M.outTape
  · subst j
    simp only [TrackedParentOutputBridge.finalFrame,
      if_neg (show workTape M M.outTape≠TrackedParentOutputBridge.bufferTape M from resume_internal_work_ne_buffer M M.outTape),
      if_pos (show workTape M M.outTape=TrackedParentOutputBridge.targetTape M by rfl)]
  · have ht : workTape M j≠TrackedParentOutputBridge.targetTape M := by intro h; exact hj (resume_internal_work_injective M h)
    simp only [TrackedParentOutputBridge.finalFrame,if_neg ht]
    change (TrackedParentOutputBridge.initialFrame M
      (resume_internal_outputParent M n request resume base rho sigma offset extent c label w)
      sigma offset extent (resume_internal_parkedParent M c) w).head (workTape M j)=_
    rw [(resume_internal_output_initial_ready M n request resume base rho sigma offset extent c label w).2,
      resume_internal_output_parent_work_head]

private theorem resume_internal_output_final_buffer (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (resume_internal_outputFinal M n request resume base rho sigma offset extent c label w).cells (bufferTape M)=
      TrackedOutputReturn.bufferTape M (base.cells (bufferTape M)) sigma w ∧
    (resume_internal_outputFinal M n request resume base rho sigma offset extent c label w).head (bufferTape M)=sigma+w.length+1 := by
  have ht : TrackedParentOutputBridge.bufferTape M≠TrackedParentOutputBridge.targetTape M := by
    intro h; have := congrArg Fin.val h; simp [TrackedParentOutputBridge.bufferTape,TrackedParentOutputBridge.targetTape,workTape] at this
  constructor
  · change (FixedTapeExtension.embed (TrackedParentOutputBridge.machine M) _
      (TrackedParentOutputBridge.finalFrame M _ sigma offset extent (resume_internal_parkedParent M c) w)).cells
      (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (TrackedParentOutputBridge.bufferTape M))=_
    rw [resume_internal_extension_old_cells]
    simp only [TrackedParentOutputBridge.finalFrame,if_neg ht]
    change (TrackedParentOutputBridge.initialFrame M
      (resume_internal_outputParent M n request resume base rho sigma offset extent c label w)
      sigma offset extent (resume_internal_parkedParent M c) w).cells (TrackedParentOutputBridge.bufferTape M)=_
    rw [(resume_internal_output_initial_ready M n request resume base rho sigma offset extent c label w).1]
    exact (resume_internal_output_parent_buffer M n request resume base rho sigma offset extent c label w).1
  · change (FixedTapeExtension.embed (TrackedParentOutputBridge.machine M) _
      (TrackedParentOutputBridge.finalFrame M _ sigma offset extent (resume_internal_parkedParent M c) w)).head
      (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (TrackedParentOutputBridge.bufferTape M))=_
    rw [resume_internal_extension_old_heads]
    simp only [TrackedParentOutputBridge.finalFrame,if_true]

private theorem resume_internal_output_final_root (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (resume_internal_outputFinal M n request resume base rho sigma offset extent c label w).cells ⟨0,by change 0 < M.k+3; omega⟩=
      base.cells ⟨0,by change 0 < M.k+3; omega⟩ ∧
    (resume_internal_outputFinal M n request resume base rho sigma offset extent c label w).head ⟨0,by change 0 < M.k+3; omega⟩=
      base.head ⟨0,by change 0 < M.k+3; omega⟩ := by
  have ht : (⟨0,by change 0 < M.k+2; omega⟩ : Fin (M.k+2))≠TrackedParentOutputBridge.targetTape M := by
    intro h; have := congrArg Fin.val h; simp [TrackedParentOutputBridge.targetTape,workTape] at this
  have hb : (⟨0,by change 0 < M.k+2; omega⟩ : Fin (M.k+2))≠TrackedParentOutputBridge.bufferTape M := by
    intro h; have := congrArg Fin.val h; simp [TrackedParentOutputBridge.bufferTape] at this
  constructor
  · change (FixedTapeExtension.embed (TrackedParentOutputBridge.machine M) _
      (TrackedParentOutputBridge.finalFrame M _ sigma offset extent (resume_internal_parkedParent M c) w)).cells
      (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) ⟨0,by change 0 < M.k+2; omega⟩)=_
    rw [resume_internal_extension_old_cells]
    simp only [TrackedParentOutputBridge.finalFrame,if_neg ht]
    change (TrackedParentOutputBridge.initialFrame M
      (resume_internal_outputParent M n request resume base rho sigma offset extent c label w)
      sigma offset extent (resume_internal_parkedParent M c) w).cells ⟨0,by change 0 < M.k+2; omega⟩=_
    rw [(resume_internal_output_initial_ready M n request resume base rho sigma offset extent c label w).1,resume_internal_output_parent_cells]
    simp only [TrackedParentRestore.finalFrame,TrackedBankedSimulation.embed]
    simp only [dif_neg (by omega : ¬2 ≤ (0:ℕ))]
    exact (resume_internal_inspection_root M n request resume base rho sigma offset extent c label w).1
  · change (FixedTapeExtension.embed (TrackedParentOutputBridge.machine M) _
      (TrackedParentOutputBridge.finalFrame M _ sigma offset extent (resume_internal_parkedParent M c) w)).head
      (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) ⟨0,by change 0 < M.k+2; omega⟩)=_
    rw [resume_internal_extension_old_heads]
    simp only [TrackedParentOutputBridge.finalFrame,if_neg hb,if_neg ht]
    change (TrackedParentOutputBridge.initialFrame M
      (resume_internal_outputParent M n request resume base rho sigma offset extent c label w)
      sigma offset extent (resume_internal_parkedParent M c) w).head ⟨0,by change 0 < M.k+2; omega⟩=_
    rw [(resume_internal_output_initial_ready M n request resume base rho sigma offset extent c label w).2,resume_internal_output_parent_heads]
    simp only [TrackedParentRestore.finalFrame,dif_neg (by omega : ¬2 ≤ (0:ℕ))]
    exact (resume_internal_inspection_root M n request resume base rho sigma offset extent c label w).2

private theorem resume_internal_output_final_stack (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (resume_internal_outputFinal M n request resume base rho sigma offset extent c label w).cells (stackTape M)=
      FiniteContinuationStack.freshTape M (base.cells (stackTape M)) rho ∧
    (resume_internal_outputFinal M n request resume base rho sigma offset extent c label w).head (stackTape M)=rho := by
  have he : stackTape M=FixedTapeExtension.extraTape (TrackedParentOutputBridge.machine M) := by apply Fin.ext; rfl
  constructor
  · simp only [resume_internal_outputFinal,he,resume_internal_extension_extra_cells,resume_internal_outputPadBase]
    rw [he.symm]
    exact (resume_internal_popped_stack M n request resume base rho sigma offset extent c label w).1
  · simp only [resume_internal_outputFinal,he,resume_internal_extension_extra_heads,resume_internal_outputPadBase]
    rw [he.symm]
    exact (resume_internal_popped_stack M n request resume base rho sigma offset extent c label w).2

end IntMul.FlatRecursiveResume



namespace IntMul.FlatRecursiveResume

open IntMul.FlatRecursiveScheduler
open IntMul.FlatRecursiveCall
open IntMul.BankedSimulation (workTape innerTape)

private theorem resume_internal_flatrecursiveresumeconclusion_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem resume_internal_output_resumed_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    relabel M n request resume (.body (resume label))
      (liftOutput M n request resume label (resume_internal_outputFinal M n request resume base rho sigma offset extent c label w))=
    resumedFrame M n request resume base rho sigma offset extent c label w := by
  classical
  apply resume_internal_flatrecursiveresumeconclusion_cfg_ext
  · rfl
  · funext i
    have hik : i.val < M.k+3 := i.isLt
    by_cases hi : i.val < M.k+2
    · by_cases hw : 2 ≤ i.val
      · let j := innerTape M ⟨i.val,hi⟩ hw
        have he : resume_internal_physicalWork M j=i := by
          apply Fin.ext
          simp only [resume_internal_physicalWork,FixedTapeExtension.oldTape,workTape,innerTape,j]
          omega
        rw [←he]
        change (resume_internal_outputFinal M n request resume base rho sigma offset extent c label w).cells (resume_internal_physicalWork M j)=
          (FixedTapeExtension.embed (TrackedBankedSimulation.machine M) _
            (TrackedBankedSimulation.embed M _ _ _ _)).cells
            (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) (workTape M j))
        rw [resume_internal_extension_old_cells]
        exact resume_internal_output_final_work M n request resume base rho sigma offset extent c label w tail j
      · by_cases hb : i.val=1
        · have he : i=bufferTape M := Fin.ext hb
          subst i
          simp only [relabel,liftOutput]
          rw [(resume_internal_output_final_buffer M n request resume base rho sigma offset extent c label w).1]
          simp [resumedFrame,bodyFrame,liftBody,FixedTapeExtension.embed,
            TrackedBankedSimulation.embed,parentBase,bufferTape,FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
        · have hz : i.val=0 := by omega
          have he : i=⟨0,by change 0 < M.k+3; omega⟩ := Fin.ext hz
          rw [he]
          simp only [relabel,liftOutput]
          rw [(resume_internal_output_final_root M n request resume base rho sigma offset extent c label w).1]
          simp [resumedFrame,bodyFrame,liftBody,FixedTapeExtension.embed,
            TrackedBankedSimulation.embed,parentBase,FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
    · have he : i=stackTape M := by apply Fin.ext; simp only [stackTape,FiniteContinuationStack.stackTape]; omega
      subst i
      simp only [relabel,liftOutput]
      rw [(resume_internal_output_final_stack M n request resume base rho sigma offset extent c label w).1]
      simp only [resumedFrame,bodyFrame,liftBody]
      rw [show stackTape M=FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M) by rfl,
        resume_internal_extension_extra_cells]
      rw [show FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M)=stackTape M by rfl]
      simp only [stackBase,if_true]
  · funext i
    have hik : i.val < M.k+3 := i.isLt
    by_cases hi : i.val < M.k+2
    · by_cases hw : 2 ≤ i.val
      · let j := innerTape M ⟨i.val,hi⟩ hw
        have he : resume_internal_physicalWork M j=i := by
          apply Fin.ext
          simp only [resume_internal_physicalWork,FixedTapeExtension.oldTape,workTape,innerTape,j]
          omega
        rw [←he]
        change (resume_internal_outputFinal M n request resume base rho sigma offset extent c label w).head (resume_internal_physicalWork M j)=
          (FixedTapeExtension.embed (TrackedBankedSimulation.machine M) _
            (TrackedBankedSimulation.embed M _ _ _ _)).head
            (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) (workTape M j))
        rw [resume_internal_extension_old_heads,resume_internal_embed_work_head,resume_internal_output_final_work_head]
        simp [parentAfterChild]
      · by_cases hb : i.val=1
        · have he : i=bufferTape M := Fin.ext hb
          subst i
          simp only [relabel,liftOutput]
          rw [(resume_internal_output_final_buffer M n request resume base rho sigma offset extent c label w).2]
          simp [resumedFrame,bodyFrame,liftBody,FixedTapeExtension.embed,
            TrackedBankedSimulation.embed,parentBase,bufferTape,FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
        · have hz : i.val=0 := by omega
          have he : i=⟨0,by change 0 < M.k+3; omega⟩ := Fin.ext hz
          rw [he]
          simp only [relabel,liftOutput]
          rw [(resume_internal_output_final_root M n request resume base rho sigma offset extent c label w).2]
          simp [resumedFrame,bodyFrame,liftBody,FixedTapeExtension.embed,
            TrackedBankedSimulation.embed,parentBase,FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
    · have he : i=stackTape M := by apply Fin.ext; simp only [stackTape,FiniteContinuationStack.stackTape]; omega
      subst i
      simp only [relabel,liftOutput]
      rw [(resume_internal_output_final_stack M n request resume base rho sigma offset extent c label w).2]
      simp only [resumedFrame,bodyFrame,liftBody]
      rw [show stackTape M=FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M) by rfl,
        resume_internal_extension_extra_heads]
      rw [show FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M)=stackTape M by rfl]
      simp only [stackBase,if_true]

end IntMul.FlatRecursiveResume



namespace IntMul.FlatRecursiveResume

open IntMul.FlatRecursiveScheduler
open IntMul.FlatRecursiveCall
open IntMul.TrackedBankCleanup (span)

/-- A physical child return recovers its finite continuation and resumes the
SAME parent body on the SAME fixed tapes. Every head move is charged. -/
private theorem resume_parent_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∃ t, t ≤ span M (fun j => extent j+1)+n+w.length+2*max w.length (extent M.outTape)+12 ∧
      (machine M n request resume).step^[t]
        (childInspection M n request resume base rho sigma offset extent c label w)=
        resumedFrame M n request resume base rho sigma offset extent c label w := by
  have hstack := resume_internal_inspection_stack M n request resume base rho sigma offset extent c label w
  have hins : (machine M n request resume).step
      (childInspection M n request resume base rho sigma offset extent c label w)=
      liftRestore M n request resume (resume_internal_restoreStart M n request resume base rho sigma offset extent c label w) := by
    rw [resume_internal_inspect_parent_dispatch M n request resume _ rfl
      (resume_internal_inspection_nonroot M n request resume base rho sigma offset extent c label w),hstack.2]
    exact resume_internal_inspection_restore_ready M n request resume base rho sigma offset extent c label w tail
  let R := span M (fun j => extent j+1)+1
  have hrr : (restoreMachine M).step^[R]
      (resume_internal_restoreStart M n request resume base rho sigma offset extent c label w)=
      resume_internal_restoreFinal M n request resume base rho sigma offset extent c label w := by
    have h := (FixedTapeExtension.simulate_run (TrackedParentRestore.machine M)
      (resume_internal_restorePadBase M n request resume base rho sigma offset extent c label w)
      (TrackedParentRestore.initialFrame M
        (resume_internal_restoreParent M n request resume base rho sigma offset extent c label w)
        offset extent c (fun j => extent j+1)) R).1
    rw [(TrackedParentRestore.restore_correct M
      (resume_internal_restoreParent M n request resume base rho sigma offset extent c label w)
      offset extent c unique (fun j => extent j+1)).1] at h
    exact h
  have hrh : ((restoreMachine M).step^[R]
      (resume_internal_restoreStart M n request resume base rho sigma offset extent c label w)).state=(restoreMachine M).qHalt := by
    rw [hrr]; rfl
  obtain ⟨r,hrc,hrrun⟩ := resume_internal_restore_to_halt M n request resume
    (resume_internal_restoreStart M n request resume base rho sigma offset extent c label w) R hrh
  rw [hrr] at hrrun
  have hstage1 : (machine M n request resume).step^[r+1]
      (childInspection M n request resume base rho sigma offset extent c label w)=
      liftRestore M n request resume (resume_internal_restoreFinal M n request resume base rho sigma offset extent c label w) := by
    rw [Function.iterate_succ_apply,hins,hrrun]
  have hpop : (machine M n request resume).step^[n+3]
      (liftRestore M n request resume (resume_internal_restoreFinal M n request resume base rho sigma offset extent c label w))=
      liftPop M n request resume (resume_internal_popped M n request resume base rho sigma offset extent c label w) := by
    rw [show n+3=(n+2)+1 by omega,Function.iterate_succ_apply,resume_internal_restore_dispatch M n request resume _ rfl,
      resume_internal_restore_pop_ready M n request resume base rho sigma offset extent c label w]
    exact FlatRecursiveStack.resume_internal_pop_correct M n request resume _ rho label
  have hstage2 : (machine M n request resume).step^[n+4]
      (liftRestore M n request resume (resume_internal_restoreFinal M n request resume base rho sigma offset extent c label w))=
      liftOutput M n request resume label (resume_internal_outputStart M n request resume base rho sigma offset extent c label w) := by
    rw [show n+4=(n+3)+1 by omega,Function.iterate_succ_apply',hpop,
      resume_internal_pop_dispatch M n request resume _ label rfl]
    exact resume_internal_pop_output_ready M n request resume base rho sigma offset extent c label w
  let O := w.length+2*max w.length (extent M.outTape)+5
  have hor : (outputMachine M).step^[O]
      (resume_internal_outputStart M n request resume base rho sigma offset extent c label w)=
      resume_internal_outputFinal M n request resume base rho sigma offset extent c label w := by
    have h := (FixedTapeExtension.simulate_run (TrackedParentOutputBridge.machine M)
      (resume_internal_outputPadBase M n request resume base rho sigma offset extent c label w)
      (TrackedParentOutputBridge.initialFrame M
        (resume_internal_outputParent M n request resume base rho sigma offset extent c label w)
        sigma offset extent (resume_internal_parkedParent M c) w) O).1
    rw [(TrackedParentOutputBridge.output_correct M
      (resume_internal_outputParent M n request resume base rho sigma offset extent c label w)
      sigma offset extent (resume_internal_parkedParent M c) w ((unique M.outTape 0).2 rfl)
      (tail M.outTape)).1] at h
    exact h
  have hoh : ((outputMachine M).step^[O]
      (resume_internal_outputStart M n request resume base rho sigma offset extent c label w)).state=(outputMachine M).qHalt := by
    rw [hor]; rfl
  obtain ⟨q,hqc,hqrun⟩ := resume_internal_output_to_halt M n request resume label
    (resume_internal_outputStart M n request resume base rho sigma offset extent c label w) O hoh
  rw [hor] at hqrun
  have hstage3 : (machine M n request resume).step^[q+1]
      (liftOutput M n request resume label (resume_internal_outputStart M n request resume base rho sigma offset extent c label w))=
      resumedFrame M n request resume base rho sigma offset extent c label w := by
    rw [Function.iterate_succ_apply',hqrun,resume_internal_output_dispatch M n request resume label _ rfl]
    exact resume_internal_output_resumed_ready M n request resume base rho sigma offset extent c label w tail
  refine ⟨(q+1)+((n+4)+(r+1)),by dsimp only [R,O] at *; omega,?_⟩
  rw [Function.iterate_add_apply (machine M n request resume).step (q+1) ((n+4)+(r+1)),
    Function.iterate_add_apply (machine M n request resume).step (n+4) (r+1),
    hstage1,hstage2,hstage3]

end IntMul.FlatRecursiveResume


open IntMul IntMul.FlatRecursiveResume IntMul.FlatRecursiveScheduler IntMul.FlatRecursiveCall IntMul.TrackedBankCleanup

theorem solution (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∃ t, t ≤ span M (fun j => extent j+1)+n+w.length+2*max w.length (extent M.outTape)+12 ∧
      (machine M n request resume).step^[t]
        (childInspection M n request resume base rho sigma offset extent c label w)=
        resumedFrame M n request resume base rho sigma offset extent c label w :=
  IntMul.FlatRecursiveResume.resume_parent_correct M n request resume base rho sigma offset extent c label w unique tail

#print axioms solution
