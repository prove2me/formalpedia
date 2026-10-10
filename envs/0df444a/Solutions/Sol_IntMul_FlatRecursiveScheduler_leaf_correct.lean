-- Prove2me | solution 1 for IntMul.FlatRecursiveScheduler.leaf_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T02:38:48.185974+00:00
-- url     : https://prove2.me/submissions/bc91aeb9-f6c5-42a9-8a36-f66f253a04f3

import Definitions.Def_IntMul_FlatRecursiveReturn
import Theorems.Thm_IntMul_FlatRecursiveScheduler_bootstrap_correct
import Theorems.Thm_IntMul_FlatRecursiveReturn_return_cleanup_correct
import Theorems.Thm_IntMul_TrackedBankedSimulation_simulate_run
import Theorems.Thm_IntMul_TrackedOutputShift_shift_correct
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Mathlib.Data.List.GetD
import Mathlib.Tactic


namespace IntMul.FlatRecursiveScheduler

private theorem leaf_internal_flatrecursiveschedulerpadding_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem leaf_internal_extension_old_cells (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) (j : Fin N.k) :
    (FixedTapeExtension.embed N base c).cells (FixedTapeExtension.oldTape N j)=c.cells j := by
  simp only [FixedTapeExtension.embed,FixedTapeExtension.oldTape,dif_pos j.isLt]
  have h : FixedTapeExtension.innerTape N ⟨j.val,by have := j.isLt; omega⟩ j.isLt=j := by apply Fin.ext; rfl
  rw [h]

private theorem leaf_internal_extension_old_heads (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) (j : Fin N.k) :
    (FixedTapeExtension.embed N base c).head (FixedTapeExtension.oldTape N j)=c.head j := by
  simp only [FixedTapeExtension.embed,FixedTapeExtension.oldTape,dif_pos j.isLt]
  have h : FixedTapeExtension.innerTape N ⟨j.val,by have := j.isLt; omega⟩ j.isLt=j := by apply Fin.ext; rfl
  rw [h]

private theorem leaf_internal_extension_extra_cells (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) :
    (FixedTapeExtension.embed N base c).cells (FixedTapeExtension.extraTape N)=base.cells (FixedTapeExtension.extraTape N) := by
  simp [FixedTapeExtension.embed,FixedTapeExtension.extraTape]

private theorem leaf_internal_extension_extra_heads (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) :
    (FixedTapeExtension.embed N base c).head (FixedTapeExtension.extraTape N)=base.head (FixedTapeExtension.extraTape N) := by
  simp [FixedTapeExtension.embed,FixedTapeExtension.extraTape]

private theorem leaf_internal_extension_cells_ready (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg)
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

private theorem leaf_internal_extension_heads_ready (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg)
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

private theorem leaf_internal_padded_init (N : MultitapeTM) (x y : List Bool) :
    (FixedTapeExtension.machine N).initCfg x y =
      FixedTapeExtension.embed N ((FixedTapeExtension.machine N).initCfg x y) (N.initCfg x y) := by
  apply leaf_internal_flatrecursiveschedulerpadding_cfg_ext
  · rfl
  · apply (leaf_internal_extension_cells_ready N _ _ ?_).symm
    intro j
    have hzero : FixedTapeExtension.oldTape N j=(FixedTapeExtension.machine N).inTape ↔ j=N.inTape := by
      constructor
      · intro h; apply Fin.ext
        have hv := congrArg (fun i : Fin (N.k+1) => i.val) h
        exact hv
      · intro h; subst j; rfl
    simp only [MultitapeTM.initCfg,hzero]
    split <;> rfl
  · apply (leaf_internal_extension_heads_ready N _ _ ?_).symm
    intro j
    rfl

end IntMul.FlatRecursiveScheduler



namespace IntMul.FlatRecursiveScheduler

private theorem leaf_internal_flatrecursiveschedulerprograms_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem leaf_internal_flatrecursiveschedulerprograms_fixed_iterate (N : MultitapeTM) (c : N.Cfg) (fixed : N.step c=c) (T : ℕ) :
    N.step^[T] c=c := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,fixed]

private theorem leaf_internal_flatrecursiveschedulerprograms_halted_step (N : MultitapeTM) (c : N.Cfg) (halt : c.state=N.qHalt) : N.step c=c := by
  apply leaf_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp [MultitapeTM.step,halt,N.halt_fixed]
  · funext i
    simp only [MultitapeTM.step,halt,N.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,N.halt_fixed]

/-- First entry to any family of quiescent service exits preserves the exact
complete supplied terminal configuration, including all tape heads. -/
private theorem leaf_internal_flatrecursiveschedulerprograms_first_exit (N : MultitapeTM) (P : N.K → Prop)
    (fixed : ∀ d : N.Cfg, P d.state → N.step d=d) (c : N.Cfg) (T : ℕ)
    (exit : P (N.step^[T] c).state) :
    ∃ t, t≤ T ∧ N.step^[t] c=N.step^[T] c ∧ ∀ s, s< t → ¬P (N.step^[s] c).state := by
  classical
  have hex : ∃ t, P (N.step^[t] c).state := ⟨T,exit⟩
  let t := Nat.find hex
  have ht : t≤ T := Nat.find_min' hex exit
  have hp : P (N.step^[t] c).state := Nat.find_spec hex
  refine ⟨t,ht,?_,?_⟩
  · rw [show T=(T-t)+t by omega,Function.iterate_add_apply,leaf_internal_flatrecursiveschedulerprograms_fixed_iterate N _ (fixed _ hp)]
  · intro s hs
    exact Nat.find_min hex hs

private theorem leaf_internal_boot_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (live : c.state≠(bootMachine M).qHalt) :
    (machine M n request resume).step (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step c) := by
  have ht : transition M n request resume (.boot c.state) (fun i => c.cells i (c.head i))=
      (let r := (bootMachine M).δ c.state (fun i => c.cells i (c.head i)); (.boot r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply leaf_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftBoot,ht]
  · simp only [MultitapeTM.step,liftBoot,ht]
  · simp only [MultitapeTM.step,liftBoot,ht]

private theorem leaf_internal_boot_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((bootMachine M).step^[s] c).state≠(bootMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      leaf_internal_boot_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem leaf_internal_boot_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (T : ℕ)
    (exit : ((bootMachine M).step^[T] c).state=(bootMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := leaf_internal_flatrecursiveschedulerprograms_first_exit (bootMachine M)
    (fun q => q=(bootMachine M).qHalt) (by intro d hd; exact leaf_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [leaf_internal_boot_iterate M n request resume c s hlive,he]

private theorem leaf_internal_preparation_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (live : c.state≠(preparationMachine M).qHalt) :
    (machine M n request resume).step (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step c) := by
  have ht : transition M n request resume (.preparation c.state) (fun i => c.cells i (c.head i))=
      (let r := (preparationMachine M).δ c.state (fun i => c.cells i (c.head i)); (.preparation r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply leaf_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftPreparation,ht]
  · simp only [MultitapeTM.step,liftPreparation,ht]
  · simp only [MultitapeTM.step,liftPreparation,ht]

private theorem leaf_internal_preparation_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((preparationMachine M).step^[s] c).state≠(preparationMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      leaf_internal_preparation_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem leaf_internal_preparation_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (T : ℕ)
    (exit : ((preparationMachine M).step^[T] c).state=(preparationMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := leaf_internal_flatrecursiveschedulerprograms_first_exit (preparationMachine M)
    (fun q => q=(preparationMachine M).qHalt) (by intro d hd; exact leaf_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [leaf_internal_preparation_iterate M n request resume c s hlive,he]

private theorem leaf_internal_body_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (live : c.state≠(bodyMachine M).qHalt)
    (no_request : request c.state=none) :
    (machine M n request resume).step (liftBody M n request resume c)=
      liftBody M n request resume ((bodyMachine M).step c) := by
  have ht : transition M n request resume (.body c.state) (fun i => c.cells i (c.head i))=
      (let r := (bodyMachine M).δ c.state (fun i => c.cells i (c.head i)); (.body r.1,r.2)) := by
    simp only [transition,if_neg live,no_request]
  apply leaf_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftBody,ht]
  · simp only [MultitapeTM.step,liftBody,ht]
  · simp only [MultitapeTM.step,liftBody,ht]

private theorem leaf_internal_body_iterate (M : MultitapeTM) (n : ℕ)
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
      leaf_internal_body_step M n request resume _ (live T (by omega)) (no_request T (by omega)),Function.iterate_succ_apply']

private theorem leaf_internal_body_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (T : ℕ)
    (exit : ((bodyMachine M).step^[T] c).state=(bodyMachine M).qHalt)
    (no_request : ∀ s, s < T → request (((bodyMachine M).step^[s] c).state)=none) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftBody M n request resume c)=
      liftBody M n request resume ((bodyMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := leaf_internal_flatrecursiveschedulerprograms_first_exit (bodyMachine M)
    (fun q => q=(bodyMachine M).qHalt) (by intro d hd; exact leaf_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [leaf_internal_body_iterate M n request resume c s hlive (by intro r hr; exact no_request r (by omega)),he]

private theorem leaf_internal_input_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (live : c.state≠(inputMachine M).qHalt) :
    (machine M n request resume).step (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step c) := by
  have ht : transition M n request resume (.input label c.state) (fun i => c.cells i (c.head i))=
      (let r := (inputMachine M).δ c.state (fun i => c.cells i (c.head i)); (.input label r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply leaf_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftInput,ht]
  · simp only [MultitapeTM.step,liftInput,ht]
  · simp only [MultitapeTM.step,liftInput,ht]

private theorem leaf_internal_input_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((inputMachine M).step^[s] c).state≠(inputMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      leaf_internal_input_step M n request resume label _ (live T (by omega)),Function.iterate_succ_apply']

private theorem leaf_internal_input_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (T : ℕ)
    (exit : ((inputMachine M).step^[T] c).state=(inputMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := leaf_internal_flatrecursiveschedulerprograms_first_exit (inputMachine M)
    (fun q => q=(inputMachine M).qHalt) (by intro d hd; exact leaf_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [leaf_internal_input_iterate M n request resume label c s hlive,he]

private theorem leaf_internal_reservation_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (live : c.state≠(reservationMachine M).qHalt) :
    (machine M n request resume).step (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step c) := by
  have ht : transition M n request resume (.reservation c.state) (fun i => c.cells i (c.head i))=
      (let r := (reservationMachine M).δ c.state (fun i => c.cells i (c.head i)); (.reservation r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply leaf_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftReservation,ht]
  · simp only [MultitapeTM.step,liftReservation,ht]
  · simp only [MultitapeTM.step,liftReservation,ht]

private theorem leaf_internal_reservation_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((reservationMachine M).step^[s] c).state≠(reservationMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      leaf_internal_reservation_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem leaf_internal_reservation_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (T : ℕ)
    (exit : ((reservationMachine M).step^[T] c).state=(reservationMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := leaf_internal_flatrecursiveschedulerprograms_first_exit (reservationMachine M)
    (fun q => q=(reservationMachine M).qHalt) (by intro d hd; exact leaf_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [leaf_internal_reservation_iterate M n request resume c s hlive,he]

private theorem leaf_internal_return_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (live : c.state≠(returnMachine M).qHalt) :
    (machine M n request resume).step (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step c) := by
  have ht : transition M n request resume (.returning c.state) (fun i => c.cells i (c.head i))=
      (let r := (returnMachine M).δ c.state (fun i => c.cells i (c.head i)); (.returning r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply leaf_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftReturn,ht]
  · simp only [MultitapeTM.step,liftReturn,ht]
  · simp only [MultitapeTM.step,liftReturn,ht]

private theorem leaf_internal_return_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((returnMachine M).step^[s] c).state≠(returnMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      leaf_internal_return_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem leaf_internal_return_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (T : ℕ)
    (exit : ((returnMachine M).step^[T] c).state=(returnMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := leaf_internal_flatrecursiveschedulerprograms_first_exit (returnMachine M)
    (fun q => q=(returnMachine M).qHalt) (by intro d hd; exact leaf_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [leaf_internal_return_iterate M n request resume c s hlive,he]

private theorem leaf_internal_cleanup_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (live : c.state≠(cleanupMachine M).qHalt) :
    (machine M n request resume).step (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step c) := by
  have ht : transition M n request resume (.cleanup c.state) (fun i => c.cells i (c.head i))=
      (let r := (cleanupMachine M).δ c.state (fun i => c.cells i (c.head i)); (.cleanup r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply leaf_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftCleanup,ht]
  · simp only [MultitapeTM.step,liftCleanup,ht]
  · simp only [MultitapeTM.step,liftCleanup,ht]

private theorem leaf_internal_cleanup_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((cleanupMachine M).step^[s] c).state≠(cleanupMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      leaf_internal_cleanup_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem leaf_internal_cleanup_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (T : ℕ)
    (exit : ((cleanupMachine M).step^[T] c).state=(cleanupMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := leaf_internal_flatrecursiveschedulerprograms_first_exit (cleanupMachine M)
    (fun q => q=(cleanupMachine M).qHalt) (by intro d hd; exact leaf_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [leaf_internal_cleanup_iterate M n request resume c s hlive,he]

private theorem leaf_internal_restore_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (restoreMachine M).Cfg) (live : c.state≠(restoreMachine M).qHalt) :
    (machine M n request resume).step (liftRestore M n request resume c)=
      liftRestore M n request resume ((restoreMachine M).step c) := by
  have ht : transition M n request resume (.restore c.state) (fun i => c.cells i (c.head i))=
      (let r := (restoreMachine M).δ c.state (fun i => c.cells i (c.head i)); (.restore r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply leaf_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftRestore,ht]
  · simp only [MultitapeTM.step,liftRestore,ht]
  · simp only [MultitapeTM.step,liftRestore,ht]

private theorem leaf_internal_restore_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (restoreMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((restoreMachine M).step^[s] c).state≠(restoreMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftRestore M n request resume c)=
      liftRestore M n request resume ((restoreMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      leaf_internal_restore_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem leaf_internal_restore_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (restoreMachine M).Cfg) (T : ℕ)
    (exit : ((restoreMachine M).step^[T] c).state=(restoreMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftRestore M n request resume c)=
      liftRestore M n request resume ((restoreMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := leaf_internal_flatrecursiveschedulerprograms_first_exit (restoreMachine M)
    (fun q => q=(restoreMachine M).qHalt) (by intro d hd; exact leaf_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [leaf_internal_restore_iterate M n request resume c s hlive,he]

private theorem leaf_internal_output_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (live : c.state≠(outputMachine M).qHalt) :
    (machine M n request resume).step (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step c) := by
  have ht : transition M n request resume (.output label c.state) (fun i => c.cells i (c.head i))=
      (let r := (outputMachine M).δ c.state (fun i => c.cells i (c.head i)); (.output label r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply leaf_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftOutput,ht]
  · simp only [MultitapeTM.step,liftOutput,ht]
  · simp only [MultitapeTM.step,liftOutput,ht]

private theorem leaf_internal_output_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((outputMachine M).step^[s] c).state≠(outputMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      leaf_internal_output_step M n request resume label _ (live T (by omega)),Function.iterate_succ_apply']

private theorem leaf_internal_output_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (T : ℕ)
    (exit : ((outputMachine M).step^[T] c).state=(outputMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := leaf_internal_flatrecursiveschedulerprograms_first_exit (outputMachine M)
    (fun q => q=(outputMachine M).qHalt) (by intro d hd; exact leaf_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [leaf_internal_output_iterate M n request resume label c s hlive,he]

private theorem leaf_internal_finish_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (live : c.state≠(finishMachine M).qHalt) :
    (machine M n request resume).step (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step c) := by
  have ht : transition M n request resume (.finish c.state) (fun i => c.cells i (c.head i))=
      (let r := (finishMachine M).δ c.state (fun i => c.cells i (c.head i)); (.finish r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply leaf_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftFinish,ht]
  · simp only [MultitapeTM.step,liftFinish,ht]
  · simp only [MultitapeTM.step,liftFinish,ht]

private theorem leaf_internal_finish_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((finishMachine M).step^[s] c).state≠(finishMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      leaf_internal_finish_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem leaf_internal_finish_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (T : ℕ)
    (exit : ((finishMachine M).step^[T] c).state=(finishMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := leaf_internal_flatrecursiveschedulerprograms_first_exit (finishMachine M)
    (fun q => q=(finishMachine M).qHalt) (by intro d hd; exact leaf_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [leaf_internal_finish_iterate M n request resume c s hlive,he]

end IntMul.FlatRecursiveScheduler



namespace IntMul.FlatRecursiveScheduler

open IntMul.TrackedBankedSimulation (extents)

private noncomputable def leaf_internal_bodyView (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) : (bodyMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankedSimulation.machine M)
    (stackBase M n request resume base rho)
    (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma v) offset extent c)

private theorem leaf_internal_body_service_run (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (c : M.Cfg) (v : List Bool) (T : ℕ)
    (marker : ∀ j, c.cells j 0=M.startSym) (near : ∀ j, c.head j ≤ extent j+1) :
    (bodyMachine M).step^[T] (leaf_internal_bodyView M n request resume base rho sigma offset extent c v)=
      leaf_internal_bodyView M n request resume base rho sigma offset (extents M c extent T) (M.step^[T] c) v := by
  have hr := (FixedTapeExtension.simulate_run (TrackedBankedSimulation.machine M)
    (stackBase M n request resume base rho)
    (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma v) offset extent c) T).1
  rw [(TrackedBankedSimulation.simulate_run M (parentBase M n request resume base sigma v)
    offset extent positive c T marker near).1] at hr
  exact hr

/-- The actual flat scheduler executes an ordinary body segment and reaches
its complete tracked terminal frame without consuming a request state. -/
private theorem leaf_internal_body_segment_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (c : M.Cfg) (v : List Bool) (T : ℕ)
    (marker : ∀ j, c.cells j 0=M.startSym) (near : ∀ j, c.head j ≤ extent j+1)
    (halt : (M.step^[T] c).state=M.qHalt)
    (no_request : ∀ s, s < T → request (M.step^[s] c).state=none) :
    ∃ t, t ≤ T ∧ (machine M n request resume).step^[t]
      (bodyFrame M n request resume base rho sigma offset extent c v)=
      bodyFrame M n request resume base rho sigma offset (extents M c extent T) (M.step^[T] c) v := by
  have hr := leaf_internal_body_service_run M n request resume base rho sigma offset extent positive c v T marker near
  have hh : ((bodyMachine M).step^[T] (leaf_internal_bodyView M n request resume base rho sigma offset extent c v)).state=
      (bodyMachine M).qHalt := by
    rw [hr]
    exact halt
  obtain ⟨t,ht,htrun⟩ := leaf_internal_body_to_halt M n request resume
    (leaf_internal_bodyView M n request resume base rho sigma offset extent c v) T hh (by
      intro s hs
      rw [leaf_internal_body_service_run M n request resume base rho sigma offset extent positive c v s marker near]
      exact no_request s hs)
  rw [hr] at htrun
  exact ⟨t,ht,htrun⟩

end IntMul.FlatRecursiveScheduler



namespace IntMul.FlatRecursiveScheduler

private theorem leaf_internal_flatrecursiveschedulerdispatch_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem leaf_internal_flatrecursiveschedulerdispatch_right_actions (M : MultitapeTM) (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M)
    (tape : Fin (M.k+3)) : moveActions M a tape .right=
      fun i => (a i,if i=tape then .right else .stay) := by
  classical
  funext i
  simp only [moveActions]
  split_ifs <;> cases a i <;> rfl

private theorem leaf_internal_flatrecursiveschedulerdispatch_left_actions (M : MultitapeTM) (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M)
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

private theorem leaf_internal_stay_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (q : State M n)
    (ht : transition M n request resume c.state (fun i => c.cells i (c.head i))=
      (q,fun i => (c.cells i (c.head i),.stay))) :
    (machine M n request resume).step c=relabel M n request resume q c := by
  apply leaf_internal_flatrecursiveschedulerdispatch_cfg_ext
  · simp only [MultitapeTM.step,ht,relabel]
  · simp only [MultitapeTM.step,ht,relabel]
    funext i
    rw [Function.update_eq_self]
  · simp only [MultitapeTM.step,ht,relabel]

private theorem leaf_internal_right_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (q : State M n) (tape : Fin (M.k+3))
    (ht : transition M n request resume c.state (fun i => c.cells i (c.head i))=
      (q,moveActions M (fun i => c.cells i (c.head i)) tape .right)) :
    (machine M n request resume).step c=headFrame M n request resume q c tape (c.head tape+1) := by
  classical
  rw [leaf_internal_flatrecursiveschedulerdispatch_right_actions] at ht
  apply leaf_internal_flatrecursiveschedulerdispatch_cfg_ext
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

private theorem leaf_internal_left_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (q : State M n) (tape : Fin (M.k+3))
    (present : c.cells tape (c.head tape)≠none)
    (ht : transition M n request resume c.state (fun i => c.cells i (c.head i))=
      (q,moveActions M (fun i => c.cells i (c.head i)) tape .left)) :
    (machine M n request resume).step c=headFrame M n request resume q c tape (c.head tape-1) := by
  classical
  rw [leaf_internal_flatrecursiveschedulerdispatch_left_actions M _ tape present] at ht
  apply leaf_internal_flatrecursiveschedulerdispatch_cfg_ext
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

private theorem leaf_internal_boot_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (exit : c.state=(bootMachine M).qHalt) :
    (machine M n request resume).step (liftBoot M n request resume c)=headFrame M n request resume (.preparation .mark) (liftBoot M n request resume c) (stackTape M) (c.head (stackTape M)+1) := by
  apply leaf_internal_right_step
  change transition M n request resume (.boot c.state) _=_
  simp only [transition,if_pos exit]

private theorem leaf_internal_preparation_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (exit : c.state=(preparationMachine M).qHalt) :
    (machine M n request resume).step (liftPreparation M n request resume c)=relabel M n request resume (.resetBuffer) (liftPreparation M n request resume c) := by
  apply leaf_internal_stay_step
  change transition M n request resume (.preparation c.state) _=_
  simp only [transition,if_pos exit]

private theorem leaf_internal_input_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (exit : c.state=(inputMachine M).qHalt) :
    (machine M n request resume).step (liftInput M n request resume label c)=relabel M n request resume (.push (.pushStart label)) (liftInput M n request resume label c) := by
  apply leaf_internal_stay_step
  change transition M n request resume (.input label c.state) _=_
  simp only [transition,if_pos exit]

private theorem leaf_internal_reservation_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (exit : c.state=(reservationMachine M).qHalt) :
    (machine M n request resume).step (liftReservation M n request resume c)=relabel M n request resume (.preparation .mark) (liftReservation M n request resume c) := by
  apply leaf_internal_stay_step
  change transition M n request resume (.reservation c.state) _=_
  simp only [transition,if_pos exit]

private theorem leaf_internal_return_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (exit : c.state=(returnMachine M).qHalt) :
    (machine M n request resume).step (liftReturn M n request resume c)=relabel M n request resume (.cleanup .rewind) (liftReturn M n request resume c) := by
  apply leaf_internal_stay_step
  change transition M n request resume (.returning c.state) _=_
  simp only [transition,if_pos exit]

private theorem leaf_internal_cleanup_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (exit : c.state=(cleanupMachine M).qHalt)
    (present : c.cells (stackTape M) (c.head (stackTape M))≠none) :
    (machine M n request resume).step (liftCleanup M n request resume c)=headFrame M n request resume (.inspectStack) (liftCleanup M n request resume c) (stackTape M) (c.head (stackTape M)-1) := by
  apply leaf_internal_left_step M n request resume _ _ _ present
  change transition M n request resume (.cleanup c.state) _=_
  simp only [transition,if_pos exit]

private theorem leaf_internal_restore_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (restoreMachine M).Cfg) (exit : c.state=(restoreMachine M).qHalt) :
    (machine M n request resume).step (liftRestore M n request resume c)=relabel M n request resume (.pop .popStart) (liftRestore M n request resume c) := by
  apply leaf_internal_stay_step
  change transition M n request resume (.restore c.state) _=_
  simp only [transition,if_pos exit]

private theorem leaf_internal_output_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (exit : c.state=(outputMachine M).qHalt) :
    (machine M n request resume).step (liftOutput M n request resume label c)=relabel M n request resume (.body (resume label)) (liftOutput M n request resume label c) := by
  apply leaf_internal_stay_step
  change transition M n request resume (.output label c.state) _=_
  simp only [transition,if_pos exit]

private theorem leaf_internal_finish_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (exit : c.state=(finishMachine M).qHalt) :
    (machine M n request resume).step (liftFinish M n request resume c)=relabel M n request resume (.halt) (liftFinish M n request resume c) := by
  apply leaf_internal_stay_step
  change transition M n request resume (.finish c.state) _=_
  simp only [transition,if_pos exit]

private theorem leaf_internal_body_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (exit : c.state=(bodyMachine M).qHalt) :
    (machine M n request resume).step (liftBody M n request resume c)=relabel M n request resume ( .returning (returnMachine M).qStart) (liftBody M n request resume c) := by
  apply leaf_internal_stay_step
  change transition M n request resume (.body c.state) _=_
  simp only [transition,if_pos exit]

private theorem leaf_internal_body_request_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (label : Fin n) (live : c.state≠M.qHalt)
    (call : request c.state=some label) :
    (machine M n request resume).step (liftBody M n request resume c)=
      relabel M n request resume (.input label .before) (liftBody M n request resume c) := by
  apply leaf_internal_stay_step
  change transition M n request resume (.body c.state) _=_
  simp only [transition,if_neg live,call]

private theorem leaf_internal_push_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (exit : c.state=.pushDone) :
    (machine M n request resume).step (liftPush M n request resume c)=
      relabel M n request resume (.reservation .seek) (liftPush M n request resume c) := by
  apply leaf_internal_stay_step
  change transition M n request resume (.push c.state) _=_
  simp only [transition,if_pos exit]

private theorem leaf_internal_pop_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (label : Fin n) (exit : c.state=.resume label) :
    (machine M n request resume).step (liftPop M n request resume c)=
      relabel M n request resume (.output label .before) (liftPop M n request resume c) := by
  apply leaf_internal_stay_step
  change transition M n request resume (.pop c.state) _=_
  simp only [transition,exit]

private theorem leaf_internal_inspect_root_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.inspectStack)
    (root : c.cells (stackTape M) (c.head (stackTape M))=none) :
    (machine M n request resume).step c=relabel M n request resume (.finish .rewind) c := by
  apply leaf_internal_stay_step
  simp only [phase,transition,if_pos root]

private theorem leaf_internal_inspect_parent_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.inspectStack)
    (parent : c.cells (stackTape M) (c.head (stackTape M))≠none) :
    (machine M n request resume).step c=
      headFrame M n request resume (.restore .rewind) c (stackTape M) (c.head (stackTape M)+1) := by
  apply leaf_internal_right_step
  simp only [phase,transition,if_neg parent]

private theorem leaf_internal_reset_marker_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.resetBuffer)
    (marker : c.cells (bufferTape M) (c.head (bufferTape M))=some (M.startSym,true)) :
    (machine M n request resume).step c=
      headFrame M n request resume (.body M.qStart) c (bufferTape M) (c.head (bufferTape M)+1) := by
  apply leaf_internal_right_step
  simp only [phase,transition,if_pos marker]

private theorem leaf_internal_reset_live_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.resetBuffer)
    (marker : c.cells (bufferTape M) (c.head (bufferTape M))≠some (M.startSym,true))
    (present : c.cells (bufferTape M) (c.head (bufferTape M))≠none) :
    (machine M n request resume).step c=
      headFrame M n request resume .resetBuffer c (bufferTape M) (c.head (bufferTape M)-1) := by
  apply leaf_internal_left_step M n request resume _ _ _ present
  simp only [phase,transition,if_neg marker]

end IntMul.FlatRecursiveScheduler



namespace IntMul.FlatRecursiveScheduler

open IntMul.TrackedBankedSimulation (Sym)

private theorem leaf_internal_flatrecursiveschedulerleafframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def leaf_internal_leafInspection (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    (machine M n request resume).Cfg :=
  FlatRecursiveReturn.inspectionFrame M n request resume (nativeBase M n request resume x y) 1 1 (fun _ => 1) w

private noncomputable def leaf_internal_leafShiftParent (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    (TrackedOutputShift.machine M).Cfg where
  state := .rewind
  cells := fun i => (leaf_internal_leafInspection M n request resume x y w).cells
    (FixedTapeExtension.oldTape (TrackedOutputShift.machine M) i)
  head := fun i => (leaf_internal_leafInspection M n request resume x y w).head
    (FixedTapeExtension.oldTape (TrackedOutputShift.machine M) i)

private noncomputable def leaf_internal_leafShiftPadBase (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) : (finishMachine M).Cfg where
  state := .rewind
  cells := (leaf_internal_leafInspection M n request resume x y w).cells
  head := (leaf_internal_leafInspection M n request resume x y w).head

private noncomputable def leaf_internal_leafShiftStart (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) : (finishMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedOutputShift.machine M) (leaf_internal_leafShiftPadBase M n request resume x y w)
    (TrackedOutputShift.rewindFrame M (leaf_internal_leafShiftParent M n request resume x y w) w (w.length+2))

private noncomputable def leaf_internal_leafShiftFinal (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) : (finishMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedOutputShift.machine M) (leaf_internal_leafShiftPadBase M n request resume x y w)
    (TrackedOutputShift.finalFrame M (leaf_internal_leafShiftParent M n request resume x y w) w)

private theorem leaf_internal_flatrecursiveschedulerleafframes_return_idem (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List Bool) :
    TrackedOutputReturn.bufferTape M (TrackedOutputReturn.bufferTape M base sigma w) sigma w=
      TrackedOutputReturn.bufferTape M base sigma w := by
  funext p
  by_cases hp : p < sigma
  · simp only [TrackedOutputReturn.bufferTape,if_pos hp]
  · simp only [TrackedOutputReturn.bufferTape,if_neg hp]

private theorem leaf_internal_leaf_shift_old_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    TrackedOutputShift.rewindFrame M (leaf_internal_leafShiftParent M n request resume x y w) w (w.length+2)=
      leaf_internal_leafShiftParent M n request resume x y w := by
  apply leaf_internal_flatrecursiveschedulerleafframes_cfg_ext
  · rfl
  · funext i
    simp only [TrackedOutputShift.rewindFrame]
    by_cases hi : i.val=1
    · simp only [if_pos hi,leaf_internal_leafShiftParent,leaf_internal_leafInspection,FlatRecursiveReturn.inspectionFrame,
        FixedTapeExtension.oldTape,dif_pos i.isLt,dif_neg (by omega : ¬2 ≤ i.val),if_pos hi]
      exact leaf_internal_flatrecursiveschedulerleafframes_return_idem M _ 1 w
    · simp only [if_neg hi]
  · funext i
    simp only [TrackedOutputShift.rewindFrame]
    by_cases hi : i.val=1
    · simp only [if_pos hi,leaf_internal_leafShiftParent,leaf_internal_leafInspection,FlatRecursiveReturn.inspectionFrame,
        FixedTapeExtension.oldTape,dif_pos i.isLt,dif_neg (by omega : ¬2 ≤ i.val),if_pos hi]
      omega
    · simp only [if_neg hi]

private theorem leaf_internal_leaf_shift_start_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    relabel M n request resume (.finish .rewind) (leaf_internal_leafInspection M n request resume x y w)=
      liftFinish M n request resume (leaf_internal_leafShiftStart M n request resume x y w) := by
  rw [leaf_internal_leafShiftStart,leaf_internal_leaf_shift_old_ready]
  have hp : FixedTapeExtension.embed (TrackedOutputShift.machine M)
      (leaf_internal_leafShiftPadBase M n request resume x y w) (leaf_internal_leafShiftParent M n request resume x y w)=
      leaf_internal_leafShiftPadBase M n request resume x y w := by
    apply leaf_internal_flatrecursiveschedulerleafframes_cfg_ext
    · rfl
    · apply leaf_internal_extension_cells_ready
      intro j
      rfl
    · apply leaf_internal_extension_heads_ready
      intro j
      rfl
  rw [hp]
  rfl

private theorem leaf_internal_flatrecursiveschedulerleafframes_initial_zero (N : MultitapeTM) (x y : List Bool) (i : Fin N.k) :
    (N.initCfg x y).cells i 0=N.startSym := by
  simp only [MultitapeTM.initCfg]
  split <;> rfl

private theorem leaf_internal_flatrecursiveschedulerleafframes_initial_empty (N : MultitapeTM) (x y : List Bool) (i : Fin N.k) (hi : i.val ≠ 0) :
    (N.initCfg x y).cells i=N.tapeOf [] := by
  simp only [MultitapeTM.initCfg]
  rw [if_neg (by intro h; exact hi (congrArg Fin.val h))]

private theorem leaf_internal_leaf_stack_root (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    (leaf_internal_leafInspection M n request resume x y w).cells (stackTape M)
      ((leaf_internal_leafInspection M n request resume x y w).head (stackTape M))=none := by
  have hi : ¬(stackTape M).val < M.k+2 := by change ¬M.k+2 < M.k+2; omega
  simp only [leaf_internal_leafInspection,FlatRecursiveReturn.inspectionFrame,dif_neg hi,Nat.sub_self,
    FiniteContinuationStack.freshTape,if_pos (by omega : (0 : ℕ) < 1),nativeBase]
  exact leaf_internal_flatrecursiveschedulerleafframes_initial_zero _ _ _ _

private theorem leaf_internal_flatrecursiveschedulerleafframes_output_base_eq (M : MultitapeTM) (a b : ℕ → Sym M) (w : List Bool) (h : a 0=b 0) :
    TrackedOutputShift.outputTape M a w=TrackedOutputShift.outputTape M b w := by
  funext p
  by_cases hp : p=0
  · subst p
    simp only [TrackedOutputShift.outputTape,if_true,h]
  · simp only [TrackedOutputShift.outputTape,if_neg hp]

private theorem leaf_internal_flatrecursiveschedulerleafframes_fresh_native (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (x y : List Bool) (i : Fin (M.k+3)) (hi : i.val ≠ 0) :
    TrackedBankCleanup.freshTape M (((machine M n request resume).initCfg x y).cells i) 1=
      ((machine M n request resume).initCfg x y).cells i := by
  rw [leaf_internal_flatrecursiveschedulerleafframes_initial_empty (machine M n request resume) x y i hi]
  funext p
  cases p with
  | zero => rfl
  | succ p => simp [TrackedBankCleanup.freshTape,MultitapeTM.tapeOf]

private theorem leaf_internal_leaf_final_native (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    relabel M n request resume .halt (liftFinish M n request resume (leaf_internal_leafShiftFinal M n request resume x y w))=
      nativeFinalFrame M n request resume x y w := by
  apply leaf_internal_flatrecursiveschedulerleafframes_cfg_ext
  · rfl
  · funext i p
    have hik : i.val < M.k+3 := i.isLt
    simp only [relabel,liftFinish,leaf_internal_leafShiftFinal,FixedTapeExtension.embed,nativeFinalFrame]
    by_cases hb : i.val=1
    · have hi : i.val < M.k+2 := by have := M.two_le_k; omega
      simp only [dif_pos hi,TrackedOutputShift.finalFrame,FixedTapeExtension.innerTape,if_pos hb]
      have hzero : (leaf_internal_leafShiftParent M n request resume x y w).cells ⟨i.val,hi⟩ 0=
          ((machine M n request resume).initCfg x y).cells i 0 := by
        simp only [leaf_internal_leafShiftParent,leaf_internal_leafInspection,FlatRecursiveReturn.inspectionFrame,
          FixedTapeExtension.oldTape,dif_pos hi,dif_neg (by omega : ¬2 ≤ i.val),if_pos hb,
          TrackedOutputReturn.bufferTape,if_pos (by omega : (0 : ℕ) < 1),nativeBase]
      exact congrFun (leaf_internal_flatrecursiveschedulerleafframes_output_base_eq M _ _ w hzero) p
    · simp only [if_neg hb]
      by_cases hi : i.val < M.k+2
      · simp only [dif_pos hi,TrackedOutputShift.finalFrame,FixedTapeExtension.innerTape,if_neg hb,
          leaf_internal_leafShiftParent,leaf_internal_leafInspection,FlatRecursiveReturn.inspectionFrame,
          FixedTapeExtension.oldTape,dif_pos hi]
        by_cases hw : 2 ≤ i.val
        · simp only [dif_pos hw,nativeBase]
          exact congrFun (leaf_internal_flatrecursiveschedulerleafframes_fresh_native M n request resume x y i (by omega)) p
        · simp only [dif_neg hw,if_neg hb,nativeBase]
      · simp only [dif_neg hi,leaf_internal_leafShiftPadBase,leaf_internal_leafInspection,FlatRecursiveReturn.inspectionFrame,
          dif_neg hi,nativeBase]
        change TrackedBankCleanup.freshTape M (((machine M n request resume).initCfg x y).cells i) 1 p=_
        exact congrFun (leaf_internal_flatrecursiveschedulerleafframes_fresh_native M n request resume x y i (by omega)) p
  · funext i
    have hik : i.val < M.k+3 := i.isLt
    simp only [relabel,liftFinish,leaf_internal_leafShiftFinal,FixedTapeExtension.embed,nativeFinalFrame]
    by_cases hi : i.val < M.k+2
    · have hs : i≠stackTape M := by
        intro h; have hv := congrArg Fin.val h
        simp only [stackTape,FiniteContinuationStack.stackTape] at hv
        omega
      simp only [dif_pos hi,TrackedOutputShift.finalFrame,FixedTapeExtension.innerTape,if_neg hs]
      by_cases hb : i.val=1
      · simp only [if_pos hb,if_neg (by omega : i.val ≠ 0)]
      · simp only [if_neg hb,leaf_internal_leafShiftParent,leaf_internal_leafInspection,FlatRecursiveReturn.inspectionFrame,
          FixedTapeExtension.oldTape,dif_pos hi]
        by_cases hw : 2 ≤ i.val
        · simp only [dif_pos hw,if_neg (by omega : i.val ≠ 0)]
        · have hz : i.val=0 := by omega
          simp only [dif_neg hw,if_neg hb,nativeBase,if_pos hz]
    · have hs : i=stackTape M := by apply Fin.ext; simp only [stackTape,FiniteContinuationStack.stackTape]; omega
      simp only [dif_neg hi,leaf_internal_leafShiftPadBase,leaf_internal_leafInspection,FlatRecursiveReturn.inspectionFrame,
        dif_neg hi,Nat.sub_self,if_neg (by omega : i.val ≠ 0),if_neg (by omega : i.val ≠ 1),if_pos hs]

end IntMul.FlatRecursiveScheduler



namespace IntMul.FlatRecursiveSchedulerNativeInvariants

open IntMul.TrackedBankedSimulation (extents nextExtent)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

private theorem leaf_internal_flatrecursiveschedulernativeinvariants_word_letter (M : MultitapeTM) (x y : List Bool) (a : M.Sym)
    (ha : a ∈ inputWord M x y) : a = M.zero ∨ a = M.one ∨ a = M.sep := by
  simp only [inputWord,List.mem_append,List.mem_cons,List.mem_map] at ha
  rcases ha with ⟨b,_,rfl⟩ | (ha | ⟨b,_,rfl⟩)
  · cases b <;> simp [MultitapeTM.bitSym]
  · exact Or.inr (Or.inr ha)
  · cases b <;> simp [MultitapeTM.bitSym]

private theorem leaf_internal_flatrecursiveschedulernativeinvariants_word_payload_ne_start (M : MultitapeTM) (x y : List Bool) (p : ℕ) :
    (inputWord M x y).getD p M.blank ≠ M.startSym := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at hd
  by_cases hp : p < (inputWord M x y).length
  · rw [List.getD_eq_getElem _ _ hp]
    have hl := leaf_internal_flatrecursiveschedulernativeinvariants_word_letter M x y (inputWord M x y)[p] (List.getElem_mem hp)
    aesop
  · rw [List.getD_eq_default _ _ (by omega)]
    aesop

private theorem leaf_internal_initial_unique_markers (M : MultitapeTM) (x y : List Bool) :
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
        have h := leaf_internal_flatrecursiveschedulernativeinvariants_word_payload_ne_start M x y p
        simp only [h,Nat.succ_ne_zero]
      · simp only [if_neg hj,MultitapeTM.tapeOf,List.getD_nil]
        have hd := M.syms_distinct
        simp only [List.nodup_cons,List.mem_cons,not_or] at hd
        aesop

private theorem leaf_internal_initial_blank_tails (M : MultitapeTM) (x y : List Bool) :
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

private theorem leaf_internal_initial_heads_near (M : MultitapeTM) (x y : List Bool) :
    ∀ j, (M.initCfg x y).head j ≤ initialExtent M x y j + 1 := by
  intro j
  simp [MultitapeTM.initCfg]


end IntMul.FlatRecursiveSchedulerNativeInvariants



namespace IntMul.TrackedBankedSpace

open IntMul.TrackedBankedSimulation (nextExtent extents)

private theorem leaf_internal_trackedbankedspaceinvariants_cfg_ext (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem leaf_internal_trackedbankedspaceinvariants_halted_step (M : MultitapeTM) (c : M.Cfg) (halt : c.state = M.qHalt) : M.step c = c := by
  apply leaf_internal_trackedbankedspaceinvariants_cfg_ext
  · simp [MultitapeTM.step,halt,M.halt_fixed]
  · funext j
    simp only [MultitapeTM.step,halt,M.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,M.halt_fixed]

private theorem leaf_internal_trackedbankedspaceinvariants_blank_tail_step (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    ∀ j p, nextExtent M c extent j < p → (M.step c).cells j p = M.blank := by
  classical
  intro j p hp
  by_cases halt : c.state = M.qHalt
  · rw [leaf_internal_trackedbankedspaceinvariants_halted_step M c halt]
    simp only [nextExtent,if_pos halt] at hp
    exact tail j p hp
  · simp only [nextExtent,if_neg halt] at hp
    change Function.update (c.cells j) (c.head j)
      ((M.δ c.state (fun j => c.cells j (c.head j))).2 j).1 p = _
    rw [Function.update_of_ne (by omega : p ≠ c.head j)]
    exact tail j p (by omega)

/-- Blank tails remain blank beyond the tracked extent. This is the explicit
precondition needed to turn a false visited flag into a fresh-bank boundary. -/
private theorem leaf_internal_blank_tail_run (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ) (T : ℕ)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    ∀ j p, extents M c extent T j < p → (M.step^[T] c).cells j p = M.blank := by
  induction T with
  | zero => exact tail
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact leaf_internal_trackedbankedspaceinvariants_blank_tail_step M _ _ ih

private theorem leaf_internal_trackedbankedspaceinvariants_unique_marker_step (M : MultitapeTM) (c : M.Cfg)
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
private theorem leaf_internal_unique_marker_run (M : MultitapeTM) (c : M.Cfg) (T : ℕ)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0) :
    ∀ j p, (M.step^[T] c).cells j p = M.startSym ↔ p = 0 := by
  induction T with
  | zero => exact unique
  | succ T ih => rw [Function.iterate_succ_apply']; exact leaf_internal_trackedbankedspaceinvariants_unique_marker_step M _ ih

private theorem leaf_internal_trackedbankedspaceinvariants_head_step_bound (M : MultitapeTM) (c : M.Cfg) (j : Fin M.k) :
    (M.step c).head j ≤ c.head j + 1 := by
  simp only [MultitapeTM.step]
  split <;> omega

private theorem leaf_internal_trackedbankedspaceinvariants_near_step (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ)
    (near : ∀ j, c.head j ≤ extent j + 1) :
    ∀ j, (M.step c).head j ≤ nextExtent M c extent j + 1 := by
  classical
  intro j
  by_cases halt : c.state = M.qHalt
  · rw [leaf_internal_trackedbankedspaceinvariants_halted_step M c halt]
    simpa only [nextExtent,if_pos halt] using near j
  · simp only [nextExtent,if_neg halt]
    have hh := leaf_internal_trackedbankedspaceinvariants_head_step_bound M c j
    have hm := Nat.le_max_right (extent j) (c.head j)
    omega

private theorem leaf_internal_heads_near_run (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ) (T : ℕ)
    (near : ∀ j, c.head j ≤ extent j + 1) :
    ∀ j, (M.step^[T] c).head j ≤ extents M c extent T j + 1 := by
  induction T with
  | zero => exact near
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact leaf_internal_trackedbankedspaceinvariants_near_step M _ _ ih


end IntMul.TrackedBankedSpace




namespace IntMul.FlatRecursiveScheduler

open IntMul.TrackedBankPreparation (inputWord initialExtent)
open IntMul.TrackedBankedSimulation (extents)
open IntMul.TrackedBankCleanup (span)
open IntMul.FlatRecursiveReturn (returnedHeads)

private theorem leaf_internal_leaf_finish_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    ∃ t, t ≤ 4*w.length+5 ∧
      (machine M n request resume).step^[t]
        (liftFinish M n request resume (leaf_internal_leafShiftStart M n request resume x y w))=
        nativeFinalFrame M n request resume x y w := by
  have hr : (finishMachine M).step^[4*w.length+4] (leaf_internal_leafShiftStart M n request resume x y w)=
      leaf_internal_leafShiftFinal M n request resume x y w := by
    have h := (FixedTapeExtension.simulate_run (TrackedOutputShift.machine M)
      (leaf_internal_leafShiftPadBase M n request resume x y w)
      (TrackedOutputShift.rewindFrame M (leaf_internal_leafShiftParent M n request resume x y w) w (w.length+2))
      (4*w.length+4)).1
    rw [TrackedOutputShift.shift_correct] at h
    exact h
  have he : ((finishMachine M).step^[4*w.length+4]
      (leaf_internal_leafShiftStart M n request resume x y w)).state=(finishMachine M).qHalt := by
    rw [hr]
    rfl
  obtain ⟨s,hsclock,hsrun⟩ := leaf_internal_finish_to_halt M n request resume
    (leaf_internal_leafShiftStart M n request resume x y w) (4*w.length+4) he
  rw [hr] at hsrun
  refine ⟨s+1,by omega,?_⟩
  rw [Function.iterate_succ_apply',hsrun,leaf_internal_finish_dispatch M n request resume _ rfl,leaf_internal_leaf_final_native]

private theorem leaf_internal_leaf_root_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    ∃ t, t ≤ 4*w.length+6 ∧
      (machine M n request resume).step^[t] (leaf_internal_leafInspection M n request resume x y w)=
        nativeFinalFrame M n request resume x y w := by
  obtain ⟨s,hs,hr⟩ := leaf_internal_leaf_finish_correct M n request resume x y w
  refine ⟨s+1,by omega,?_⟩
  rw [Function.iterate_succ_apply,leaf_internal_inspect_root_dispatch M n request resume _ rfl
    (leaf_internal_leaf_stack_root M n request resume x y w),leaf_internal_leaf_shift_start_ready,hr]

/-- A complete ordinary leaf invocation through the very same fixed table
used for recursive calls, from native input to literal canonical output. -/
private theorem leaf_internal_leaf_run_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (x y : List Bool) (T : ℕ) (halt : (M.step^[T] (M.initCfg x y)).state=M.qHalt)
    (no_request : ∀ s, s < T → request (M.step^[s] (M.initCfg x y)).state=none)
    (w : List Bool) (out : (M.step^[T] (M.initCfg x y)).cells M.outTape=M.tapeOf (w.map M.bitSym)) :
    let d := M.step^[T] (M.initCfg x y)
    let e := extents M (M.initCfg x y) (initialExtent M x y) T
    ∃ t, t ≤ T+5*(inputWord M x y).length+7*w.length+max (d.head M.outTape) 1+
        span M (returnedHeads M d)+2*span M e+30 ∧
      (machine M n request resume).step^[t] ((machine M n request resume).initCfg x y)=
        nativeFinalFrame M n request resume x y w := by
  dsimp only
  let base := nativeBase M n request resume x y
  let c := M.initCfg x y
  let e := initialExtent M x y
  obtain ⟨b,hbclock,hbrun⟩ := bootstrap_correct M n request resume x y
  obtain ⟨s,hsclock,hsrun⟩ := leaf_internal_body_segment_correct M n request resume base 1 1 (fun _ => 1) e
    (by intro j; omega) c [] T (by intro j; exact (FlatRecursiveSchedulerNativeInvariants.leaf_internal_initial_unique_markers M x y j 0).mpr rfl)
    (FlatRecursiveSchedulerNativeInvariants.leaf_internal_initial_heads_near M x y) halt no_request
  obtain ⟨r,hrclock,hrrun⟩ := FlatRecursiveReturn.return_cleanup_correct M n request resume base 1 1
    (fun _ => 1) (extents M c e T) (by intro j; omega) (M.step^[T] c) [] w halt out
    (TrackedBankedSpace.leaf_internal_unique_marker_run M c T (FlatRecursiveSchedulerNativeInvariants.leaf_internal_initial_unique_markers M x y))
    (TrackedBankedSpace.leaf_internal_blank_tail_run M c e T (FlatRecursiveSchedulerNativeInvariants.leaf_internal_initial_blank_tails M x y))
  obtain ⟨f,hfclock,hfrun⟩ := leaf_internal_leaf_root_correct M n request resume x y w
  have hbs : (machine M n request resume).step^[s+b] ((machine M n request resume).initCfg x y)=
      bodyFrame M n request resume base 1 1 (fun _ => 1) (extents M c e T) (M.step^[T] c) [] := by
    rw [Function.iterate_add_apply,hbrun]
    exact hsrun
  have hret : (machine M n request resume).step^[r+(s+b)] ((machine M n request resume).initCfg x y)=
      leaf_internal_leafInspection M n request resume x y w := by
    rw [Function.iterate_add_apply,hbs,hrrun]
    rfl
  refine ⟨f+(r+(s+b)),by simp only [List.length_nil,Nat.zero_add,show max w.length 0=w.length by omega] at hrclock; dsimp only [base,c,e] at *; omega,?_⟩
  rw [Function.iterate_add_apply,hret,hfrun]

private theorem leaf_internal_native_final_output (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    (nativeFinalFrame M n request resume x y w).cells (machine M n request resume).outTape=
      (machine M n request resume).tapeOf (w.map (machine M n request resume).bitSym) := by
  funext p
  simp only [nativeFinalFrame,MultitapeTM.outTape,if_true]
  cases p with
  | zero =>
    simp only [TrackedOutputShift.outputTape,if_true,MultitapeTM.initCfg]
    split <;> rfl
  | succ p =>
    simp only [TrackedOutputShift.outputTape,Nat.succ_ne_zero,if_false,Nat.add_sub_cancel,MultitapeTM.tapeOf]
    by_cases hp : p < w.length
    · rw [List.getD_eq_getElem _ _ (by simpa using hp),List.getD_eq_getElem _ _ (by simpa using hp)]
      simp only [List.getElem_map,hp,decide_true]
      cases h : w[p] <;> rfl
    · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
      simp only [hp,decide_false]

private theorem leaf_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (x y : List Bool) (T : ℕ) (halt : (M.step^[T] (M.initCfg x y)).state=M.qHalt)
    (no_request : ∀ s, s < T → request (M.step^[s] (M.initCfg x y)).state=none)
    (w : List Bool) (out : (M.step^[T] (M.initCfg x y)).cells M.outTape=M.tapeOf (w.map M.bitSym)) :
    let d := M.step^[T] (M.initCfg x y)
    let e := extents M (M.initCfg x y) (initialExtent M x y) T
    ∃ t, t ≤ T+5*(inputWord M x y).length+7*w.length+max (d.head M.outTape) 1+
        span M (returnedHeads M d)+2*span M e+30 ∧
      (machine M n request resume).step^[t] ((machine M n request resume).initCfg x y)=
        nativeFinalFrame M n request resume x y w ∧
      (machine M n request resume).HaltsWithOutput x y t w := by
  dsimp only
  obtain ⟨t,ht,hr⟩ := leaf_internal_leaf_run_correct M n request resume x y T halt no_request w out
  refine ⟨t,ht,hr,?_⟩
  unfold MultitapeTM.HaltsWithOutput
  rw [hr]
  exact ⟨rfl,leaf_internal_native_final_output M n request resume x y w⟩

end IntMul.FlatRecursiveScheduler


open IntMul IntMul.FlatRecursiveScheduler IntMul.TrackedBankPreparation IntMul.TrackedBankedSimulation IntMul.TrackedBankCleanup IntMul.FlatRecursiveReturn

theorem solution (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (x y : List Bool) (T : ℕ) (halt : (M.step^[T] (M.initCfg x y)).state=M.qHalt)
    (no_request : ∀ s, s < T → request (M.step^[s] (M.initCfg x y)).state=none)
    (w : List Bool) (out : (M.step^[T] (M.initCfg x y)).cells M.outTape=M.tapeOf (w.map M.bitSym)) :
    let d := M.step^[T] (M.initCfg x y)
    let e := extents M (M.initCfg x y) (initialExtent M x y) T
    ∃ t, t ≤ T+5*(inputWord M x y).length+7*w.length+max (d.head M.outTape) 1+
        span M (returnedHeads M d)+2*span M e+30 ∧
      (machine M n request resume).step^[t] ((machine M n request resume).initCfg x y)=
        nativeFinalFrame M n request resume x y w ∧
      (machine M n request resume).HaltsWithOutput x y t w :=
  IntMul.FlatRecursiveScheduler.leaf_correct M n request resume x y T halt no_request w out

#print axioms solution
