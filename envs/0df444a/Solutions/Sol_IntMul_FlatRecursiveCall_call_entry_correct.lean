-- Prove2me | solution 1 for IntMul.FlatRecursiveCall.call_entry_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T02:50:31.040721+00:00
-- url     : https://prove2.me/submissions/62d8f81b-7412-417e-987b-b0acb9a572f3

import Definitions.Def_IntMul_FlatRecursiveCall
import Theorems.Thm_IntMul_TrackedChildInputBridge_input_correct
import Theorems.Thm_IntMul_TrackedBankReservation_reserve_correct
import Theorems.Thm_IntMul_TrackedBankPreparation_setup_correct
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Mathlib.Data.List.GetD
import Mathlib.Tactic


namespace IntMul.FlatRecursiveScheduler

private theorem call_internal_flatrecursiveschedulerpadding_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem call_internal_extension_old_cells (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) (j : Fin N.k) :
    (FixedTapeExtension.embed N base c).cells (FixedTapeExtension.oldTape N j)=c.cells j := by
  simp only [FixedTapeExtension.embed,FixedTapeExtension.oldTape,dif_pos j.isLt]
  have h : FixedTapeExtension.innerTape N ⟨j.val,by have := j.isLt; omega⟩ j.isLt=j := by apply Fin.ext; rfl
  rw [h]

private theorem call_internal_extension_old_heads (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) (j : Fin N.k) :
    (FixedTapeExtension.embed N base c).head (FixedTapeExtension.oldTape N j)=c.head j := by
  simp only [FixedTapeExtension.embed,FixedTapeExtension.oldTape,dif_pos j.isLt]
  have h : FixedTapeExtension.innerTape N ⟨j.val,by have := j.isLt; omega⟩ j.isLt=j := by apply Fin.ext; rfl
  rw [h]

private theorem call_internal_extension_extra_cells (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) :
    (FixedTapeExtension.embed N base c).cells (FixedTapeExtension.extraTape N)=base.cells (FixedTapeExtension.extraTape N) := by
  simp [FixedTapeExtension.embed,FixedTapeExtension.extraTape]

private theorem call_internal_extension_extra_heads (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) :
    (FixedTapeExtension.embed N base c).head (FixedTapeExtension.extraTape N)=base.head (FixedTapeExtension.extraTape N) := by
  simp [FixedTapeExtension.embed,FixedTapeExtension.extraTape]

private theorem call_internal_extension_cells_ready (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg)
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

private theorem call_internal_extension_heads_ready (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg)
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

private theorem call_internal_padded_init (N : MultitapeTM) (x y : List Bool) :
    (FixedTapeExtension.machine N).initCfg x y =
      FixedTapeExtension.embed N ((FixedTapeExtension.machine N).initCfg x y) (N.initCfg x y) := by
  apply call_internal_flatrecursiveschedulerpadding_cfg_ext
  · rfl
  · apply (call_internal_extension_cells_ready N _ _ ?_).symm
    intro j
    have hzero : FixedTapeExtension.oldTape N j=(FixedTapeExtension.machine N).inTape ↔ j=N.inTape := by
      constructor
      · intro h; apply Fin.ext
        have hv := congrArg (fun i : Fin (N.k+1) => i.val) h
        exact hv
      · intro h; subst j; rfl
    simp only [MultitapeTM.initCfg,hzero]
    split <;> rfl
  · apply (call_internal_extension_heads_ready N _ _ ?_).symm
    intro j
    rfl

end IntMul.FlatRecursiveScheduler



namespace IntMul.FlatRecursiveScheduler

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem call_internal_work_inner (M : MultitapeTM) (i : Fin (M.k+2)) (h : 2≤ i.val) :
    workTape M (innerTape M i h)=i := by
  apply Fin.ext
  simp only [workTape,innerTape]
  omega

private theorem call_internal_work_injective (M : MultitapeTM) : Function.Injective (workTape M) := by
  intro i j h
  apply Fin.ext
  have h := congrArg Fin.val h
  simp only [workTape] at h
  omega

private theorem call_internal_work_ne_buffer (M : MultitapeTM) (j : Fin M.k) :
    workTape M j≠TrackedChildInputBridge.bufferTape M := by
  intro h
  have h := congrArg Fin.val h
  simp only [workTape,TrackedChildInputBridge.bufferTape] at h
  omega

private theorem call_internal_embed_work (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) (p : ℕ) :
    (TrackedBankedSimulation.embed M base offset extent c).cells (workTape M j) (offset j+p)=
      some (c.cells j p,decide (p≤ extent j)) := by
  simp only [TrackedBankedSimulation.embed,workTape]
  rw [dif_pos (by omega)]
  have hi : innerTape M ⟨j.val+2,by omega⟩ (by change 2≤ j.val+2; omega)=j := by
    apply Fin.ext
    simp [innerTape]
  simp only [hi,if_neg (by omega : ¬offset j+p< offset j),show offset j+p-offset j=p by omega]

private theorem call_internal_embed_work_head (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) :
    (TrackedBankedSimulation.embed M base offset extent c).head (workTape M j)=offset j+c.head j := by
  simp only [TrackedBankedSimulation.embed,workTape]
  rw [dif_pos (by omega)]
  have hi : innerTape M ⟨j.val+2,by omega⟩ (by change 2≤ j.val+2; omega)=j := by
    apply Fin.ext
    simp [innerTape]
  rw [hi]

private theorem call_internal_embed_cells_ready (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
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
      have hw : workTape M j=i := call_internal_work_inner M i hi
      rw [hw,show offset j+(p-offset j)=p by omega] at h
      exact h.symm
  · simp only [dif_neg hi]

private theorem call_internal_embed_heads_ready (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (heads : ∀ j, base.head (workTape M j)=offset j+c.head j) :
    (TrackedBankedSimulation.embed M base offset extent c).head=base.head := by
  funext i
  dsimp only [TrackedBankedSimulation.embed]
  by_cases hi : 2≤ i.val
  · rw [dif_pos hi]
    have h := heads (innerTape M i hi)
    rw [call_internal_work_inner M i hi] at h
    exact h.symm
  · simp only [dif_neg hi]


end IntMul.FlatRecursiveScheduler



namespace IntMul.FlatRecursiveScheduler

open IntMul.TrackedBankedSimulation (extents)

private noncomputable def call_internal_bodyView (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) : (bodyMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankedSimulation.machine M)
    (stackBase M n request resume base rho)
    (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma v) offset extent c)


end IntMul.FlatRecursiveScheduler


namespace IntMul.FlatRecursiveScheduler

private theorem call_internal_flatrecursiveschedulerprograms_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem call_internal_flatrecursiveschedulerprograms_fixed_iterate (N : MultitapeTM) (c : N.Cfg) (fixed : N.step c=c) (T : ℕ) :
    N.step^[T] c=c := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,fixed]

private theorem call_internal_flatrecursiveschedulerprograms_halted_step (N : MultitapeTM) (c : N.Cfg) (halt : c.state=N.qHalt) : N.step c=c := by
  apply call_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp [MultitapeTM.step,halt,N.halt_fixed]
  · funext i
    simp only [MultitapeTM.step,halt,N.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,N.halt_fixed]

/-- First entry to any family of quiescent service exits preserves the exact
complete supplied terminal configuration, including all tape heads. -/
private theorem call_internal_flatrecursiveschedulerprograms_first_exit (N : MultitapeTM) (P : N.K → Prop)
    (fixed : ∀ d : N.Cfg, P d.state → N.step d=d) (c : N.Cfg) (T : ℕ)
    (exit : P (N.step^[T] c).state) :
    ∃ t, t≤ T ∧ N.step^[t] c=N.step^[T] c ∧ ∀ s, s< t → ¬P (N.step^[s] c).state := by
  classical
  have hex : ∃ t, P (N.step^[t] c).state := ⟨T,exit⟩
  let t := Nat.find hex
  have ht : t≤ T := Nat.find_min' hex exit
  have hp : P (N.step^[t] c).state := Nat.find_spec hex
  refine ⟨t,ht,?_,?_⟩
  · rw [show T=(T-t)+t by omega,Function.iterate_add_apply,call_internal_flatrecursiveschedulerprograms_fixed_iterate N _ (fixed _ hp)]
  · intro s hs
    exact Nat.find_min hex hs

private theorem call_internal_boot_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (live : c.state≠(bootMachine M).qHalt) :
    (machine M n request resume).step (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step c) := by
  have ht : transition M n request resume (.boot c.state) (fun i => c.cells i (c.head i))=
      (let r := (bootMachine M).δ c.state (fun i => c.cells i (c.head i)); (.boot r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply call_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftBoot,ht]
  · simp only [MultitapeTM.step,liftBoot,ht]
  · simp only [MultitapeTM.step,liftBoot,ht]

private theorem call_internal_boot_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((bootMachine M).step^[s] c).state≠(bootMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      call_internal_boot_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem call_internal_boot_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (T : ℕ)
    (exit : ((bootMachine M).step^[T] c).state=(bootMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := call_internal_flatrecursiveschedulerprograms_first_exit (bootMachine M)
    (fun q => q=(bootMachine M).qHalt) (by intro d hd; exact call_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [call_internal_boot_iterate M n request resume c s hlive,he]

private theorem call_internal_preparation_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (live : c.state≠(preparationMachine M).qHalt) :
    (machine M n request resume).step (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step c) := by
  have ht : transition M n request resume (.preparation c.state) (fun i => c.cells i (c.head i))=
      (let r := (preparationMachine M).δ c.state (fun i => c.cells i (c.head i)); (.preparation r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply call_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftPreparation,ht]
  · simp only [MultitapeTM.step,liftPreparation,ht]
  · simp only [MultitapeTM.step,liftPreparation,ht]

private theorem call_internal_preparation_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((preparationMachine M).step^[s] c).state≠(preparationMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      call_internal_preparation_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem call_internal_preparation_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (T : ℕ)
    (exit : ((preparationMachine M).step^[T] c).state=(preparationMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := call_internal_flatrecursiveschedulerprograms_first_exit (preparationMachine M)
    (fun q => q=(preparationMachine M).qHalt) (by intro d hd; exact call_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [call_internal_preparation_iterate M n request resume c s hlive,he]

private theorem call_internal_body_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (live : c.state≠(bodyMachine M).qHalt)
    (no_request : request c.state=none) :
    (machine M n request resume).step (liftBody M n request resume c)=
      liftBody M n request resume ((bodyMachine M).step c) := by
  have ht : transition M n request resume (.body c.state) (fun i => c.cells i (c.head i))=
      (let r := (bodyMachine M).δ c.state (fun i => c.cells i (c.head i)); (.body r.1,r.2)) := by
    simp only [transition,if_neg live,no_request]
  apply call_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftBody,ht]
  · simp only [MultitapeTM.step,liftBody,ht]
  · simp only [MultitapeTM.step,liftBody,ht]

private theorem call_internal_body_iterate (M : MultitapeTM) (n : ℕ)
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
      call_internal_body_step M n request resume _ (live T (by omega)) (no_request T (by omega)),Function.iterate_succ_apply']

private theorem call_internal_body_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (T : ℕ)
    (exit : ((bodyMachine M).step^[T] c).state=(bodyMachine M).qHalt)
    (no_request : ∀ s, s < T → request (((bodyMachine M).step^[s] c).state)=none) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftBody M n request resume c)=
      liftBody M n request resume ((bodyMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := call_internal_flatrecursiveschedulerprograms_first_exit (bodyMachine M)
    (fun q => q=(bodyMachine M).qHalt) (by intro d hd; exact call_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [call_internal_body_iterate M n request resume c s hlive (by intro r hr; exact no_request r (by omega)),he]

private theorem call_internal_input_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (live : c.state≠(inputMachine M).qHalt) :
    (machine M n request resume).step (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step c) := by
  have ht : transition M n request resume (.input label c.state) (fun i => c.cells i (c.head i))=
      (let r := (inputMachine M).δ c.state (fun i => c.cells i (c.head i)); (.input label r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply call_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftInput,ht]
  · simp only [MultitapeTM.step,liftInput,ht]
  · simp only [MultitapeTM.step,liftInput,ht]

private theorem call_internal_input_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((inputMachine M).step^[s] c).state≠(inputMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      call_internal_input_step M n request resume label _ (live T (by omega)),Function.iterate_succ_apply']

private theorem call_internal_input_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (T : ℕ)
    (exit : ((inputMachine M).step^[T] c).state=(inputMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := call_internal_flatrecursiveschedulerprograms_first_exit (inputMachine M)
    (fun q => q=(inputMachine M).qHalt) (by intro d hd; exact call_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [call_internal_input_iterate M n request resume label c s hlive,he]

private theorem call_internal_reservation_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (live : c.state≠(reservationMachine M).qHalt) :
    (machine M n request resume).step (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step c) := by
  have ht : transition M n request resume (.reservation c.state) (fun i => c.cells i (c.head i))=
      (let r := (reservationMachine M).δ c.state (fun i => c.cells i (c.head i)); (.reservation r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply call_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftReservation,ht]
  · simp only [MultitapeTM.step,liftReservation,ht]
  · simp only [MultitapeTM.step,liftReservation,ht]

private theorem call_internal_reservation_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((reservationMachine M).step^[s] c).state≠(reservationMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      call_internal_reservation_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem call_internal_reservation_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (T : ℕ)
    (exit : ((reservationMachine M).step^[T] c).state=(reservationMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := call_internal_flatrecursiveschedulerprograms_first_exit (reservationMachine M)
    (fun q => q=(reservationMachine M).qHalt) (by intro d hd; exact call_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [call_internal_reservation_iterate M n request resume c s hlive,he]

private theorem call_internal_return_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (live : c.state≠(returnMachine M).qHalt) :
    (machine M n request resume).step (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step c) := by
  have ht : transition M n request resume (.returning c.state) (fun i => c.cells i (c.head i))=
      (let r := (returnMachine M).δ c.state (fun i => c.cells i (c.head i)); (.returning r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply call_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftReturn,ht]
  · simp only [MultitapeTM.step,liftReturn,ht]
  · simp only [MultitapeTM.step,liftReturn,ht]

private theorem call_internal_return_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((returnMachine M).step^[s] c).state≠(returnMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      call_internal_return_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem call_internal_return_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (T : ℕ)
    (exit : ((returnMachine M).step^[T] c).state=(returnMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := call_internal_flatrecursiveschedulerprograms_first_exit (returnMachine M)
    (fun q => q=(returnMachine M).qHalt) (by intro d hd; exact call_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [call_internal_return_iterate M n request resume c s hlive,he]

private theorem call_internal_cleanup_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (live : c.state≠(cleanupMachine M).qHalt) :
    (machine M n request resume).step (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step c) := by
  have ht : transition M n request resume (.cleanup c.state) (fun i => c.cells i (c.head i))=
      (let r := (cleanupMachine M).δ c.state (fun i => c.cells i (c.head i)); (.cleanup r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply call_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftCleanup,ht]
  · simp only [MultitapeTM.step,liftCleanup,ht]
  · simp only [MultitapeTM.step,liftCleanup,ht]

private theorem call_internal_cleanup_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((cleanupMachine M).step^[s] c).state≠(cleanupMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      call_internal_cleanup_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem call_internal_cleanup_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (T : ℕ)
    (exit : ((cleanupMachine M).step^[T] c).state=(cleanupMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := call_internal_flatrecursiveschedulerprograms_first_exit (cleanupMachine M)
    (fun q => q=(cleanupMachine M).qHalt) (by intro d hd; exact call_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [call_internal_cleanup_iterate M n request resume c s hlive,he]

private theorem call_internal_restore_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (restoreMachine M).Cfg) (live : c.state≠(restoreMachine M).qHalt) :
    (machine M n request resume).step (liftRestore M n request resume c)=
      liftRestore M n request resume ((restoreMachine M).step c) := by
  have ht : transition M n request resume (.restore c.state) (fun i => c.cells i (c.head i))=
      (let r := (restoreMachine M).δ c.state (fun i => c.cells i (c.head i)); (.restore r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply call_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftRestore,ht]
  · simp only [MultitapeTM.step,liftRestore,ht]
  · simp only [MultitapeTM.step,liftRestore,ht]

private theorem call_internal_restore_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (restoreMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((restoreMachine M).step^[s] c).state≠(restoreMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftRestore M n request resume c)=
      liftRestore M n request resume ((restoreMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      call_internal_restore_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem call_internal_restore_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (restoreMachine M).Cfg) (T : ℕ)
    (exit : ((restoreMachine M).step^[T] c).state=(restoreMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftRestore M n request resume c)=
      liftRestore M n request resume ((restoreMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := call_internal_flatrecursiveschedulerprograms_first_exit (restoreMachine M)
    (fun q => q=(restoreMachine M).qHalt) (by intro d hd; exact call_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [call_internal_restore_iterate M n request resume c s hlive,he]

private theorem call_internal_output_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (live : c.state≠(outputMachine M).qHalt) :
    (machine M n request resume).step (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step c) := by
  have ht : transition M n request resume (.output label c.state) (fun i => c.cells i (c.head i))=
      (let r := (outputMachine M).δ c.state (fun i => c.cells i (c.head i)); (.output label r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply call_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftOutput,ht]
  · simp only [MultitapeTM.step,liftOutput,ht]
  · simp only [MultitapeTM.step,liftOutput,ht]

private theorem call_internal_output_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((outputMachine M).step^[s] c).state≠(outputMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      call_internal_output_step M n request resume label _ (live T (by omega)),Function.iterate_succ_apply']

private theorem call_internal_output_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (T : ℕ)
    (exit : ((outputMachine M).step^[T] c).state=(outputMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := call_internal_flatrecursiveschedulerprograms_first_exit (outputMachine M)
    (fun q => q=(outputMachine M).qHalt) (by intro d hd; exact call_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [call_internal_output_iterate M n request resume label c s hlive,he]

private theorem call_internal_finish_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (live : c.state≠(finishMachine M).qHalt) :
    (machine M n request resume).step (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step c) := by
  have ht : transition M n request resume (.finish c.state) (fun i => c.cells i (c.head i))=
      (let r := (finishMachine M).δ c.state (fun i => c.cells i (c.head i)); (.finish r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply call_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftFinish,ht]
  · simp only [MultitapeTM.step,liftFinish,ht]
  · simp only [MultitapeTM.step,liftFinish,ht]

private theorem call_internal_finish_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((finishMachine M).step^[s] c).state≠(finishMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      call_internal_finish_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem call_internal_finish_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (T : ℕ)
    (exit : ((finishMachine M).step^[T] c).state=(finishMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := call_internal_flatrecursiveschedulerprograms_first_exit (finishMachine M)
    (fun q => q=(finishMachine M).qHalt) (by intro d hd; exact call_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [call_internal_finish_iterate M n request resume c s hlive,he]

end IntMul.FlatRecursiveScheduler



namespace IntMul.FlatRecursiveScheduler

private theorem call_internal_flatrecursiveschedulerdispatch_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem call_internal_flatrecursiveschedulerdispatch_right_actions (M : MultitapeTM) (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M)
    (tape : Fin (M.k+3)) : moveActions M a tape .right=
      fun i => (a i,if i=tape then .right else .stay) := by
  classical
  funext i
  simp only [moveActions]
  split_ifs <;> cases a i <;> rfl

private theorem call_internal_flatrecursiveschedulerdispatch_left_actions (M : MultitapeTM) (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M)
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

private theorem call_internal_stay_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (q : State M n)
    (ht : transition M n request resume c.state (fun i => c.cells i (c.head i))=
      (q,fun i => (c.cells i (c.head i),.stay))) :
    (machine M n request resume).step c=relabel M n request resume q c := by
  apply call_internal_flatrecursiveschedulerdispatch_cfg_ext
  · simp only [MultitapeTM.step,ht,relabel]
  · simp only [MultitapeTM.step,ht,relabel]
    funext i
    rw [Function.update_eq_self]
  · simp only [MultitapeTM.step,ht,relabel]

private theorem call_internal_right_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (q : State M n) (tape : Fin (M.k+3))
    (ht : transition M n request resume c.state (fun i => c.cells i (c.head i))=
      (q,moveActions M (fun i => c.cells i (c.head i)) tape .right)) :
    (machine M n request resume).step c=headFrame M n request resume q c tape (c.head tape+1) := by
  classical
  rw [call_internal_flatrecursiveschedulerdispatch_right_actions] at ht
  apply call_internal_flatrecursiveschedulerdispatch_cfg_ext
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

private theorem call_internal_left_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (q : State M n) (tape : Fin (M.k+3))
    (present : c.cells tape (c.head tape)≠none)
    (ht : transition M n request resume c.state (fun i => c.cells i (c.head i))=
      (q,moveActions M (fun i => c.cells i (c.head i)) tape .left)) :
    (machine M n request resume).step c=headFrame M n request resume q c tape (c.head tape-1) := by
  classical
  rw [call_internal_flatrecursiveschedulerdispatch_left_actions M _ tape present] at ht
  apply call_internal_flatrecursiveschedulerdispatch_cfg_ext
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

private theorem call_internal_boot_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (exit : c.state=(bootMachine M).qHalt) :
    (machine M n request resume).step (liftBoot M n request resume c)=headFrame M n request resume (.preparation .mark) (liftBoot M n request resume c) (stackTape M) (c.head (stackTape M)+1) := by
  apply call_internal_right_step
  change transition M n request resume (.boot c.state) _=_
  simp only [transition,if_pos exit]

private theorem call_internal_preparation_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (exit : c.state=(preparationMachine M).qHalt) :
    (machine M n request resume).step (liftPreparation M n request resume c)=relabel M n request resume (.resetBuffer) (liftPreparation M n request resume c) := by
  apply call_internal_stay_step
  change transition M n request resume (.preparation c.state) _=_
  simp only [transition,if_pos exit]

private theorem call_internal_input_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (exit : c.state=(inputMachine M).qHalt) :
    (machine M n request resume).step (liftInput M n request resume label c)=relabel M n request resume (.push (.pushStart label)) (liftInput M n request resume label c) := by
  apply call_internal_stay_step
  change transition M n request resume (.input label c.state) _=_
  simp only [transition,if_pos exit]

private theorem call_internal_reservation_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (exit : c.state=(reservationMachine M).qHalt) :
    (machine M n request resume).step (liftReservation M n request resume c)=relabel M n request resume (.preparation .mark) (liftReservation M n request resume c) := by
  apply call_internal_stay_step
  change transition M n request resume (.reservation c.state) _=_
  simp only [transition,if_pos exit]

private theorem call_internal_return_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (exit : c.state=(returnMachine M).qHalt) :
    (machine M n request resume).step (liftReturn M n request resume c)=relabel M n request resume (.cleanup .rewind) (liftReturn M n request resume c) := by
  apply call_internal_stay_step
  change transition M n request resume (.returning c.state) _=_
  simp only [transition,if_pos exit]

private theorem call_internal_cleanup_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (exit : c.state=(cleanupMachine M).qHalt)
    (present : c.cells (stackTape M) (c.head (stackTape M))≠none) :
    (machine M n request resume).step (liftCleanup M n request resume c)=headFrame M n request resume (.inspectStack) (liftCleanup M n request resume c) (stackTape M) (c.head (stackTape M)-1) := by
  apply call_internal_left_step M n request resume _ _ _ present
  change transition M n request resume (.cleanup c.state) _=_
  simp only [transition,if_pos exit]

private theorem call_internal_restore_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (restoreMachine M).Cfg) (exit : c.state=(restoreMachine M).qHalt) :
    (machine M n request resume).step (liftRestore M n request resume c)=relabel M n request resume (.pop .popStart) (liftRestore M n request resume c) := by
  apply call_internal_stay_step
  change transition M n request resume (.restore c.state) _=_
  simp only [transition,if_pos exit]

private theorem call_internal_output_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (exit : c.state=(outputMachine M).qHalt) :
    (machine M n request resume).step (liftOutput M n request resume label c)=relabel M n request resume (.body (resume label)) (liftOutput M n request resume label c) := by
  apply call_internal_stay_step
  change transition M n request resume (.output label c.state) _=_
  simp only [transition,if_pos exit]

private theorem call_internal_finish_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (exit : c.state=(finishMachine M).qHalt) :
    (machine M n request resume).step (liftFinish M n request resume c)=relabel M n request resume (.halt) (liftFinish M n request resume c) := by
  apply call_internal_stay_step
  change transition M n request resume (.finish c.state) _=_
  simp only [transition,if_pos exit]

private theorem call_internal_body_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (exit : c.state=(bodyMachine M).qHalt) :
    (machine M n request resume).step (liftBody M n request resume c)=relabel M n request resume ( .returning (returnMachine M).qStart) (liftBody M n request resume c) := by
  apply call_internal_stay_step
  change transition M n request resume (.body c.state) _=_
  simp only [transition,if_pos exit]

private theorem call_internal_body_request_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (label : Fin n) (live : c.state≠M.qHalt)
    (call : request c.state=some label) :
    (machine M n request resume).step (liftBody M n request resume c)=
      relabel M n request resume (.input label .before) (liftBody M n request resume c) := by
  apply call_internal_stay_step
  change transition M n request resume (.body c.state) _=_
  simp only [transition,if_neg live,call]

private theorem call_internal_push_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (exit : c.state=.pushDone) :
    (machine M n request resume).step (liftPush M n request resume c)=
      relabel M n request resume (.reservation .seek) (liftPush M n request resume c) := by
  apply call_internal_stay_step
  change transition M n request resume (.push c.state) _=_
  simp only [transition,if_pos exit]

private theorem call_internal_pop_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (label : Fin n) (exit : c.state=.resume label) :
    (machine M n request resume).step (liftPop M n request resume c)=
      relabel M n request resume (.output label .before) (liftPop M n request resume c) := by
  apply call_internal_stay_step
  change transition M n request resume (.pop c.state) _=_
  simp only [transition,exit]

private theorem call_internal_inspect_root_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.inspectStack)
    (root : c.cells (stackTape M) (c.head (stackTape M))=none) :
    (machine M n request resume).step c=relabel M n request resume (.finish .rewind) c := by
  apply call_internal_stay_step
  simp only [phase,transition,if_pos root]

private theorem call_internal_inspect_parent_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.inspectStack)
    (parent : c.cells (stackTape M) (c.head (stackTape M))≠none) :
    (machine M n request resume).step c=
      headFrame M n request resume (.restore .rewind) c (stackTape M) (c.head (stackTape M)+1) := by
  apply call_internal_right_step
  simp only [phase,transition,if_neg parent]

private theorem call_internal_reset_marker_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.resetBuffer)
    (marker : c.cells (bufferTape M) (c.head (bufferTape M))=some (M.startSym,true)) :
    (machine M n request resume).step c=
      headFrame M n request resume (.body M.qStart) c (bufferTape M) (c.head (bufferTape M)+1) := by
  apply call_internal_right_step
  simp only [phase,transition,if_pos marker]

private theorem call_internal_reset_live_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.resetBuffer)
    (marker : c.cells (bufferTape M) (c.head (bufferTape M))≠some (M.startSym,true))
    (present : c.cells (bufferTape M) (c.head (bufferTape M))≠none) :
    (machine M n request resume).step c=
      headFrame M n request resume .resetBuffer c (bufferTape M) (c.head (bufferTape M)-1) := by
  apply call_internal_left_step M n request resume _ _ _ present
  simp only [phase,transition,if_neg marker]

end IntMul.FlatRecursiveScheduler



namespace IntMul.FlatRecursiveScheduler

private theorem call_internal_flatrecursiveschedulerreset_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def call_internal_resetFrame (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a r : ℕ) : (machine M n request resume).Cfg where
  state := .resetBuffer
  cells := c.cells
  head := Function.update c.head (bufferTape M) (sigma+(a-r))

private theorem call_internal_flatrecursiveschedulerreset_empty_return_scan (M : MultitapeTM) (base : ℕ → TrackedBankedSimulation.Sym M)
    (sigma p : ℕ) : TrackedOutputReturn.bufferTape M base sigma [] (sigma+p)=
      if p=0 then some (M.startSym,true) else some (M.blank,false) := by
  cases p with
  | zero => simp [TrackedOutputReturn.bufferTape]
  | succ p => simp [TrackedOutputReturn.bufferTape,show ¬sigma+(p+1) < sigma by omega,
      show sigma+(p+1)≠sigma by omega]

private theorem call_internal_reset_scan (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a r : ℕ)
    (empty : c.cells (bufferTape M)=TrackedOutputReturn.bufferTape M (c.cells (bufferTape M)) sigma []) :
    (call_internal_resetFrame M n request resume c sigma a r).cells (bufferTape M)
      ((call_internal_resetFrame M n request resume c sigma a r).head (bufferTape M))=
        if a ≤ r then some (M.startSym,true) else some (M.blank,false) := by
  simp only [call_internal_resetFrame,Function.update_self]
  rw [empty,call_internal_flatrecursiveschedulerreset_empty_return_scan]
  split_ifs <;> first | rfl | omega

private theorem call_internal_reset_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a r : ℕ)
    (empty : c.cells (bufferTape M)=TrackedOutputReturn.bufferTape M (c.cells (bufferTape M)) sigma [])
    (hr : r < a) :
    (machine M n request resume).step (call_internal_resetFrame M n request resume c sigma a r)=
      call_internal_resetFrame M n request resume c sigma a (r+1) := by
  have hscan := call_internal_reset_scan M n request resume c sigma a r empty
  rw [if_neg (by omega : ¬a ≤ r)] at hscan
  have hm : (call_internal_resetFrame M n request resume c sigma a r).cells (bufferTape M)
      ((call_internal_resetFrame M n request resume c sigma a r).head (bufferTape M))≠some (M.startSym,true) := by
    rw [hscan]
    intro h
    have h := congrArg Prod.snd (Option.some.inj h)
    cases h
  rw [call_internal_reset_live_step M n request resume _ rfl hm (by rw [hscan]; exact Option.some_ne_none _)]
  apply call_internal_flatrecursiveschedulerreset_cfg_ext
  · rfl
  · rfl
  · simp only [headFrame,call_internal_resetFrame,Function.update_self,Function.update_idem]
    congr 1
    omega

private theorem call_internal_reset_run (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a r : ℕ)
    (empty : c.cells (bufferTape M)=TrackedOutputReturn.bufferTape M (c.cells (bufferTape M)) sigma [])
    (hr : r ≤ a) :
    (machine M n request resume).step^[r] (call_internal_resetFrame M n request resume c sigma a 0)=
      call_internal_resetFrame M n request resume c sigma a r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply',ih (by omega),call_internal_reset_step M n request resume c sigma a r empty (by omega)]

private theorem call_internal_reset_complete (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a : ℕ)
    (phase : c.state=.resetBuffer) (head : c.head (bufferTape M)=sigma+a)
    (empty : c.cells (bufferTape M)=TrackedOutputReturn.bufferTape M (c.cells (bufferTape M)) sigma []) :
    (machine M n request resume).step^[a+1] c=
      headFrame M n request resume (.body M.qStart) c (bufferTape M) (sigma+1) := by
  have hstart : c=call_internal_resetFrame M n request resume c sigma a 0 := by
    apply call_internal_flatrecursiveschedulerreset_cfg_ext
    · exact phase
    · rfl
    · simp only [call_internal_resetFrame,Nat.sub_zero,←head]
      exact (Function.update_eq_self _ _).symm
  rw [hstart,Function.iterate_succ_apply',call_internal_reset_run M n request resume _ sigma a a empty le_rfl]
  have hm := call_internal_reset_scan M n request resume c sigma a a empty
  rw [if_pos le_rfl] at hm
  rw [call_internal_reset_marker_dispatch M n request resume _ rfl hm]
  apply call_internal_flatrecursiveschedulerreset_cfg_ext
  · rfl
  · rfl
  · simp only [headFrame,call_internal_resetFrame,Nat.sub_self,Nat.add_zero,Function.update_self,Function.update_idem]

end IntMul.FlatRecursiveScheduler



namespace IntMul.FiniteContinuationStack

open IntMul.TrackedBankedSimulation (Sym)

private theorem call_internal_finitecontinuationstacktape_zero_ne_one (M : MultitapeTM) : M.zero ≠ M.one := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,and_true] at hd
  tauto

private theorem call_internal_decode_onehot (M : MultitapeTM) (n : ℕ) (q : Fin n) (j : ℕ) :
    TrackedBankedSimulation.decode M (some (M.bitSym (decide (j = q.val)),true)) = M.one ↔ j = q.val := by
  by_cases hj : j = q.val
  · simp [hj,MultitapeTM.bitSym,TrackedBankedSimulation.decode]
  · simp [hj,MultitapeTM.bitSym,TrackedBankedSimulation.decode,call_internal_finitecontinuationstacktape_zero_ne_one M]

private theorem call_internal_record_bit (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n)
    (j : ℕ) (r : ℕ) (hr : r < j) :
    recordTape M n base rho q j (rho + r + 1) = some (M.bitSym (decide (r = q.val)),true) := by
  simp [recordTape,show ¬rho + r + 1 < rho by omega,
    show rho + r + 1 ≠ rho by omega,show rho + r + 1 < rho + j + 1 by omega,
    show rho + r + 1 - rho - 1 = r by omega]

private theorem call_internal_record_marker (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n) (j : ℕ) :
    recordTape M n base rho q j rho = some (M.sep,true) := by simp [recordTape]

private theorem call_internal_fresh_at (M : MultitapeTM) (base : ℕ → Sym M) (rho p : ℕ) (hp : rho ≤ p) :
    freshTape M base rho p = some (M.blank,false) := by simp [freshTape,show ¬p < rho by omega]

private theorem call_internal_marker_write (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n) :
    Function.update (freshTape M base rho) rho (some (M.sep,true)) = recordTape M n base rho q 0 := by
  funext p
  by_cases he : p = rho
  · subst p
    simp [recordTape]
  · rw [Function.update_of_ne he]
    by_cases hp : p < rho
    · simp [freshTape,recordTape,hp]
    · simp [freshTape,recordTape,hp,he,show ¬p < rho + 0 + 1 by omega]

private theorem call_internal_bit_write (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n) (j : ℕ) :
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

private theorem call_internal_bit_erase (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n)
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

private theorem call_internal_marker_erase (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n) :
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
private theorem call_internal_recovered_step (n : ℕ) (q : Fin n) (j : ℕ) (hj : j < n) :
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

private theorem call_internal_pop_scan (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ)
    (q : Fin n) (j : ℕ) (hj : j < n) :
    (popFrame M n base rho q j).cells (stackTape M) ((popFrame M n base rho q j).head (stackTape M)) =
      some (M.bitSym (decide (n - 1 - j = q.val)),true) := by
  simp only [popFrame,ite_true]
  have he : rho + (n - j) = rho + (n - 1 - j) + 1 := by omega
  rw [he,call_internal_record_bit M n _ rho q (n - j) (n - 1 - j) (by omega)]

end IntMul.FiniteContinuationStack



namespace IntMul.FiniteContinuationStack

open IntMul.TrackedBankedSimulation (Sym)

private theorem call_internal_finitecontinuationstacksteps_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem call_internal_finitecontinuationstacksteps_raw_other (M : MultitapeTM) (n : ℕ) (q : State n)
    (a : Fin (M.k + 3) → Sym M) (i : Fin (M.k + 3)) (hi : i ≠ stackTape M) :
    (rawTransition M n q a).2 i = (a i,.stay) := by
  classical
  cases q <;> dsimp only [rawTransition] <;> split_ifs <;> simp_all

private theorem call_internal_finitecontinuationstacksteps_protect_same_stay (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .stay = (a,.stay) := by cases a <;> rfl

/-- A tagged scan and tagged write make the physical protection wrapper
transparent; every non-stack tape remains exact and its head stays. -/
private theorem call_internal_finitecontinuationstacksteps_physical_transition (M : MultitapeTM) (n : ℕ) (q : State n)
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
    · rw [call_internal_finitecontinuationstacksteps_raw_other M n q a i hi,call_internal_finitecontinuationstacksteps_protect_same_stay]
      simp only [if_neg hi]

private theorem call_internal_push_marker_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step (pushStartFrame M n base rho q) = pushFrame M n base rho q 0 := by
  let a := fun i => (pushStartFrame M n base rho q).cells i ((pushStartFrame M n base rho q).head i)
  have hs : a (stackTape M) = some (M.blank,false) := by
    simp [a,pushStartFrame,freshTape]
  have ht := call_internal_finitecontinuationstacksteps_physical_transition M n (.pushStart q) a (pushFrame M n base rho q 0).state
    (M.blank,false) (M.sep,true) .right hs
    (by simp [rawTransition,pushFrame,show 0 < n by have := q.isLt; omega]) (by simp [rawTransition])
  dsimp only [a] at ht
  change transition M n (pushStartFrame M n base rho q).state _ = _ at ht
  apply call_internal_finitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,pushStartFrame,pushFrame,ite_true]
      exact call_internal_marker_write M n _ rho q
    · simp only [if_neg hi,pushStartFrame,pushFrame,if_neg hi]
      exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,pushStartFrame,pushFrame,ite_true,Nat.add_zero]
    · simp only [if_neg hi,pushStartFrame,pushFrame,if_neg hi]

private theorem call_internal_push_bit_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ)
    (q : Fin n) (j : ℕ) (hj : j < n) :
    (machine M n).step (pushFrame M n base rho q j) = pushFrame M n base rho q (j + 1) := by
  let a := fun i => (pushFrame M n base rho q j).cells i ((pushFrame M n base rho q j).head i)
  have hs : a (stackTape M) = some (M.blank,false) := by
    simp [a,pushFrame,recordTape,show ¬rho + j + 1 < rho by omega,show rho + j + 1 ≠ rho by omega]
  have ht := call_internal_finitecontinuationstacksteps_physical_transition M n (pushFrame M n base rho q j).state a
    (pushFrame M n base rho q (j + 1)).state (M.blank,false) (M.bitSym (decide (j = q.val)),true) .right hs
    (by simp only [pushFrame,dif_pos hj,rawTransition])
    (by simp only [pushFrame,dif_pos hj,rawTransition]; split_ifs <;> simp)
  dsimp only [a] at ht
  apply call_internal_finitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,pushFrame,ite_true]
      exact call_internal_bit_write M n _ rho q j
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
private theorem call_internal_push_dispatch (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step (pushFrame M n base rho q n) = popStartFrame M n base rho q := by
  have ht : transition M n (pushFrame M n base rho q n).state
      (fun i => (pushFrame M n base rho q n).cells i ((pushFrame M n base rho q n).head i)) =
      (.popStart,fun i => ((pushFrame M n base rho q n).cells i ((pushFrame M n base rho q n).head i),.stay)) := by
    simp only [pushFrame,dif_neg (by omega : ¬n < n),transition,rawTransition,call_internal_finitecontinuationstacksteps_protect_same_stay]
  apply call_internal_finitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    rfl

private theorem call_internal_pop_start_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step (popStartFrame M n base rho q) = popFrame M n base rho q 0 := by
  let a := fun i => (popStartFrame M n base rho q).cells i ((popStartFrame M n base rho q).head i)
  have hs : a (stackTape M) = some (M.blank,false) := by
    simp [a,popStartFrame,pushFrame,recordTape,show ¬rho + n + 1 < rho by omega,
      show rho + n + 1 ≠ rho by omega]
  have hf : recovered n q 0 = none := by
    simp [recovered,show ¬n - q.val ≤ 0 by have := q.isLt; omega]
  have ht := call_internal_finitecontinuationstacksteps_physical_transition M n .popStart a (popFrame M n base rho q 0).state
    (M.blank,false) (M.blank,false) .left hs
    (by simp only [rawTransition,if_pos (by have := q.isLt; omega : 0 < n),popFrame,
      dif_pos (by have := q.isLt; omega : 0 < n),hf])
    (by simp [rawTransition,show 0 < n by have := q.isLt; omega,hs])
  dsimp only [a] at ht
  change transition M n (popStartFrame M n base rho q).state _ = _ at ht
  apply call_internal_finitecontinuationstacksteps_cfg_ext
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

private theorem call_internal_pop_bit_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ)
    (q : Fin n) (j : ℕ) (hj : j < n) :
    (machine M n).step (popFrame M n base rho q j) = popFrame M n base rho q (j + 1) := by
  classical
  let a := fun i => (popFrame M n base rho q j).cells i ((popFrame M n base rho q j).head i)
  have hs : a (stackTape M) = some (M.bitSym (decide (n - 1 - j = q.val)),true) :=
    call_internal_pop_scan M n base rho q j hj
  have hpred : TrackedBankedSimulation.decode M (a (stackTape M)) = M.one ↔ n - 1 - j = q.val := by
    rw [hs]
    exact call_internal_decode_onehot M n q (n - 1 - j)
  have hf : (if TrackedBankedSimulation.decode M (a (stackTape M)) = M.one then
      some (⟨n - 1 - j,by omega⟩ : Fin n) else recovered n q j) = recovered n q (j + 1) := by
    simpa only [hpred] using call_internal_recovered_step n q j hj
  have ht := call_internal_finitecontinuationstacksteps_physical_transition M n (popFrame M n base rho q j).state a
    (popFrame M n base rho q (j + 1)).state
    (M.bitSym (decide (n - 1 - j = q.val)),true) (M.blank,false) .left hs
    (by simp only [popFrame,dif_pos hj,rawTransition]; rw [hf])
    (by simp only [popFrame,dif_pos hj,rawTransition]; split_ifs <;> simp)
  dsimp only [a] at ht
  apply call_internal_finitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,popFrame,ite_true]
      exact call_internal_bit_erase M n _ rho q j hj
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
private theorem call_internal_pop_marker_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step (popFrame M n base rho q n) = finalFrame M n base rho q := by
  let a := fun i => (popFrame M n base rho q n).cells i ((popFrame M n base rho q n).head i)
  have hs : a (stackTape M) = some (M.sep,true) := by
    simp [a,popFrame,recordTape]
  have hf : recovered n q n = some q := by simp [recovered]
  have ht := call_internal_finitecontinuationstacksteps_physical_transition M n (popFrame M n base rho q n).state a (.resume q)
    (M.sep,true) (M.blank,false) .stay hs
    (by simp only [popFrame,dif_neg (by omega : ¬n < n),hf,rawTransition,if_pos hs])
    (by simp [popFrame,hf,rawTransition])
  dsimp only [a] at ht
  apply call_internal_finitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,popFrame,finalFrame,pushStartFrame,ite_true,Nat.sub_self,Nat.add_zero]
      exact call_internal_marker_erase M n _ rho q
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

private theorem call_internal_flatrecursivestack_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem call_internal_push_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (live : c.state≠.pushDone) :
    (machine M n request resume).step (liftPush M n request resume c)=
      liftPush M n request resume ((FiniteContinuationStack.machine M n).step c) := by
  have ht : transition M n request resume (.push c.state) (fun i => c.cells i (c.head i))=
      (let r := FiniteContinuationStack.transition M n c.state (fun i => c.cells i (c.head i)); (.push r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply call_internal_flatrecursivestack_cfg_ext
  · simp only [MultitapeTM.step,liftPush,ht]
  · simp only [MultitapeTM.step,liftPush,ht]
  · simp only [MultitapeTM.step,liftPush,ht]

private theorem call_internal_push_run (M : MultitapeTM) (n : ℕ)
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
    rw [Function.iterate_succ_apply',ih (by omega),call_internal_push_step M n request resume _ hlive,
      FiniteContinuationStack.call_internal_push_bit_step M n base rho label j (by omega)]

private theorem call_internal_push_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (FiniteContinuationStack.machine M n).Cfg) (rho : ℕ) (label : Fin n) :
    (machine M n request resume).step^[n+1]
      (liftPush M n request resume (FiniteContinuationStack.pushStartFrame M n base rho label))=
      liftPush M n request resume (FiniteContinuationStack.pushFrame M n base rho label n) := by
  have hlive : (FiniteContinuationStack.pushStartFrame M n base rho label).state≠.pushDone := by simp [FiniteContinuationStack.pushStartFrame]
  rw [Function.iterate_add_apply,Function.iterate_one,call_internal_push_step M n request resume _ hlive,
    FiniteContinuationStack.call_internal_push_marker_step,call_internal_push_run M n request resume base rho label n le_rfl]

private theorem call_internal_pop_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (live : ∀ label, c.state≠.resume label) :
    (machine M n request resume).step (liftPop M n request resume c)=
      liftPop M n request resume ((FiniteContinuationStack.machine M n).step c) := by
  have ht : transition M n request resume (.pop c.state) (fun i => c.cells i (c.head i))=
      (let r := FiniteContinuationStack.transition M n c.state (fun i => c.cells i (c.head i)); (.pop r.1,r.2)) := by
    cases hs : c.state <;> first | rfl | skip
    rename_i label
    exact False.elim (live label hs)
  apply call_internal_flatrecursivestack_cfg_ext
  · simp only [MultitapeTM.step,liftPop,ht]
  · simp only [MultitapeTM.step,liftPop,ht]
  · simp only [MultitapeTM.step,liftPop,ht]

private theorem call_internal_pop_run (M : MultitapeTM) (n : ℕ)
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
    rw [Function.iterate_succ_apply',ih (by omega),call_internal_pop_step M n request resume _ hlive,
      FiniteContinuationStack.call_internal_pop_bit_step M n base rho label j (by omega)]

private theorem call_internal_pop_correct (M : MultitapeTM) (n : ℕ)
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
    rw [Function.iterate_add_apply,Function.iterate_one,call_internal_pop_step M n request resume _ hlive,
      FiniteContinuationStack.call_internal_pop_start_step,call_internal_pop_run M n request resume base rho label n le_rfl]
  have hm : ∀ q, (FiniteContinuationStack.popFrame M n base rho label n).state≠.resume q := by
    intro q
    simp [FiniteContinuationStack.popFrame]
  rw [show n+2=(n+1)+1 by omega,Function.iterate_succ_apply',hr,call_internal_pop_step M n request resume _ hm,
    FiniteContinuationStack.call_internal_pop_marker_step]

end IntMul.FlatRecursiveStack



namespace IntMul.FlatRecursiveCall

open IntMul.FlatRecursiveScheduler
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem call_internal_flatrecursivecallinputframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def call_internal_inputParent (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) : (TrackedChildInputBridge.machine M).Cfg where
  state := (TrackedChildInputBridge.machine M).qStart
  cells := fun i => base.cells (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) i)
  head := fun i => base.head (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) i)

private noncomputable def call_internal_inputPadBase (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) : (inputMachine M).Cfg where
  state := (inputMachine M).qStart
  cells := (call_internal_bodyView M n request resume base rho sigma offset extent c v).cells
  head := (call_internal_bodyView M n request resume base rho sigma offset extent c v).head

private noncomputable def call_internal_inputStart (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) : (inputMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedChildInputBridge.machine M)
    (call_internal_inputPadBase M n request resume base rho sigma offset extent c v)
    (TrackedChildInputBridge.initialFrame M (call_internal_inputParent M n request resume base) sigma offset extent c v)

private noncomputable def call_internal_inputFinal (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) : (inputMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedChildInputBridge.machine M)
    (call_internal_inputPadBase M n request resume base rho sigma offset extent c v)
    (TrackedChildInputBridge.finalFrame M (call_internal_inputParent M n request resume base) sigma offset extent c v x y)

private theorem call_internal_flatrecursivecallinputframes_word_before_heads (M : MultitapeTM) (base : (TrackedChildInputBridge.machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) :
    (TrackedChildInputBridge.beforeFrame M base sigma offset extent c v 0).head=
      TrackedChildInputBridge.initialHeads M base sigma offset extent c v := by
  funext i
  simp only [TrackedChildInputBridge.beforeFrame,Nat.sub_zero]
  by_cases hb : i=TrackedChildInputBridge.bufferTape M
  · subst i
    simp only [if_true,TrackedChildInputBridge.initialHeads,TrackedBankedSimulation.embed,
      TrackedChildInputBridge.bufferTape,dif_neg (by omega : ¬2 ≤ (1 : ℕ)),
      TrackedChildInputBridge.parentBase,if_true]
    omega
  · simp only [if_neg hb]
    by_cases hp : i=TrackedChildInputBridge.packetTape M
    · subst i
      simp only [if_true]
      exact (call_internal_embed_work_head M (TrackedChildInputBridge.parentBase M base sigma v)
        offset extent c M.outTape).symm
    · simp only [if_neg hp]

private theorem call_internal_flatrecursivecallinputframes_word_parent_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (sigma : ℕ) (v : List Bool) :
    TrackedChildInputBridge.parentBase M
      (call_internal_inputParent M n request resume base) sigma v=
      parentBase M n request resume base sigma v := by
  apply call_internal_flatrecursivecallinputframes_cfg_ext
  · rfl
  · funext i
    simp only [TrackedChildInputBridge.parentBase,call_internal_inputParent,parentBase]
    by_cases hb : i.val=1
    · have he : i=TrackedChildInputBridge.bufferTape M := Fin.ext hb
      simp only [if_pos he,if_pos hb]
    · have he : i≠TrackedChildInputBridge.bufferTape M := by intro h; exact hb (congrArg Fin.val h)
      simp only [if_neg he,if_neg hb]
  · funext i
    simp only [TrackedChildInputBridge.parentBase,call_internal_inputParent,parentBase]
    by_cases hb : i.val=1
    · have he : i=TrackedChildInputBridge.bufferTape M := Fin.ext hb
      simp only [if_pos he,if_pos hb]
    · have he : i≠TrackedChildInputBridge.bufferTape M := by intro h; exact hb (congrArg Fin.val h)
      simp only [if_neg he,if_neg hb]

private theorem call_internal_body_input_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) :
    relabel M n request resume (.input label .before)
      (bodyFrame M n request resume base rho sigma offset extent c v)=
    liftInput M n request resume label (call_internal_inputStart M n request resume base rho sigma offset extent c v) := by
  have hc : (TrackedChildInputBridge.initialFrame M (call_internal_inputParent M n request resume base)
      sigma offset extent c v).cells=
      (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma v) offset extent c).cells := by
    simp only [TrackedChildInputBridge.initialFrame,
      TrackedChildInputBridge.initialFrame,TrackedChildInputBridge.beforeFrame,
      TrackedChildInputBridge.initialCells,call_internal_flatrecursivecallinputframes_word_parent_ready]
  have hh : (TrackedChildInputBridge.initialFrame M (call_internal_inputParent M n request resume base)
      sigma offset extent c v).head=
      (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma v) offset extent c).head := by
    simp only [TrackedChildInputBridge.initialFrame,
      TrackedChildInputBridge.initialFrame,call_internal_flatrecursivecallinputframes_word_before_heads,
      TrackedChildInputBridge.initialHeads,call_internal_flatrecursivecallinputframes_word_parent_ready]
  apply call_internal_flatrecursivecallinputframes_cfg_ext
  · rfl
  · funext i
    simp only [relabel,bodyFrame,liftBody,liftInput,call_internal_inputStart,call_internal_inputPadBase,call_internal_bodyView,
      FixedTapeExtension.embed,hc]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape]
    · simp only [dif_neg hi]
  · funext i
    simp only [relabel,bodyFrame,liftBody,liftInput,call_internal_inputStart,call_internal_inputPadBase,call_internal_bodyView,
      FixedTapeExtension.embed,hh]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape]
    · simp only [dif_neg hi]

end IntMul.FlatRecursiveCall



namespace IntMul.FlatRecursiveCall

open IntMul.FlatRecursiveScheduler
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem call_internal_flatrecursivecallstackframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def call_internal_pushParent (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (FiniteContinuationStack.machine M n).Cfg where
  state := .popStart
  cells := (call_internal_inputFinal M n request resume base rho sigma offset extent c v x y).cells
  head := (call_internal_inputFinal M n request resume base rho sigma offset extent c v x y).head

private theorem call_internal_input_stack_cells (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (call_internal_inputFinal M n request resume base rho sigma offset extent c v x y).cells (stackTape M)=
      FiniteContinuationStack.freshTape M (base.cells (stackTape M)) rho := by
  have he : stackTape M=FixedTapeExtension.extraTape (TrackedChildInputBridge.machine M) := by
    apply Fin.ext; rfl
  simp only [call_internal_inputFinal,he,call_internal_extension_extra_cells,call_internal_inputPadBase,call_internal_bodyView,call_internal_extension_extra_cells]
  rw [show FixedTapeExtension.extraTape (TrackedChildInputBridge.machine M)=
    FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M) by rfl]
  simp only [call_internal_extension_extra_cells,call_internal_extension_extra_heads]
  rw [show FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M)=stackTape M by rfl]
  simp only [stackBase,eq_self,if_true]

private theorem call_internal_input_stack_head (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (call_internal_inputFinal M n request resume base rho sigma offset extent c v x y).head (stackTape M)=rho := by
  have he : stackTape M=FixedTapeExtension.extraTape (TrackedChildInputBridge.machine M) := by
    apply Fin.ext; rfl
  simp only [call_internal_inputFinal,he,call_internal_extension_extra_heads,call_internal_inputPadBase,call_internal_bodyView,call_internal_extension_extra_heads]
  rw [show FixedTapeExtension.extraTape (TrackedChildInputBridge.machine M)=
    FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M) by rfl]
  simp only [call_internal_extension_extra_cells,call_internal_extension_extra_heads]
  rw [show FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M)=stackTape M by rfl]
  simp only [stackBase,eq_self,if_true]

private theorem call_internal_input_push_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    relabel M n request resume (.push (.pushStart label))
      (liftInput M n request resume label (call_internal_inputFinal M n request resume base rho sigma offset extent c v x y))=
    liftPush M n request resume (FiniteContinuationStack.pushStartFrame M n
      (call_internal_pushParent M n request resume base rho sigma offset extent c v x y) rho label) := by
  apply call_internal_flatrecursivecallstackframes_cfg_ext
  · rfl
  · funext i p
    simp only [relabel,liftInput,liftPush,FiniteContinuationStack.pushStartFrame,call_internal_pushParent]
    by_cases hi : i=stackTape M
    · subst i
      simp only [if_true,call_internal_input_stack_cells,FiniteContinuationStack.freshTape]
      by_cases hp : p < rho <;> simp only [hp,if_true,if_false]
    · simp only [if_neg hi]
  · funext i
    simp only [relabel,liftInput,liftPush,FiniteContinuationStack.pushStartFrame,call_internal_pushParent]
    by_cases hi : i=stackTape M
    · subst i
      simp only [if_true,call_internal_input_stack_head]
    · simp only [if_neg hi]

end IntMul.FlatRecursiveCall



namespace IntMul.FlatRecursiveCall

open IntMul.FlatRecursiveScheduler
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem call_internal_flatrecursivecallreservationframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def call_internal_pushed (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (FiniteContinuationStack.machine M n).Cfg :=
  FiniteContinuationStack.pushFrame M n
    (call_internal_pushParent M n request resume base rho sigma offset extent c v x y) rho label n

private noncomputable def call_internal_reserveParent (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (TrackedBankReservation.machine M).Cfg where
  state := .seek
  cells := fun i => (call_internal_pushed M n request resume label base rho sigma offset extent c v x y).cells
    (FixedTapeExtension.oldTape (TrackedBankReservation.machine M) i)
  head := fun i => (call_internal_pushed M n request resume label base rho sigma offset extent c v x y).head
    (FixedTapeExtension.oldTape (TrackedBankReservation.machine M) i)

private noncomputable def call_internal_reservePadBase (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (reservationMachine M).Cfg where
  state := .seek
  cells := (call_internal_pushed M n request resume label base rho sigma offset extent c v x y).cells
  head := (call_internal_pushed M n request resume label base rho sigma offset extent c v x y).head

private noncomputable def call_internal_reserveStart (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (reservationMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankReservation.machine M)
    (call_internal_reservePadBase M n request resume label base rho sigma offset extent c v x y)
    (TrackedBankReservation.initialFrame M
      (call_internal_reserveParent M n request resume label base rho sigma offset extent c v x y)
      offset extent (parentAfterInput M c))

private noncomputable def call_internal_reserveFinal (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (reservationMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankReservation.machine M)
    (call_internal_reservePadBase M n request resume label base rho sigma offset extent c v x y)
    (TrackedBankReservation.finalFrame M
      (call_internal_reserveParent M n request resume label base rho sigma offset extent c v x y)
      offset extent (parentAfterInput M c))

private theorem call_internal_stack_ne_old (M : MultitapeTM) (i : Fin (M.k+2)) :
    FixedTapeExtension.oldTape (TrackedBankReservation.machine M) i≠stackTape M := by
  intro h
  have h := congrArg Fin.val h
  simp only [FixedTapeExtension.oldTape,stackTape,FiniteContinuationStack.stackTape] at h
  have := i.isLt
  omega

private theorem call_internal_reserve_parent_cells (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) (j : Fin M.k) (p : ℕ) :
    (call_internal_reserveParent M n request resume label base rho sigma offset extent c v x y).cells
      (workTape M j) (offset j+p)=some ((parentAfterInput M c).cells j p,decide (p≤ extent j)) := by
  simp only [call_internal_reserveParent,call_internal_pushed,FiniteContinuationStack.pushFrame,if_neg (call_internal_stack_ne_old M _),call_internal_pushParent]
  rw [show FixedTapeExtension.oldTape (TrackedBankReservation.machine M) (workTape M j)=
    FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) (workTape M j) by rfl]
  simp only [call_internal_inputFinal,call_internal_extension_old_cells,TrackedChildInputBridge.finalFrame,
    if_neg (call_internal_work_ne_buffer M j),TrackedChildInputBridge.initialCells,parentAfterInput]
  exact call_internal_embed_work M _ offset extent c j p

private theorem call_internal_reserve_parent_heads (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) (j : Fin M.k) :
    (call_internal_reserveParent M n request resume label base rho sigma offset extent c v x y).head
      (workTape M j)=offset j+(parentAfterInput M c).head j := by
  simp only [call_internal_reserveParent,call_internal_pushed,FiniteContinuationStack.pushFrame,if_neg (call_internal_stack_ne_old M _),call_internal_pushParent]
  rw [show FixedTapeExtension.oldTape (TrackedBankReservation.machine M) (workTape M j)=
    FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) (workTape M j) by rfl]
  simp only [call_internal_inputFinal,call_internal_extension_old_heads,TrackedChildInputBridge.finalFrame,
    if_neg (call_internal_work_ne_buffer M j),parentAfterInput]
  by_cases hj : j=M.outTape
  · subst j
    simp only [TrackedChildInputBridge.packetTape,eq_self,if_true,Nat.add_zero]
  · have hn : workTape M j≠TrackedChildInputBridge.packetTape M := by
      intro h; exact hj (call_internal_work_injective M h)
    rw [if_neg hn]
    simp only [if_neg hj,TrackedChildInputBridge.initialHeads]
    exact call_internal_embed_work_head M _ offset extent c j

private theorem call_internal_push_reserve_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    relabel M n request resume (.reservation .seek)
      (liftPush M n request resume (call_internal_pushed M n request resume label base rho sigma offset extent c v x y))=
    liftReservation M n request resume (call_internal_reserveStart M n request resume label base rho sigma offset extent c v x y) := by
  have hc : (TrackedBankReservation.initialFrame M
      (call_internal_reserveParent M n request resume label base rho sigma offset extent c v x y)
      offset extent (parentAfterInput M c)).cells=
      (call_internal_reserveParent M n request resume label base rho sigma offset extent c v x y).cells := by
    exact call_internal_embed_cells_ready M _ offset extent _ (call_internal_reserve_parent_cells M n request resume label base rho sigma offset extent c v x y)
  have hh : (TrackedBankReservation.initialFrame M
      (call_internal_reserveParent M n request resume label base rho sigma offset extent c v x y)
      offset extent (parentAfterInput M c)).head=
      (call_internal_reserveParent M n request resume label base rho sigma offset extent c v x y).head := by
    simp only [TrackedBankReservation.initialFrame,TrackedBankReservation.seekFrame,Nat.zero_min,Nat.add_zero]
    exact call_internal_embed_heads_ready M
      (TrackedBankReservation.parentBase M (call_internal_reserveParent M n request resume label base rho sigma offset extent c v x y))
      offset extent (parentAfterInput M c) (call_internal_reserve_parent_heads M n request resume label base rho sigma offset extent c v x y)
  apply call_internal_flatrecursivecallreservationframes_cfg_ext
  · rfl
  · funext i
    simp only [relabel,liftPush,liftReservation,call_internal_reserveStart,FixedTapeExtension.embed]
    rw [hc]
    simp only [call_internal_reserveParent,call_internal_reservePadBase]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
    · simp only [dif_neg hi]
  · funext i
    simp only [relabel,liftPush,liftReservation,call_internal_reserveStart,FixedTapeExtension.embed]
    rw [hh]
    simp only [call_internal_reserveParent,call_internal_reservePadBase]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
    · simp only [dif_neg hi]

end IntMul.FlatRecursiveCall



namespace IntMul.FlatRecursiveCall

open IntMul.FlatRecursiveScheduler
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)
open IntMul.TrackedBankReservation (newOffsets)

private theorem call_internal_flatrecursivecallpreparationframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def call_internal_preparationParent (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (TrackedBankPreparation.machine M).Cfg where
  state := .mark
  cells := (call_internal_reserveParent M n request resume label base rho sigma offset extent c v x y).cells
  head := (TrackedBankReservation.finalFrame M
    (call_internal_reserveParent M n request resume label base rho sigma offset extent c v x y)
    offset extent (parentAfterInput M c)).head

private noncomputable def call_internal_preparationPadBase (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (preparationMachine M).Cfg where
  state := .mark
  cells := (call_internal_reserveFinal M n request resume label base rho sigma offset extent c v x y).cells
  head := (call_internal_reserveFinal M n request resume label base rho sigma offset extent c v x y).head

private noncomputable def call_internal_preparationStart (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (preparationMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankPreparation.machine M)
    (call_internal_preparationPadBase M n request resume label base rho sigma offset extent c v x y)
    (TrackedBankPreparation.initialFrame M
      (call_internal_preparationParent M n request resume label base rho sigma offset extent c v x y)
      sigma (newOffsets M offset extent) x y)

private noncomputable def call_internal_preparationFinal (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (preparationMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankPreparation.machine M)
    (call_internal_preparationPadBase M n request resume label base rho sigma offset extent c v x y)
    (TrackedBankPreparation.readyFrame M
      (call_internal_preparationParent M n request resume label base rho sigma offset extent c v x y)
      sigma (newOffsets M offset extent) x y)

private theorem call_internal_preparation_fresh (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) (j : Fin M.k) :
    TrackedBankPreparation.freshTape M
      ((call_internal_preparationParent M n request resume label base rho sigma offset extent c v x y).cells (workTape M j))
      (newOffsets M offset extent j)=
    (call_internal_preparationParent M n request resume label base rho sigma offset extent c v x y).cells (workTape M j) := by
  funext p
  by_cases hp : p < newOffsets M offset extent j
  · simp only [TrackedBankPreparation.freshTape,if_pos hp]
  · simp only [TrackedBankPreparation.freshTape,if_neg hp]
    have ho : offset j≤ p := by unfold newOffsets at hp; omega
    have he : extent j < p-offset j := by unfold newOffsets at hp; omega
    have h := call_internal_reserve_parent_cells M n request resume label base rho sigma offset extent c v x y j (p-offset j)
    rw [show offset j+(p-offset j)=p by omega] at h
    simp only [parentAfterInput] at h
    rw [show (call_internal_preparationParent M n request resume label base rho sigma offset extent c v x y).cells
      (workTape M j) p=some (c.cells j (p-offset j),decide (p-offset j≤ extent j)) from h]
    rw [tail j (p-offset j) he]
    simp only [decide_eq_false_iff_not.mpr (by omega : ¬p-offset j≤ extent j)]

private theorem call_internal_preparation_source (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (call_internal_preparationParent M n request resume label base rho sigma offset extent c v x y).cells
      ⟨1,by change 1 < M.k+2; omega⟩=
      TrackedBankPreparation.sourceTape M
        ((call_internal_preparationParent M n request resume label base rho sigma offset extent c v x y).cells
          ⟨1,by change 1 < M.k+2; omega⟩) sigma (TrackedBankPreparation.inputWord M x y) := by
  have he : FixedTapeExtension.oldTape (TrackedBankReservation.machine M) ⟨1,by change 1 < M.k+2; omega⟩≠FiniteContinuationStack.stackTape M :=
    call_internal_stack_ne_old M _
  simp only [call_internal_preparationParent,call_internal_reserveParent,call_internal_pushed,FiniteContinuationStack.pushFrame,if_neg he,call_internal_pushParent]
  rw [show FixedTapeExtension.oldTape (TrackedBankReservation.machine M) ⟨1,by change 1 < M.k+2; omega⟩=
    FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) ⟨1,by change 1 < M.k+2; omega⟩ by rfl]
  simp only [call_internal_inputFinal,call_internal_extension_old_cells,TrackedChildInputBridge.finalFrame,
    show (⟨1,by change 1 < M.k+2; omega⟩ : Fin (M.k+2))=TrackedChildInputBridge.bufferTape M by rfl,if_true]
  funext p
  by_cases hp : p < sigma <;> simp only [TrackedBankPreparation.sourceTape,hp,if_true,if_false]

private theorem call_internal_preparation_source_head (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (call_internal_preparationParent M n request resume label base rho sigma offset extent c v x y).head
      ⟨1,by change 1 < M.k+2; omega⟩=sigma := by
  simp only [call_internal_preparationParent,TrackedBankReservation.finalFrame,dif_neg (by omega : ¬2≤ (1:ℕ)),
    call_internal_reserveParent,call_internal_pushed,FiniteContinuationStack.pushFrame,if_neg (call_internal_stack_ne_old M _),call_internal_pushParent]
  rw [show FixedTapeExtension.oldTape (TrackedBankReservation.machine M) ⟨1,by change 1 < M.k+2; omega⟩=
    FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) ⟨1,by change 1 < M.k+2; omega⟩ by rfl]
  simp only [call_internal_inputFinal,call_internal_extension_old_heads,TrackedChildInputBridge.finalFrame,
    show (⟨1,by change 1 < M.k+2; omega⟩ : Fin (M.k+2))=TrackedChildInputBridge.bufferTape M by rfl,if_true]

private theorem call_internal_reserve_preparation_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    relabel M n request resume (.preparation .mark)
      (liftReservation M n request resume (call_internal_reserveFinal M n request resume label base rho sigma offset extent c v x y))=
    liftPreparation M n request resume (call_internal_preparationStart M n request resume label base rho sigma offset extent c v x y) := by
  have hc : (TrackedBankReservation.finalFrame M
      (call_internal_reserveParent M n request resume label base rho sigma offset extent c v x y)
      offset extent (parentAfterInput M c)).cells=
      (call_internal_reserveParent M n request resume label base rho sigma offset extent c v x y).cells := by
    exact call_internal_embed_cells_ready M _ offset extent _ (call_internal_reserve_parent_cells M n request resume label base rho sigma offset extent c v x y)
  have hpc : (TrackedBankPreparation.initialFrame M
      (call_internal_preparationParent M n request resume label base rho sigma offset extent c v x y)
      sigma (newOffsets M offset extent) x y).cells=
      (call_internal_preparationParent M n request resume label base rho sigma offset extent c v x y).cells := by
    funext i
    simp only [TrackedBankPreparation.initialFrame]
    by_cases hw : 2≤ i.val
    · simp only [dif_pos hw]
      have h := call_internal_preparation_fresh M n request resume label base rho sigma offset extent c v x y tail (innerTape M i hw)
      rw [call_internal_work_inner M i hw] at h
      exact h
    · simp only [dif_neg hw]
      by_cases hb : i.val=1
      · simp only [if_pos hb]
        have hi : i=⟨1,by change 1 < M.k+2; omega⟩ := Fin.ext hb
        rw [hi]
        exact (call_internal_preparation_source M n request resume label base rho sigma offset extent c v x y).symm
      · simp only [if_neg hb]
  have hph : (TrackedBankPreparation.initialFrame M
      (call_internal_preparationParent M n request resume label base rho sigma offset extent c v x y)
      sigma (newOffsets M offset extent) x y).head=
      (call_internal_preparationParent M n request resume label base rho sigma offset extent c v x y).head := by
    funext i
    simp only [TrackedBankPreparation.initialFrame]
    by_cases hw : 2≤ i.val
    · simp only [dif_pos hw,call_internal_preparationParent,TrackedBankReservation.finalFrame]
    · simp only [dif_neg hw]
      by_cases hb : i.val=1
      · simp only [if_pos hb]
        have hi : i=⟨1,by change 1 < M.k+2; omega⟩ := Fin.ext hb
        rw [hi]
        exact (call_internal_preparation_source_head M n request resume label base rho sigma offset extent c v x y).symm
      · simp only [if_neg hb]
  apply call_internal_flatrecursivecallpreparationframes_cfg_ext
  · rfl
  · funext i
    simp only [relabel,liftReservation,liftPreparation,call_internal_preparationStart,FixedTapeExtension.embed]
    rw [hpc]
    simp only [call_internal_reserveFinal,call_internal_preparationPadBase,call_internal_preparationParent,FixedTapeExtension.embed]
    rw [hc]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape]
    · simp only [dif_neg hi]
  · funext i
    simp only [relabel,liftReservation,liftPreparation,call_internal_preparationStart,FixedTapeExtension.embed]
    rw [hph]
    simp only [call_internal_reserveFinal,call_internal_preparationPadBase,call_internal_preparationParent,FixedTapeExtension.embed]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape]
    · simp only [dif_neg hi]

end IntMul.FlatRecursiveCall



namespace IntMul.FlatRecursiveCall

open IntMul.FlatRecursiveScheduler
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)
open IntMul.TrackedBankReservation (newOffsets)

private theorem call_internal_flatrecursivecallchildframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem call_internal_flatrecursivecallchildframes_bank_empty_buffer (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) :
    TrackedBankPreparation.bankTape M base sigma []=TrackedOutputReturn.bufferTape M base sigma [] := by
  funext p
  by_cases hp : p < sigma
  · simp only [TrackedBankPreparation.bankTape,TrackedOutputReturn.bufferTape,if_pos hp]
  · by_cases he : p=sigma
    · subst p
      simp [TrackedBankPreparation.bankTape,TrackedOutputReturn.bufferTape,MultitapeTM.tapeOf]
    · simp only [TrackedBankPreparation.bankTape,TrackedOutputReturn.bufferTape,if_neg hp,if_neg he]
      cases hq : p-sigma with
      | zero => omega
      | succ q =>
        simp only [MultitapeTM.tapeOf,List.map_nil,List.getD_nil,List.length_nil]
        simp

private theorem call_internal_flatrecursivecallchildframes_return_idem (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List Bool) :
    TrackedOutputReturn.bufferTape M (TrackedOutputReturn.bufferTape M base sigma w) sigma w=
      TrackedOutputReturn.bufferTape M base sigma w := by
  funext p
  by_cases hp : p < sigma <;> simp only [TrackedOutputReturn.bufferTape,hp,if_true,if_false]

private theorem call_internal_preparation_buffer (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (call_internal_preparationFinal M n request resume label base rho sigma offset extent c v x y).cells (bufferTape M)=
      TrackedOutputReturn.bufferTape M
        ((call_internal_preparationFinal M n request resume label base rho sigma offset extent c v x y).cells (bufferTape M)) sigma [] ∧
    (call_internal_preparationFinal M n request resume label base rho sigma offset extent c v x y).head (bufferTape M)=
      sigma+(TrackedBankPreparation.inputWord M x y).length+1 := by
  have hc : (call_internal_preparationFinal M n request resume label base rho sigma offset extent c v x y).cells (bufferTape M)=
      TrackedBankPreparation.bankTape M
        ((call_internal_preparationParent M n request resume label base rho sigma offset extent c v x y).cells ⟨1,by change 1 < M.k+2; omega⟩) sigma [] := by
    change (FixedTapeExtension.embed (TrackedBankPreparation.machine M) _
      (TrackedBankPreparation.readyFrame M _ sigma (newOffsets M offset extent) x y)).cells
      (FixedTapeExtension.oldTape (TrackedBankPreparation.machine M) ⟨1,by change 1 < M.k+2; omega⟩)=_
    rw [call_internal_extension_old_cells]
    simp only [TrackedBankPreparation.readyFrame,TrackedBankedSimulation.embed,
      dif_neg (by omega : ¬2 ≤ (1 : ℕ)),TrackedBankPreparation.callerBase,if_true]
  constructor
  · rw [hc,call_internal_flatrecursivecallchildframes_bank_empty_buffer]
    exact (call_internal_flatrecursivecallchildframes_return_idem M _ sigma []).symm
  · change (FixedTapeExtension.embed (TrackedBankPreparation.machine M) _
      (TrackedBankPreparation.readyFrame M _ sigma (newOffsets M offset extent) x y)).head
      (FixedTapeExtension.oldTape (TrackedBankPreparation.machine M) ⟨1,by change 1 < M.k+2; omega⟩)=_
    rw [call_internal_extension_old_heads]
    simp only [TrackedBankPreparation.readyFrame,TrackedBankedSimulation.embed,
      dif_neg (by omega : ¬2 ≤ (1 : ℕ)),TrackedBankPreparation.callerBase,if_true]

private theorem call_internal_preparation_parent_nonbuffer (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool)
    (i : Fin (M.k+2)) (hi : i.val≠1) :
    (call_internal_preparationParent M n request resume label base rho sigma offset extent c v x y).cells i=
      (childBase M n request resume base rho sigma offset extent c label).cells
        (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) i) := by
  have hb : i≠TrackedChildInputBridge.bufferTape M := by
    intro h; exact hi (congrArg Fin.val h)
  simp only [call_internal_preparationParent,call_internal_reserveParent,call_internal_pushed,FiniteContinuationStack.pushFrame,
    if_neg (call_internal_stack_ne_old M i),call_internal_pushParent]
  rw [show FixedTapeExtension.oldTape (TrackedBankReservation.machine M) i=
    FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) i by rfl]
  simp only [call_internal_inputFinal,call_internal_extension_old_cells]
  simp only [TrackedChildInputBridge.finalFrame,if_neg hb,TrackedChildInputBridge.initialCells]
  simp only [childBase,if_neg (call_internal_stack_ne_old M i),FixedTapeExtension.oldTape,if_neg hi,bodyFrame,liftBody]
  have hs : (⟨i.val,by have := i.isLt; omega⟩ : Fin (M.k+3))≠stackTape M := call_internal_stack_ne_old M i
  simp only [if_neg hs,FixedTapeExtension.embed,dif_pos i.isLt,FixedTapeExtension.innerTape]
  funext p
  simp only [TrackedBankedSimulation.embed]
  by_cases hw : 2 ≤ i.val
  · simp only [dif_pos hw]
    by_cases hp : p < offset (innerTape M i hw)
    · simp only [if_pos hp,TrackedChildInputBridge.parentBase,if_neg hb,call_internal_inputParent,parentBase,if_neg hi]
    · simp only [if_neg hp]
  · simp only [dif_neg hw,TrackedChildInputBridge.parentBase,if_neg hb,call_internal_inputParent,parentBase,if_neg hi]

private theorem call_internal_preparation_parent_buffer_prefix (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) (p : ℕ) (hp : p < sigma) :
    (call_internal_preparationParent M n request resume label base rho sigma offset extent c v x y).cells
      ⟨1,by change 1 < M.k+2; omega⟩ p=base.cells (bufferTape M) p := by
  simp only [call_internal_preparationParent,call_internal_reserveParent,call_internal_pushed,FiniteContinuationStack.pushFrame,
    if_neg (call_internal_stack_ne_old M _),call_internal_pushParent]
  rw [show FixedTapeExtension.oldTape (TrackedBankReservation.machine M) ⟨1,by change 1 < M.k+2; omega⟩=
    FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) ⟨1,by change 1 < M.k+2; omega⟩ by rfl]
  simp only [call_internal_inputFinal,call_internal_extension_old_cells,TrackedChildInputBridge.finalFrame,
    show (⟨1,by change 1 < M.k+2; omega⟩ : Fin (M.k+2))=TrackedChildInputBridge.bufferTape M by rfl,
    if_true,TrackedBankPreparation.sourceTape,if_pos hp,call_internal_inputParent]
  rfl

private theorem call_internal_preparation_stack_cells (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (call_internal_preparationFinal M n request resume label base rho sigma offset extent c v x y).cells (stackTape M)=
      FiniteContinuationStack.recordTape M n (base.cells (stackTape M)) rho label n := by
  have he : stackTape M=FixedTapeExtension.extraTape (TrackedBankPreparation.machine M) := by apply Fin.ext; rfl
  simp only [call_internal_preparationFinal,he,call_internal_extension_extra_cells,call_internal_preparationPadBase,call_internal_reserveFinal]
  rw [show FixedTapeExtension.extraTape (TrackedBankPreparation.machine M)=
    FixedTapeExtension.extraTape (TrackedBankReservation.machine M) by rfl]
  simp only [call_internal_extension_extra_cells,call_internal_reservePadBase,call_internal_pushed,FiniteContinuationStack.pushFrame]
  rw [show FixedTapeExtension.extraTape (TrackedBankReservation.machine M)=stackTape M by rfl]
  simp only [eq_self,if_true,call_internal_pushParent,call_internal_input_stack_cells]
  funext p
  by_cases hp : p < rho <;> simp only [FiniteContinuationStack.recordTape,FiniteContinuationStack.freshTape,hp,if_true,if_false]

private theorem call_internal_preparation_stack_head (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (call_internal_preparationFinal M n request resume label base rho sigma offset extent c v x y).head (stackTape M)=rho+n+1 := by
  have he : stackTape M=FixedTapeExtension.extraTape (TrackedBankPreparation.machine M) := by apply Fin.ext; rfl
  simp only [call_internal_preparationFinal,he,call_internal_extension_extra_heads,call_internal_preparationPadBase,call_internal_reserveFinal]
  rw [show FixedTapeExtension.extraTape (TrackedBankPreparation.machine M)=
    FixedTapeExtension.extraTape (TrackedBankReservation.machine M) by rfl]
  simp only [call_internal_extension_extra_heads,call_internal_reservePadBase,call_internal_pushed,FiniteContinuationStack.pushFrame]
  rw [show FixedTapeExtension.extraTape (TrackedBankReservation.machine M)=stackTape M by rfl]
  simp only [eq_self,if_true]


private theorem call_internal_preparation_parent_root_head (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool)
    (i : Fin (M.k+2)) (hi : i.val=0) :
    (call_internal_preparationParent M n request resume label base rho sigma offset extent c v x y).head i=
      base.head (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) i) := by
  have hb : i≠TrackedChildInputBridge.bufferTape M := by intro h; have := congrArg Fin.val h; simp [hi,TrackedChildInputBridge.bufferTape] at this
  have hp : i≠TrackedChildInputBridge.packetTape M := by intro h; have := congrArg Fin.val h; simp [hi,TrackedChildInputBridge.packetTape,workTape] at this
  have hw : ¬2 ≤ i.val := by omega
  simp only [call_internal_preparationParent,TrackedBankReservation.finalFrame,dif_neg hw,call_internal_reserveParent,call_internal_pushed,
    FiniteContinuationStack.pushFrame,if_neg (call_internal_stack_ne_old M _),call_internal_pushParent]
  rw [show FixedTapeExtension.oldTape (TrackedBankReservation.machine M) i=
    FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) i by rfl]
  simp only [call_internal_inputFinal,call_internal_extension_old_heads,TrackedChildInputBridge.finalFrame,if_neg hb,if_neg hp,
    TrackedChildInputBridge.initialHeads,TrackedBankedSimulation.embed,dif_neg hw,
    TrackedChildInputBridge.parentBase,if_neg hb,call_internal_inputParent]

private theorem call_internal_preparation_child_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    headFrame M n request resume (.body M.qStart)
      (relabel M n request resume .resetBuffer
        (liftPreparation M n request resume (call_internal_preparationFinal M n request resume label base rho sigma offset extent c v x y)))
      (bufferTape M) (sigma+1)=
    childFrame M n request resume base rho sigma offset extent c label x y := by
  classical
  apply call_internal_flatrecursivecallchildframes_cfg_ext
  · rfl
  · funext i p
    have hik : i.val < M.k+3 := i.isLt
    by_cases hi : i.val < M.k+2
    · simp only [headFrame,relabel,liftPreparation,call_internal_preparationFinal,childFrame,bodyFrame,liftBody,
        FixedTapeExtension.embed,dif_pos hi]
      simp only [TrackedBankPreparation.readyFrame,TrackedBankedSimulation.embed,
        TrackedBankPreparation.callerBase,parentBase,FixedTapeExtension.innerTape]
      by_cases hw : 2 ≤ i.val
      · simp only [dif_pos hw]
        by_cases hp : p < newOffsets M offset extent (innerTape M ⟨i.val,hi⟩ hw)
        · simp only [if_pos hp,if_neg (by omega : i.val≠1)]
          exact congrFun (call_internal_preparation_parent_nonbuffer M n request resume label base rho sigma offset extent c v x y
            ⟨i.val,hi⟩ (by change i.val≠1; omega)) p
        · simp only [if_neg hp]
      · simp only [dif_neg hw]
        by_cases hb : i.val=1
        · simp only [if_pos hb]
          rw [call_internal_flatrecursivecallchildframes_bank_empty_buffer]
          by_cases hp : p < sigma
          · simp only [TrackedOutputReturn.bufferTape,if_pos hp]
            have hi1 : (⟨i.val,hi⟩ : Fin (M.k+2))=⟨1,by omega⟩ := Fin.ext hb
            rw [hi1,call_internal_preparation_parent_buffer_prefix M n request resume label base rho sigma offset extent c v x y p hp]
            change base.cells (bufferTape M) p=
              (childBase M n request resume base rho sigma offset extent c label).cells (bufferTape M) p
            simp [childBase,bufferTape,stackTape,FiniteContinuationStack.stackTape,
              TrackedOutputReturn.bufferTape,hp]
          · simp only [TrackedOutputReturn.bufferTape,if_neg hp]
        · simp only [if_neg hb]
          exact congrFun (call_internal_preparation_parent_nonbuffer M n request resume label base rho sigma offset extent c v x y
            ⟨i.val,hi⟩ hb) p
    · have he : i=stackTape M := by apply Fin.ext; simp only [stackTape,FiniteContinuationStack.stackTape]; omega
      subst i
      change (call_internal_preparationFinal M n request resume label base rho sigma offset extent c v x y).cells (stackTape M) p=
        (FixedTapeExtension.embed (TrackedBankedSimulation.machine M)
          (stackBase M n request resume (childBase M n request resume base rho sigma offset extent c label) (rho+n+1))
          (TrackedBankedSimulation.embed M _ _ _ _)).cells (stackTape M) p
      rw [call_internal_preparation_stack_cells]
      rw [show stackTape M=FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M) by rfl,
        call_internal_extension_extra_cells]
      rw [show FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M)=stackTape M by rfl]
      simp only [stackBase,if_true,childBase,if_true,FiniteContinuationStack.freshTape]
      by_cases hp : p < rho+n+1
      · simp only [if_pos hp]
      · simp only [if_neg hp,FiniteContinuationStack.recordTape,
          if_neg (by omega : ¬p < rho),if_neg (by omega : p≠rho),if_neg hp]
  · funext i
    have hik : i.val < M.k+3 := i.isLt
    by_cases hb : i=bufferTape M
    · subst i
      simp [headFrame,childFrame,bodyFrame,liftBody,FixedTapeExtension.embed,
        TrackedBankedSimulation.embed,parentBase,bufferTape,FixedTapeExtension.innerTape]
    · simp only [headFrame,Function.update_of_ne hb,relabel,liftPreparation]
      by_cases hi : i.val < M.k+2
      · simp only [call_internal_preparationFinal,childFrame,bodyFrame,liftBody,FixedTapeExtension.embed,dif_pos hi,
          TrackedBankPreparation.readyFrame,TrackedBankedSimulation.embed,FixedTapeExtension.innerTape]
        by_cases hw : 2 ≤ i.val
        · simp [dif_pos hw,MultitapeTM.initCfg]
        · have hn : i.val≠1 := by intro h; exact hb (Fin.ext h)
          have hz : i.val=0 := by omega
          simp only [dif_neg hw,TrackedBankPreparation.callerBase,parentBase,if_neg hn]
          rw [call_internal_preparation_parent_root_head M n request resume label base rho sigma offset extent c v x y ⟨i.val,hi⟩ hz]
          simp only [childBase,FixedTapeExtension.oldTape]
          have hs : (⟨i.val,by omega⟩ : Fin (M.k+3))≠stackTape M := by intro h; have := congrArg Fin.val h; simp [stackTape,FiniteContinuationStack.stackTape] at this; omega
          simp only [if_neg hs,if_neg hn,dif_pos hi,dif_neg hw]
      · have he : i=stackTape M := by apply Fin.ext; simp only [stackTape,FiniteContinuationStack.stackTape]; omega
        subst i
        rw [call_internal_preparation_stack_head]
        simp only [childFrame,bodyFrame,liftBody]
        rw [show stackTape M=FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M) by rfl,
          call_internal_extension_extra_heads]
        rw [show FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M)=stackTape M by rfl]
        simp only [stackBase,if_true]

end IntMul.FlatRecursiveCall




namespace IntMul.FlatRecursiveCall

open IntMul.FlatRecursiveScheduler
open IntMul.TrackedBankPreparation (inputWord)
open IntMul.TrackedBankCleanup (span)

/-- One real recursive call entry in the single flat transition table. -/
private theorem call_entry_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool)
    (live : c.state≠M.qHalt) (call : request c.state=some label)
    (packet : c.cells M.outTape=M.tapeOf (inputWord M x y))
    (near : ∀ j, c.head j≤ extent j+1)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∃ t, t ≤ max (c.head M.outTape) (v.length+1)+2*max (inputWord M x y).length v.length+
        3*(inputWord M x y).length+
        span M (TrackedBankReservation.distance M extent (parentAfterInput M c).head)+n+16 ∧
      (machine M n request resume).step^[t]
        (bodyFrame M n request resume base rho sigma offset extent c v)=
        childFrame M n request resume base rho sigma offset extent c label x y := by
  have hbody : (machine M n request resume).step
      (bodyFrame M n request resume base rho sigma offset extent c v)=
      liftInput M n request resume label (call_internal_inputStart M n request resume base rho sigma offset extent c v) := by
    change (machine M n request resume).step
      (liftBody M n request resume (call_internal_bodyView M n request resume base rho sigma offset extent c v))=_
    rw [call_internal_body_request_dispatch M n request resume _ label live call]
    exact call_internal_body_input_ready M n request resume label base rho sigma offset extent c v
  let I := max (c.head M.outTape) (v.length+1)+2*max (inputWord M x y).length v.length+4
  have hir : (inputMachine M).step^[I] (call_internal_inputStart M n request resume base rho sigma offset extent c v)=
      call_internal_inputFinal M n request resume base rho sigma offset extent c v x y := by
    have h := (FixedTapeExtension.simulate_run (TrackedChildInputBridge.machine M)
      (call_internal_inputPadBase M n request resume base rho sigma offset extent c v)
      (TrackedChildInputBridge.initialFrame M (call_internal_inputParent M n request resume base) sigma offset extent c v) I).1
    rw [(TrackedChildInputBridge.input_correct M (call_internal_inputParent M n request resume base)
      sigma offset extent c v x y packet).1] at h
    exact h
  have hih : ((inputMachine M).step^[I] (call_internal_inputStart M n request resume base rho sigma offset extent c v)).state=
      (inputMachine M).qHalt := by rw [hir]; rfl
  obtain ⟨s,hsc,hsr⟩ := call_internal_input_to_halt M n request resume label
    (call_internal_inputStart M n request resume base rho sigma offset extent c v) I hih
  rw [hir] at hsr
  have hdown1 : (machine M n request resume).step^[s+1]
      (bodyFrame M n request resume base rho sigma offset extent c v)=
      liftInput M n request resume label (call_internal_inputFinal M n request resume base rho sigma offset extent c v x y) := by
    rw [Function.iterate_succ_apply,hbody,hsr]
  have hstack : (machine M n request resume).step^[n+2]
      (liftInput M n request resume label (call_internal_inputFinal M n request resume base rho sigma offset extent c v x y))=
      liftPush M n request resume (call_internal_pushed M n request resume label base rho sigma offset extent c v x y) := by
    rw [show n+2=(n+1)+1 by omega,Function.iterate_succ_apply,call_internal_input_dispatch M n request resume label _ rfl,
      call_internal_input_push_ready M n request resume label base rho sigma offset extent c v x y]
    exact FlatRecursiveStack.call_internal_push_correct M n request resume _ rho label
  have hdown2 : (machine M n request resume).step^[n+3]
      (liftInput M n request resume label (call_internal_inputFinal M n request resume base rho sigma offset extent c v x y))=
      liftReservation M n request resume (call_internal_reserveStart M n request resume label base rho sigma offset extent c v x y) := by
    rw [show n+3=(n+2)+1 by omega,Function.iterate_succ_apply',hstack,
      call_internal_push_dispatch M n request resume _ (by simp [call_internal_pushed,FiniteContinuationStack.pushFrame])]
    exact call_internal_push_reserve_ready M n request resume label base rho sigma offset extent c v x y
  have hnear : ∀ j, (parentAfterInput M c).head j≤ extent j+1 := by
    intro j
    simp only [parentAfterInput]
    split
    · omega
    · exact near j
  have htail : ∀ j p, extent j < p → (parentAfterInput M c).cells j p=M.blank := tail
  let R := span M (TrackedBankReservation.distance M extent (parentAfterInput M c).head)+1
  have hrr : (reservationMachine M).step^[R]
      (call_internal_reserveStart M n request resume label base rho sigma offset extent c v x y)=
      call_internal_reserveFinal M n request resume label base rho sigma offset extent c v x y := by
    have h := (FixedTapeExtension.simulate_run (TrackedBankReservation.machine M)
      (call_internal_reservePadBase M n request resume label base rho sigma offset extent c v x y)
      (TrackedBankReservation.initialFrame M
        (call_internal_reserveParent M n request resume label base rho sigma offset extent c v x y)
        offset extent (parentAfterInput M c)) R).1
    rw [(TrackedBankReservation.reserve_correct M
      (call_internal_reserveParent M n request resume label base rho sigma offset extent c v x y)
      offset extent (parentAfterInput M c) hnear htail).1] at h
    exact h
  have hrh : ((reservationMachine M).step^[R]
      (call_internal_reserveStart M n request resume label base rho sigma offset extent c v x y)).state=(reservationMachine M).qHalt := by
    rw [hrr]; rfl
  obtain ⟨q,hqc,hqr⟩ := call_internal_reservation_to_halt M n request resume
    (call_internal_reserveStart M n request resume label base rho sigma offset extent c v x y) R hrh
  rw [hrr] at hqr
  have hdown3 : (machine M n request resume).step^[q+1]
      (liftReservation M n request resume (call_internal_reserveStart M n request resume label base rho sigma offset extent c v x y))=
      liftPreparation M n request resume (call_internal_preparationStart M n request resume label base rho sigma offset extent c v x y) := by
    rw [Function.iterate_succ_apply',hqr,call_internal_reservation_dispatch M n request resume _ rfl]
    exact call_internal_reserve_preparation_ready M n request resume label base rho sigma offset extent c v x y tail
  let P := 2*(inputWord M x y).length+3
  have hpr : (preparationMachine M).step^[P]
      (call_internal_preparationStart M n request resume label base rho sigma offset extent c v x y)=
      call_internal_preparationFinal M n request resume label base rho sigma offset extent c v x y := by
    have h := (FixedTapeExtension.simulate_run (TrackedBankPreparation.machine M)
      (call_internal_preparationPadBase M n request resume label base rho sigma offset extent c v x y)
      (TrackedBankPreparation.initialFrame M
        (call_internal_preparationParent M n request resume label base rho sigma offset extent c v x y)
        sigma (TrackedBankReservation.newOffsets M offset extent) x y) P).1
    rw [TrackedBankPreparation.setup_correct] at h
    exact h
  have hph : ((preparationMachine M).step^[P]
      (call_internal_preparationStart M n request resume label base rho sigma offset extent c v x y)).state=(preparationMachine M).qHalt := by
    rw [hpr]; rfl
  obtain ⟨p,hpc,hprun⟩ := call_internal_preparation_to_halt M n request resume
    (call_internal_preparationStart M n request resume label base rho sigma offset extent c v x y) P hph
  rw [hpr] at hprun
  have hdown4 : (machine M n request resume).step^[p+1]
      (liftPreparation M n request resume (call_internal_preparationStart M n request resume label base rho sigma offset extent c v x y))=
      relabel M n request resume .resetBuffer
        (liftPreparation M n request resume (call_internal_preparationFinal M n request resume label base rho sigma offset extent c v x y)) := by
    rw [Function.iterate_succ_apply',hprun,call_internal_preparation_dispatch M n request resume _ rfl]
  have hbuf := call_internal_preparation_buffer M n request resume label base rho sigma offset extent c v x y
  have hdown5 : (machine M n request resume).step^[(inputWord M x y).length+2]
      (relabel M n request resume .resetBuffer
        (liftPreparation M n request resume (call_internal_preparationFinal M n request resume label base rho sigma offset extent c v x y)))=
      childFrame M n request resume base rho sigma offset extent c label x y := by
    rw [show (inputWord M x y).length+2=((inputWord M x y).length+1)+1 by omega,
      call_internal_reset_complete M n request resume _ sigma ((inputWord M x y).length+1) rfl hbuf.2 hbuf.1]
    exact call_internal_preparation_child_ready M n request resume label base rho sigma offset extent c v x y
  let a := s+1
  let b := n+3
  let d := q+1
  let e := p+1
  let f := (inputWord M x y).length+2
  refine ⟨f+(e+(d+(b+a))),by dsimp only [a,b,d,e,f,I,R,P] at *; omega,?_⟩
  rw [Function.iterate_add_apply (machine M n request resume).step f (e+(d+(b+a))),
    Function.iterate_add_apply (machine M n request resume).step e (d+(b+a)),
    Function.iterate_add_apply (machine M n request resume).step d (b+a),
    Function.iterate_add_apply (machine M n request resume).step b a,
    hdown1,hdown2,hdown3,hdown4,hdown5]

end IntMul.FlatRecursiveCall


open IntMul IntMul.FlatRecursiveCall IntMul.FlatRecursiveScheduler IntMul.TrackedBankPreparation IntMul.TrackedBankCleanup

theorem solution (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool)
    (live : c.state≠M.qHalt) (call : request c.state=some label)
    (packet : c.cells M.outTape=M.tapeOf (inputWord M x y))
    (near : ∀ j, c.head j≤ extent j+1)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∃ t, t ≤ max (c.head M.outTape) (v.length+1)+2*max (inputWord M x y).length v.length+
        3*(inputWord M x y).length+
        span M (TrackedBankReservation.distance M extent (parentAfterInput M c).head)+n+16 ∧
      (machine M n request resume).step^[t]
        (bodyFrame M n request resume base rho sigma offset extent c v)=
        childFrame M n request resume base rho sigma offset extent c label x y :=
  IntMul.FlatRecursiveCall.call_entry_correct M n request resume label base rho sigma offset extent c v x y live call packet near tail

#print axioms solution
